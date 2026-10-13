#!/usr/bin/env python3
"""
acnesemu 0.1.1a by ac kondo [c] acholdings
==========================================

A single-file, clean-room NES / Famicom emulator for Python 3.  The desktop
front end follows the current FCEUX (2.6.x, Qt) console window: the same menu
bar (File / Movie / Options / Emulation / Tools / Debug / NetPlay / Help), the
same default hotkeys, a plain black game client, and FCEUX-style tool windows
(Debugger, Hex Editor, PPU Viewer, Sprite Viewer, Name Table Viewer, Trace
Logger, Cheats with Game Genie, RAM Search, RAM Watch, ...).

Speed
-----
* Normal speed is the NTSC Famicom rate: 60.0988 frames per second
  (speed 60 == Famicom).  The core is built to hold that in pure Python:
  a generated 6502 interpreter with registers in local variables and inlined
  RAM/ROM access, a cached scanline PPU renderer, and a batched APU.

Emulation
---------
* Complete 256-entry 2A03 opcode map including unofficial NMOS opcodes, with
  FCEUX CycTable cycle counts, page-cross and branch penalties.
* Scanline PPU driven by the loopy v/t registers: fine/coarse scrolling,
  mid-frame split screens, dot-accurate sprite-0 hit, sprite overflow,
  8x16 sprites, left-column clipping, greyscale/emphasis, odd-frame skip.
* MMC3-style scanline IRQs at dot 260, CPU-cycle IRQ boards (VRC, FME-7,
  Namco 163, Bandai, Irem, ...), MMC2/MMC4 CHR latches.
* 2A03 APU: two pulses, triangle, noise, DMC (with DMA stalls), frame IRQ,
  non-linear mixer; streamed at 44.1 kHz through sounddevice or pygame-ce.
* iNES / NES 2.0 with a broad commercial mapper library (see Help > About).
* NTSC (default), PAL and Dendy timing; RAM init modes; battery saves (.sav).
* Save states (10 quick slots + files), FM2 movie record / playback,
  WAV recording, Game Genie and raw cheats, screenshots (PNG).

No ROMs, BIOS files or external assets are included or required.  Bring your
own legally obtained .nes dumps.  This is an original educational
implementation - it is not FCEUX source code and is not affiliated with the
FCEUX project.
"""

from __future__ import annotations

import argparse
import collections
import copy
import os
import pathlib
import pickle
import random
import struct
import sys
import threading
import time
import webbrowser
import zlib
from array import array
from dataclasses import dataclass
from typing import Callable, Optional

try:  # The core runs headless; the GUI needs Tk.
    import tkinter as tk
    from tkinter import filedialog, messagebox, simpledialog, ttk
except ImportError:  # pragma: no cover - exercised on Tk-less Pythons
    tk = None  # type: ignore[assignment]
    filedialog = messagebox = simpledialog = ttk = None  # type: ignore[assignment]



APP_TITLE = "acnesemu 0.1.1a"
APP_VERSION = "0.1.1a"
APP_AUTHOR = "ac kondo / acholdings"
# Classic Win32 / FCEUX chrome (Windows 98-era system colors).
WIN_FACE = "#d4d0c8"
WIN_LIGHT = "#ffffff"
WIN_SHADOW = "#808080"
WIN_DARK = "#404040"
WIN_WINDOW = "#ffffff"
WIN_MENU = "#d4d0c8"
WIN_TEXT = "#000000"
WIN_DISABLED = "#808080"
WIN_HIGHLIGHT = "#0a246a"
WIN_HIGHLIGHT_TEXT = "#ffffff"
WIN_CLIENT = "#000000"
NTSC_FPS = 60.0988
# Emulation Speed units: 60 == NTSC Famicom (~NTSC_FPS). Other values scale that rate.
FAMICOM_SPEED = 60
CPU_CLOCK = 1_789_773
SCREEN_W = 256
SCREEN_H = 240

# Common NTSC 2C02 palette. Exact colors varied with display hardware.
NES_PALETTE = (
    (84, 84, 84), (0, 30, 116), (8, 16, 144), (48, 0, 136),
    (68, 0, 100), (92, 0, 48), (84, 4, 0), (60, 24, 0),
    (32, 42, 0), (8, 58, 0), (0, 64, 0), (0, 60, 0),
    (0, 50, 60), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (152, 150, 152), (8, 76, 196), (48, 50, 236), (92, 30, 228),
    (136, 20, 176), (160, 20, 100), (152, 34, 32), (120, 60, 0),
    (84, 90, 0), (40, 114, 0), (8, 124, 0), (0, 118, 40),
    (0, 102, 120), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (236, 238, 236), (76, 154, 236), (120, 124, 236), (176, 98, 236),
    (228, 84, 236), (236, 88, 180), (236, 106, 100), (212, 136, 32),
    (160, 170, 0), (116, 196, 0), (76, 208, 32), (56, 204, 108),
    (56, 180, 204), (60, 60, 60), (0, 0, 0), (0, 0, 0),
    (236, 238, 236), (168, 204, 236), (188, 188, 236), (212, 178, 236),
    (236, 174, 236), (236, 174, 212), (236, 180, 176), (228, 196, 144),
    (204, 210, 120), (180, 222, 120), (168, 226, 144), (152, 226, 180),
    (160, 214, 228), (160, 162, 160), (0, 0, 0), (0, 0, 0),
)


# Precomputed bitplane decode: PIXEL_ROW_LUT[(high << 8) | low] -> 8 pixel values
# (leftmost pixel first). Removes 8 shifts/masks from every background tile row.
PIXEL_ROW_LUT = tuple(
    bytes(
        (((low >> bit) & 1) | (((high >> bit) & 1) << 1))
        for bit in range(7, -1, -1)
    )
    for high in range(256)
    for low in range(256)
)

MIRROR_REMAP = {
    "vertical": (0, 1, 0, 1),
    "horizontal": (0, 0, 1, 1),
    "single0": (0, 0, 0, 0),
    "single1": (1, 1, 1, 1),
    "four": (0, 1, 2, 3),
}




class CartridgeError(ValueError):
    """Raised when a cartridge image is malformed or unsupported."""


class Mapper:
    def __init__(self, cart: "Cartridge") -> None:
        self.cart = cart
        self.irq_pending = False
        self.needs_cpu_clock = False

    def prg_ram_enabled(self) -> bool:
        return True

    def prg_ram_writable(self) -> bool:
        return True

    def prg_ram_index(self, address: int) -> int:
        """Offset into cart.prg_ram for $6000–$7FFF accesses."""
        return address & 0x1FFF

    def cpu_data(self, address: int) -> Optional[int]:
        """Optional direct CPU data bus value (EEPROM / open-bus boards)."""
        return None

    def cpu_read(self, address: int) -> Optional[int]:
        raise NotImplementedError

    def cpu_write(self, address: int, value: int) -> bool:
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return address % self.cart.chr_len
        return None

    def ppu_write(self, address: int, value: int) -> bool:
        # Route CHR-RAM writes through the mapper's banking so banked
        # CHR-RAM boards (VRC, Namco, …) write to the selected bank.
        if address < 0x2000 and self.cart.chr_is_ram:
            index = self.ppu_read(address)
            if index is not None:
                self.cart.chr[index] = value
                return True
        return False

    def register_read(self, address: int) -> Optional[int]:
        """Read a mapper register in $4020-$5FFF, returning a data byte."""
        return None

    def mirror_mode(self) -> str:
        return self.cart.header_mirroring

    # MMC3-style boards clock on pre-render line 261; MMC5 does not.
    clocks_prerender = True

    def clock_scanline(self) -> None:
        pass

    def clock_cpu(self, cycles: int) -> None:
        """Advance CPU-cycle IRQ counters (VRC/FME-7/Namco/etc.)."""

    def reset(self) -> None:
        self.irq_pending = False


class Mapper0(Mapper):
    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None


class Mapper1(Mapper):
    """MMC1/SxROM mapper with serial bank register."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.shift = 0x10
        self.control = 0x0C
        self.chr0 = 0
        self.chr1 = 0
        self.prg_bank = 0
        self.prg_ram_disable = False
        self._last_write_cycle = -2

    def prg_ram_enabled(self) -> bool:
        return not self.prg_ram_disable

    def prg_ram_writable(self) -> bool:
        return not self.prg_ram_disable

    def _prg_outer(self) -> int:
        # SUROM/SXROM: CHR reg bit 4 selects the upper 256 KiB PRG half.
        if self.cart.prg_len > 0x40000:
            return ((self.chr0 >> 4) & 1) << 4
        return 0

    def prg_ram_index(self, address: int) -> int:
        # SXROM: 32 KiB WRAM banked by CHR0 bits 2–3 (Final Fantasy III JP, etc.).
        if len(self.cart.prg_ram) > 0x2000:
            bank = (self.chr0 >> 2) & 3
            return (bank * 0x2000) + (address & 0x1FFF)
        return address & 0x1FFF

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        mode = (self.control >> 2) & 3
        bank_count = max(1, self.cart.prg_len // 0x4000)
        prg = self.prg_bank | self._prg_outer()
        if mode in (0, 1):
            bank = (prg & 0x0E) % bank_count
            return (bank * 0x4000 + (address & 0x7FFF)) % self.cart.prg_len
        if mode == 2:
            bank = 0 if address < 0xC000 else prg % bank_count
        else:
            bank = prg % bank_count if address < 0xC000 else bank_count - 1
        return (bank * 0x4000 + (address & 0x3FFF)) % self.cart.prg_len

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        # MMC1 ignores a write on the CPU cycle immediately after another write
        # (so RMW dummy+real pairs only load the first value into the shift reg).
        cycle = getattr(self.cart, "write_cycle", 0)
        if cycle == self._last_write_cycle + 1:
            return True
        self._last_write_cycle = cycle
        if value & 0x80:
            self.shift = 0x10
            self.control |= 0x0C
            return True
        complete = bool(self.shift & 1)
        self.shift = (self.shift >> 1) | ((value & 1) << 4)
        if complete:
            register = (address >> 13) & 3
            data = self.shift & 0x1F
            if register == 0:
                self.control = data
            elif register == 1:
                self.chr0 = data
            elif register == 2:
                self.chr1 = data
            else:
                self.prg_bank = data & 0x0F
                self.prg_ram_disable = bool(data & 0x10)
            self.shift = 0x10
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        if self.control & 0x10:
            bank = self.chr0 if address < 0x1000 else self.chr1
            index = bank * 0x1000 + (address & 0x0FFF)
        else:
            bank = self.chr0 & 0x1E
            index = bank * 0x1000 + address
        return index % len(self.cart.chr)

    def ppu_write(self, address: int, value: int) -> bool:
        index = self.ppu_read(address)
        if index is not None and self.cart.chr_is_ram:
            self.cart.chr[index] = value
            return True
        return False

    def mirror_mode(self) -> str:
        return ("single0", "single1", "vertical", "horizontal")[self.control & 3]


class Mapper2(Mapper):
    """UxROM mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.bank = value
            return True
        return False


class Mapper3(Mapper):
    """CNROM mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            banks = max(1, self.cart.chr_len // 0x2000)
            self.chr_bank = value % banks
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % self.cart.chr_len
        return None


class Mapper4(Mapper):
    """MMC3/MMC6-compatible banking and scanline IRQ counter."""

    a12_clocked = True

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.select = 0
        self.regs = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_reload = False
        self.irq_enabled = False
        # Commercial MMC3 titles expect WRAM available unless $A001 disables it.
        self.wram_enable = True
        self.wram_protect = False
        self._chr_base = [0] * 8
        self._chr_xor = 0
        self._rebuild_chr()

    def prg_ram_enabled(self) -> bool:
        return self.wram_enable

    def prg_ram_writable(self) -> bool:
        return self.wram_enable

    def _rebuild_chr(self) -> None:
        regs = self.regs
        chr_len = self.cart.chr_len
        bases = self._chr_base
        bases[0] = ((regs[0] & 0xFE) * 0x400) % chr_len
        bases[1] = (((regs[0] & 0xFE) + 1) * 0x400) % chr_len
        bases[2] = ((regs[1] & 0xFE) * 0x400) % chr_len
        bases[3] = (((regs[1] & 0xFE) + 1) * 0x400) % chr_len
        bases[4] = (regs[2] * 0x400) % chr_len
        bases[5] = (regs[3] * 0x400) % chr_len
        bases[6] = (regs[4] * 0x400) % chr_len
        bases[7] = (regs[5] * 0x400) % chr_len
        self._chr_xor = 0x1000 if self.select & 0x80 else 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = self.cart.prg_8k
        last = count - 1
        second_last = last - 1 if last else 0
        slot = (address - 0x8000) >> 13
        mode = (self.select >> 6) & 1
        if slot == 0:
            bank = second_last if mode else self.regs[6]
        elif slot == 1:
            bank = self.regs[7]
        elif slot == 2:
            bank = self.regs[6] if mode else second_last
        else:
            bank = last
        return (bank % count) * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        even = not (address & 1)
        region = address & 0xE000
        if region == 0x8000:
            if even:
                self.select = value
                self._chr_xor = 0x1000 if value & 0x80 else 0
            else:
                register = self.select & 7
                if register in (0, 1):
                    self.regs[register] = value & 0xFE
                elif register in (6, 7):
                    self.regs[register] = value & 0x3F
                else:
                    self.regs[register] = value & 0xFF
                if register <= 5:
                    self._rebuild_chr()
        elif region == 0xA000:
            if even:
                if self.cart.header_mirroring != "four":
                    self.mirror = "horizontal" if value & 1 else "vertical"
            else:
                # $A001: bit7 PRG-RAM enable, bit6 write-protect when set.
                self.wram_enable = bool(value & 0x80)
                self.wram_protect = bool(value & 0x40)
        elif region == 0xC000:
            if even:
                self.irq_latch = value
            else:
                self.irq_reload = True
        elif region == 0xE000:
            if even:
                self.irq_enabled = False
                self.irq_pending = False
            else:
                self.irq_enabled = True
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        logical = address ^ self._chr_xor
        return self._chr_base[logical >> 10] + (logical & 0x3FF)

    def ppu_write(self, address: int, value: int) -> bool:
        index = self.ppu_read(address)
        if index is not None and self.cart.chr_is_ram:
            self.cart.chr[index] = value
            return True
        return False

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_scanline(self) -> None:
        if self.irq_counter == 0 or self.irq_reload:
            self.irq_counter = self.irq_latch
            self.irq_reload = False
        else:
            self.irq_counter = (self.irq_counter - 1) & 0xFF
        if self.irq_counter == 0 and self.irq_enabled:
            self.irq_pending = True


class Mapper7(Mapper):
    """AxROM mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0
        self.single = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.bank = value & 7
            self.single = (value >> 4) & 1
            return True
        return False

    def mirror_mode(self) -> str:
        return "single1" if self.single else "single0"


class Mapper66(Mapper):
    """GxROM mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.prg_bank = (value >> 4) & 3
            self.chr_bank = value & 3
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


class Mapper9(Mapper):
    """MMC2 (Punch-Out!!) with PPU CHR latches."""

    chr_latch = True

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_fd = [0, 0]
        self.chr_fe = [0, 0]
        self.latch = [True, True]
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        if address < 0xA000:
            bank = self.prg_bank % count
        else:
            bank = count - (3 - (address - 0xA000) // 0x2000)
            bank = max(0, min(count - 1, bank))
        return (bank % count) * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0xA000:
            return False
        region = address & 0xF000
        if region == 0xA000:
            self.prg_bank = value & 0x0F
        elif region == 0xB000:
            self.chr_fd[0] = value & 0x1F
        elif region == 0xC000:
            self.chr_fe[0] = value & 0x1F
        elif region == 0xD000:
            self.chr_fd[1] = value & 0x1F
        elif region == 0xE000:
            self.chr_fe[1] = value & 0x1F
        elif region == 0xF000:
            self.mirror = "horizontal" if value & 1 else "vertical"
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        slot = 0 if address < 0x1000 else 1
        bank = self.chr_fe[slot] if self.latch[slot] else self.chr_fd[slot]
        index = (bank * 0x1000 + (address & 0x0FFF)) % len(self.cart.chr)
        lo = address & 0x0FF8
        if lo == 0x0FD8:
            self.latch[slot] = False
        elif lo == 0x0FE8:
            self.latch[slot] = True
        return index

    def ppu_write(self, address: int, value: int) -> bool:
        index = self.ppu_read(address)
        if index is not None and self.cart.chr_is_ram:
            self.cart.chr[index] = value
            return True
        return False

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper10(Mapper9):
    """MMC4 — MMC2-style CHR latches with 16 KiB PRG banks."""

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0xA000:
            return False
        region = address & 0xF000
        if region == 0xA000:
            self.prg_bank = value & 0x0F
        elif region == 0xB000:
            self.chr_fd[0] = value & 0x1F
        elif region == 0xC000:
            self.chr_fe[0] = value & 0x1F
        elif region == 0xD000:
            self.chr_fd[1] = value & 0x1F
        elif region == 0xE000:
            self.chr_fe[1] = value & 0x1F
        elif region == 0xF000:
            self.mirror = "horizontal" if value & 1 else "vertical"
        return True


class Mapper11(Mapper):
    """Color Dreams / Quattro discrete mapper."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.prg_bank = value & 0x03
            self.chr_bank = (value >> 4) & 0x0F
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


class Mapper13(Mapper):
    """CPROM — fixed PRG, banked CHR-RAM for $1000-$1FFF."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.chr_bank = value & 3
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = 0 if address < 0x1000 else self.chr_bank
        return (bank * 0x1000 + (address & 0x0FFF)) % len(self.cart.chr)

    def ppu_write(self, address: int, value: int) -> bool:
        index = self.ppu_read(address)
        if index is not None and self.cart.chr_is_ram:
            self.cart.chr[index] = value
            return True
        return False


class Mapper34(Mapper):
    """BNROM / NINA-001 style 32 KiB PRG (+ optional CHR regs)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr0 = 0
        self.chr1 = 1

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address == 0x7FFD:
            self.prg_bank = value & 1
            return True
        if address == 0x7FFE:
            self.chr0 = value & 0x0F
            return True
        if address == 0x7FFF:
            self.chr1 = value & 0x0F
            return True
        if address >= 0x8000:
            self.prg_bank = value & 0x0F
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        if len(self.cart.chr) <= 0x2000 and self.cart.chr_is_ram:
            return address % len(self.cart.chr)
        bank = self.chr0 if address < 0x1000 else self.chr1
        return (bank * 0x1000 + (address & 0x0FFF)) % len(self.cart.chr)


class Mapper71(Mapper):
    """Camerica / Codemasters (Fire Hawk mirroring variant supported)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x8000 <= address <= 0x9FFF:
            self.mirror = "single1" if value & 0x10 else "single0"
            return True
        if address >= 0xC000:
            self.bank = value & 0x0F
            return True
        if address >= 0x8000:
            self.bank = value & 0x0F
            return True
        return False

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper78(Mapper):
    """Irem 74HC161 / Holy Diver."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.prg_bank = value & 0x07
            self.chr_bank = (value >> 4) & 0x0F
            self.mirror = "single1" if value & 0x08 else "horizontal"
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper79(Mapper):
    """NINA-003/006 / American Video Entertainment."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x4100 <= address <= 0x5FFF and (address & 0x0100):
            self.prg_bank = (value >> 3) & 1
            self.chr_bank = value & 0x07
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


class Mapper87(Mapper):
    """Jaleco/other CNROM-like CHR via $6000."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x6000 <= address < 0x8000:
            self.chr_bank = ((value & 2) >> 1) | ((value & 1) << 1)
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


class Mapper89(Mapper):
    """Sunsoft-2 IC on Sunsoft-3 board."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0
        self.mirror = "single0"

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.chr_bank = (value & 0x07) | ((value >> 4) & 0x08)
            self.prg_bank = (value >> 4) & 0x07
            self.mirror = "single1" if value & 0x08 else "single0"
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper93(Mapper):
    """Sunsoft-2 on Sunsoft-3B / Fantasy Zone."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.prg_bank = (value >> 4) & 0x0F
            return True
        return False


class Mapper94(Mapper):
    """Capcom UxROM variant (Senjou no Ookami)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.bank = (value >> 2) & 0x07
            return True
        return False


class Mapper97(Mapper):
    """Irem TAM-S1 (Kaiketsu Yanchamaru)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = banks - 1 if address < 0xC000 else self.bank % banks
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.bank = value & 0x0F
            self.mirror = ("single0", "horizontal", "vertical", "single1")[(value >> 6) & 3]
            return True
        return False

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper113(Mapper):
    """HES / NINA-03/06 extended (mapper 113)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x4100 <= address <= 0x5FFF and (address & 0x4100) == 0x4100:
            self.prg_bank = (value >> 3) & 0x07
            self.chr_bank = (value & 0x07) | ((value >> 3) & 0x08)
            self.mirror = "vertical" if value & 0x80 else "horizontal"
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper140(Mapper):
    """Jaleco JF-11/14 (Bio Senshi Dan)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            banks = max(1, len(self.cart.prg) // 0x8000)
            return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x6000 <= address < 0x8000:
            self.chr_bank = value & 0x0F
            self.prg_bank = (value >> 4) & 0x03
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None


class Mapper152(Mapper):
    """Bandai / Taito 74*161/161/32 with 1-screen mirroring."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0
        self.mirror = "single0"

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.chr_bank = value & 0x0F
            self.prg_bank = (value >> 4) & 0x07
            self.mirror = "single1" if value & 0x80 else "single0"
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return (self.chr_bank * 0x2000 + address) % len(self.cart.chr)
        return None

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper180(Mapper):
    """UxROM with fixed first bank (Crazy Climber)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = 0 if address < 0xC000 else self.bank % banks
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.bank = value & 0x0F
            return True
        return False


class Mapper184(Mapper):
    """Sunsoft-1 CHR banking via $6000."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr0 = 0
        self.chr1 = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x6000 <= address < 0x8000:
            self.chr0 = value & 0x07
            self.chr1 = (value >> 4) & 0x07
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr0 if address < 0x1000 else self.chr1
        return (bank * 0x1000 + (address & 0x0FFF)) % len(self.cart.chr)


class Mapper185(Mapper):
    """CNROM with CHR-disable copy protection."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr_enable = True

    def cpu_read(self, address: int) -> Optional[int]:
        if address >= 0x8000:
            return (address - 0x8000) % len(self.cart.prg)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            # CHR is enabled when the low nibble is nonzero and not the
            # known-lockout value $13 (heuristic used by common emulators).
            low = value & 0x0F
            self.chr_enable = low != 0 and (value & 0x33) != 0x13
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        if not self.chr_enable:
            return None  # reads see open bus, which defeats the protection check
        return address % len(self.cart.chr)


class Mapper206(Mapper4):
    """Namcot 118 / DxROM — MMC3-like banking without IRQ or mirroring writes."""

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        even = not (address & 1)
        if (address & 0xE000) == 0x8000:
            if even:
                self.select = value & 0x3F
            else:
                register = self.select & 7
                self.regs[register] = value & (0xFE if register in (0, 1) else 0xFF)
                if register <= 5:
                    self._rebuild_chr()
            return True
        return False

    def clock_scanline(self) -> None:
        pass


class Mapper118(Mapper4):
    """TxSROM / MMC3 with CIRAM A10 from CHR A17."""

    def mirror_mode(self) -> str:
        # Approximate: use CHR bank 0 bit 7 as single-screen select when needed.
        # Full TxSROM is per-1KB nametable from CHR A17; use H/V fallback from bit.
        return "single1" if self.regs[0] & 0x80 else "single0"

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        even = not (address & 1)
        region = address & 0xE000
        if region == 0x8000:
            if even:
                self.select = value
            else:
                register = self.select & 7
                self.regs[register] = value & (0xFE if register in (0, 1) else 0xFF)
        elif region == 0xC000:
            if even:
                self.irq_latch = value
            else:
                self.irq_reload = True
        elif region == 0xE000:
            if even:
                self.irq_enabled = False
                self.irq_pending = False
            else:
                self.irq_enabled = True
        # Ignore $A000 mirroring — TxSROM uses CHR A17.
        return True


class Mapper119(Mapper4):
    """TQROM — MMC3 with mixed CHR: bank bit 6 selects 8 KiB of CHR-RAM."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        # Append the CHR-RAM area after the CHR-ROM image.
        self.ram_base = len(cart.chr)
        cart.chr.extend(bytearray(0x2000))
        cart.chr_len = len(cart.chr)

    def _chr_index(self, address: int) -> int:
        inverted = bool(self.select & 0x80)
        logical = address ^ (0x1000 if inverted else 0)
        slot = logical // 0x400
        pairs = (self.regs[0], self.regs[0] + 1, self.regs[1], self.regs[1] + 1)
        bank = pairs[slot] if slot < 4 else self.regs[slot - 2]
        if bank & 0x40:
            return self.ram_base + ((bank & 0x07) * 0x400 + (logical & 0x3FF))
        return ((bank & 0x3F) * 0x400 + (logical & 0x3FF)) % max(1, self.ram_base)

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return self._chr_index(address)

    def ppu_write(self, address: int, value: int) -> bool:
        if address >= 0x2000:
            return False
        index = self._chr_index(address)
        if index >= self.ram_base:
            self.cart.chr[index] = value
            return True
        return False


class Mapper75(Mapper):
    """Konami VRC1."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg = [0, 0, 0]
        self.chr = [0, 0]
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        slot = (address - 0x8000) // 0x2000
        banks = [self.prg[0], self.prg[1], self.prg[2], count - 1]
        return (banks[slot] % count) * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        region = address & 0xF000
        if region == 0x8000:
            self.prg[0] = value & 0x0F
        elif region == 0x9000:
            self.mirror = "horizontal" if value & 1 else "vertical"
            self.chr[0] = (self.chr[0] & 0x0F) | ((value & 2) << 3)
            self.chr[1] = (self.chr[1] & 0x0F) | ((value & 4) << 2)
        elif region == 0xA000:
            self.prg[1] = value & 0x0F
        elif region == 0xC000:
            self.prg[2] = value & 0x0F
        elif region == 0xE000:
            self.chr[0] = (self.chr[0] & 0x10) | (value & 0x0F)
        elif region == 0xF000:
            self.chr[1] = (self.chr[1] & 0x10) | (value & 0x0F)
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr[0] if address < 0x1000 else self.chr[1]
        return (bank * 0x1000 + (address & 0x0FFF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror


class _VRC2and4(Mapper):
    """Shared Konami VRC2/VRC4 banking + optional IRQ (VRC4)."""

    def __init__(self, cart: "Cartridge", a0_mask: int, a1_mask: int, has_irq: bool) -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.a0_mask = a0_mask
        self.a1_mask = a1_mask
        self.has_irq = has_irq
        self.prg = [0, 0]
        self.chr = [0] * 8
        self.prg_mode = 0
        self.mirror = cart.header_mirroring
        self.latch = 0
        self.irq_latch = 0
        self.irq_control = 0
        self.irq_counter = 0
        self.irq_prescale = 341

    def _reg(self, address: int) -> int:
        return ((1 if address & self.a1_mask else 0) << 1) | (1 if address & self.a0_mask else 0)

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        last = count - 1
        if self.prg_mode:
            banks = [last - 1, self.prg[1] % count, self.prg[0] % count, last]
        else:
            banks = [self.prg[0] % count, self.prg[1] % count, last - 1 if last else 0, last]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        region = address & 0xF000
        reg = self._reg(address)
        if region == 0x8000:
            self.prg[0] = value & 0x1F
        elif region == 0x9000:
            if reg in (0, 1):
                # VRC2 only has H/V (bit 0); VRC4 adds single-screen modes.
                mask = 3 if self.has_irq else 1
                self.mirror = ("vertical", "horizontal", "single0", "single1")[value & mask]
            elif reg in (2, 3) and self.has_irq:
                self.prg_mode = value & 2
        elif region == 0xA000:
            self.prg[1] = value & 0x1F
        elif 0xB000 <= region <= 0xE000:
            pair = ((region - 0xB000) // 0x1000) * 2 + (reg >> 1)
            if reg & 1:
                self.chr[pair] = (self.chr[pair] & 0x0F) | ((value & 0x0F) << 4)
            else:
                self.chr[pair] = (self.chr[pair] & 0xF0) | (value & 0x0F)
        elif region == 0xF000 and self.has_irq:
            if reg == 0:
                self.irq_latch = (self.irq_latch & 0xF0) | (value & 0x0F)
            elif reg == 1:
                self.irq_latch = (self.irq_latch & 0x0F) | ((value & 0x0F) << 4)
            elif reg == 2:
                self.irq_pending = False
                self.irq_control = value & 0x07
                if value & 2:
                    self.irq_counter = self.irq_latch
                    self.irq_prescale = 341
            elif reg == 3:
                self.irq_pending = False
                self.irq_control = (self.irq_control & ~2) | ((self.irq_control << 1) & 2)
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr[address // 0x400]
        return (bank * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not self.has_irq or not (self.irq_control & 2):
            return
        for _ in range(cycles):
            if self.irq_control & 4:
                # cycle mode
                self.irq_counter = (self.irq_counter + 1) & 0xFF
                if self.irq_counter == 0:
                    self.irq_counter = self.irq_latch
                    if self.irq_control & 1:
                        self.irq_pending = True
            else:
                self.irq_prescale -= 3
                if self.irq_prescale <= 0:
                    self.irq_prescale += 341
                    if self.irq_counter == 0xFF:
                        self.irq_counter = self.irq_latch
                        if self.irq_control & 1:
                            self.irq_pending = True
                    else:
                        self.irq_counter = (self.irq_counter + 1) & 0xFF


class Mapper21(_VRC2and4):
    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart, a0_mask=0x02, a1_mask=0x04, has_irq=True)


class Mapper22(_VRC2and4):
    """VRC2a — CHR banks shifted left by 1."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart, a0_mask=0x02, a1_mask=0x01, has_irq=False)

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr[address // 0x400] >> 1
        return (bank * 0x400 + (address & 0x3FF)) % len(self.cart.chr)


class Mapper23(_VRC2and4):
    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart, a0_mask=0x01, a1_mask=0x02, has_irq=True)


class Mapper25(_VRC2and4):
    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart, a0_mask=0x02, a1_mask=0x01, has_irq=True)


class Mapper24(Mapper):
    """Konami VRC6a banking + IRQ (expansion audio not mixed)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.prg16 = 0
        self.prg8 = 0
        self.chr = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_latch = 0
        self.irq_control = 0
        self.irq_counter = 0
        self.irq_prescale = 341

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count8 = max(1, len(self.cart.prg) // 0x2000)
        if address < 0xC000:
            bank = (self.prg16 % max(1, count8 // 2)) * 2 + (0 if address < 0xA000 else 1)
        elif address < 0xE000:
            bank = self.prg8 % count8
        else:
            bank = count8 - 1
        return bank * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        if address & 0xF000 == 0x8000:
            self.prg16 = value & 0x0F
        elif address & 0xF000 == 0x9000:
            pass  # pulse1 regs ignored
        elif address & 0xF000 == 0xA000:
            pass  # pulse2
        elif address & 0xF000 == 0xB000:
            if (address & 3) == 3:
                self.mirror = ("vertical", "horizontal", "single0", "single1")[value & 3]
            # saw / other ignored
        elif address & 0xF000 == 0xC000:
            self.prg8 = value & 0x1F
        elif address & 0xF000 == 0xD000:
            self.chr[address & 3] = value
        elif address & 0xF000 == 0xE000:
            self.chr[4 + (address & 3)] = value
        elif address & 0xF000 == 0xF000:
            reg = address & 3
            if reg == 0:
                self.irq_latch = value
            elif reg == 1:
                self.irq_pending = False
                self.irq_control = value & 0x07
                if value & 2:
                    self.irq_counter = self.irq_latch
                    self.irq_prescale = 341
            elif reg == 2:
                self.irq_pending = False
                self.irq_control = (self.irq_control & ~2) | ((self.irq_control << 1) & 2)
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not (self.irq_control & 2):
            return
        for _ in range(cycles):
            if self.irq_control & 4:
                self.irq_counter = (self.irq_counter + 1) & 0xFF
                if self.irq_counter == 0:
                    self.irq_counter = self.irq_latch
                    if self.irq_control & 1:
                        self.irq_pending = True
            else:
                self.irq_prescale -= 3
                if self.irq_prescale <= 0:
                    self.irq_prescale += 341
                    if self.irq_counter == 0xFF:
                        self.irq_counter = self.irq_latch
                        if self.irq_control & 1:
                            self.irq_pending = True
                    else:
                        self.irq_counter = (self.irq_counter + 1) & 0xFF


class Mapper26(Mapper24):
    """VRC6b — swapped A0/A1 relative to VRC6a."""

    def cpu_write(self, address: int, value: int) -> bool:
        # Translate VRC6b addressing into VRC6a layout: swap bits 0 and 1.
        bits = address & 3
        swapped = (address & 0xFFFC) | ((bits & 1) << 1) | ((bits & 2) >> 1)
        return Mapper24.cpu_write(self, swapped, value)


class Mapper69(Mapper):
    """Sunsoft FME-7 / 5B command mapper (AY audio not mixed)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.command = 0
        self.prg = [0, 0, 0, 0]
        self.chr = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_control = 0
        self.irq_counter = 0
        self.prg_ram_enable = True
        self.prg_ram_select = True

    def prg_ram_enabled(self) -> bool:
        return self.prg_ram_select and self.prg_ram_enable

    def prg_ram_writable(self) -> bool:
        return self.prg_ram_select and self.prg_ram_enable

    def cpu_read(self, address: int) -> Optional[int]:
        if 0x6000 <= address < 0x8000:
            if self.prg_ram_select:
                return None  # fall through to PRG-RAM in Cartridge
            count = max(1, len(self.cart.prg) // 0x2000)
            return (self.prg[0] % count) * 0x2000 + (address & 0x1FFF)
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        if address >= 0xE000:
            bank = count - 1
        else:
            bank = self.prg[(address - 0x8000) // 0x2000 + 1] % count
        return bank * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x6000 <= address < 0x8000:
            # ROM at $6000: swallow writes. RAM: let Cartridge handle when enabled.
            return not self.prg_ram_select
        if 0x8000 <= address <= 0x9FFF:
            self.command = value & 0x0F
            return True
        if 0xA000 <= address <= 0xBFFF:
            cmd = self.command
            if cmd < 8:
                self.chr[cmd] = value
            elif cmd == 8:
                # Bit 6 selects RAM (1) vs ROM (0) at $6000; bit 7 enables RAM.
                self.prg_ram_enable = bool(value & 0x80)
                self.prg_ram_select = bool(value & 0x40)
                self.prg[0] = value & 0x3F
            elif cmd in (9, 10, 11):
                self.prg[cmd - 8] = value & 0x3F
            elif cmd == 12:
                self.mirror = ("vertical", "horizontal", "single0", "single1")[value & 3]
            elif cmd == 13:
                self.irq_control = value
                self.irq_pending = False
            elif cmd == 14:
                self.irq_counter = (self.irq_counter & 0xFF00) | value
            elif cmd == 15:
                self.irq_counter = (self.irq_counter & 0x00FF) | (value << 8)
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not (self.irq_control & 0x80):
            return
        for _ in range(cycles):
            self.irq_counter = (self.irq_counter - 1) & 0xFFFF
            if self.irq_counter == 0xFFFF and (self.irq_control & 0x01):
                self.irq_pending = True


class Mapper19(Mapper):
    """Namco 163 banking + IRQ (wavetable audio not mixed)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.prg = [0, 0, 0]
        self.chr = [0] * 8
        self.mirror = [0, 0, 0, 0]
        self.irq_counter = 0
        self.irq_enabled = False
        self.chr_ram_enable = [True, True]

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        if address < 0xA000:
            bank = self.prg[0]
        elif address < 0xC000:
            bank = self.prg[1]
        elif address < 0xE000:
            bank = self.prg[2]
        else:
            bank = count - 1
        return (bank % count) * 0x2000 + (address & 0x1FFF)

    def register_read(self, address: int) -> Optional[int]:
        if 0x5000 <= address <= 0x57FF:
            return self.irq_counter & 0xFF
        if 0x5800 <= address <= 0x5FFF:
            return ((self.irq_counter >> 8) & 0x7F) | (0x80 if self.irq_enabled else 0)
        return None

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x5000 <= address <= 0x57FF:
            self.irq_counter = (self.irq_counter & 0xFF00) | value
            self.irq_pending = False
            return True
        if 0x5800 <= address <= 0x5FFF:
            self.irq_counter = (self.irq_counter & 0x00FF) | ((value & 0x7F) << 8)
            self.irq_enabled = bool(value & 0x80)
            self.irq_pending = False
            return True
        if address < 0x8000:
            return False
        if 0x8000 <= address <= 0xBFFF:
            # Eight 1 KiB CHR select registers, one per $800 window.
            self.chr[(address - 0x8000) // 0x800] = value
            return True
        if 0xC000 <= address <= 0xDFFF:
            # Nametable select registers — CIRAM handling approximated.
            return True
        if 0xE000 <= address <= 0xE7FF:
            self.prg[0] = value & 0x3F
            return True
        if 0xE800 <= address <= 0xEFFF:
            self.prg[1] = value & 0x3F
            self.chr_ram_enable[0] = not bool(value & 0x40)
            self.chr_ram_enable[1] = not bool(value & 0x80)
            return True
        if 0xF000 <= address <= 0xF7FF:
            self.prg[2] = value & 0x3F
            return True
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr[address // 0x400]
        return (bank * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def clock_cpu(self, cycles: int) -> None:
        if not self.irq_enabled:
            return
        for _ in range(cycles):
            self.irq_counter = (self.irq_counter + 1) & 0x7FFF
            if self.irq_counter == 0x7FFF:
                self.irq_pending = True
                self.irq_enabled = False


class Mapper32(Mapper):
    """Irem G-101."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg = [0, 0]
        self.chr = [0] * 8
        self.mode = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        last = count - 1
        if self.mode & 2:
            banks = [last - 1, self.prg[1] % count, self.prg[0] % count, last]
        else:
            banks = [self.prg[0] % count, self.prg[1] % count, last - 1 if last else 0, last]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        region = address & 0xF000
        if region == 0x8000:
            self.prg[0] = value & 0x1F
        elif region == 0x9000:
            self.mode = value & 3
            self.mirror = "horizontal" if value & 1 else "vertical"
        elif region == 0xA000:
            self.prg[1] = value & 0x1F
        elif region == 0xB000:
            self.chr[address & 7] = value
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper33(Mapper):
    """Taito TC0190 (mapper 33)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg = [0, 0]
        self.chr2 = [0, 0]  # 2 KiB banks
        self.chr1 = [0, 0, 0, 0]  # 1 KiB banks
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        banks = [self.prg[0] % count, self.prg[1] % count, max(0, count - 2), count - 1]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x8000 <= address <= 0x9FFF:
            idx = address & 3
            if idx == 0:
                self.prg[0] = value & 0x3F
                self.mirror = "horizontal" if value & 0x40 else "vertical"
            elif idx == 1:
                self.prg[1] = value & 0x3F
            elif idx == 2:
                self.chr2[0] = value
            else:
                self.chr2[1] = value
            return True
        if 0xA000 <= address <= 0xBFFF:
            self.chr1[address & 3] = value
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        if address < 0x800:
            bank = self.chr2[0] * 2 + (address // 0x400)
        elif address < 0x1000:
            bank = self.chr2[1] * 2 + ((address - 0x800) // 0x400)
        else:
            bank = self.chr1[(address - 0x1000) // 0x400]
        return (bank * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper48(Mapper33):
    """Taito TC0690 — TC0190 + MMC3-like scanline IRQ."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_enabled = False
        self.irq_reload = False

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x8000 <= address <= 0x9FFF:
            idx = address & 3
            if idx == 0:
                self.prg[0] = value & 0x3F
            elif idx == 1:
                self.prg[1] = value & 0x3F
            elif idx == 2:
                self.chr2[0] = value
            else:
                self.chr2[1] = value
            return True
        if 0xA000 <= address <= 0xBFFF:
            self.chr1[address & 3] = value
            return True
        if 0xC000 <= address <= 0xDFFF:
            if address & 1:
                self.irq_reload = True
            else:
                self.irq_latch = value ^ 0xFF
            return True
        if 0xE000 <= address <= 0xFFFF:
            if address & 1:
                self.mirror = "horizontal" if value & 1 else "vertical"
            else:
                self.irq_enabled = bool(value & 1)
                if not self.irq_enabled:
                    self.irq_pending = False
            return True
        return False

    def clock_scanline(self) -> None:
        if self.irq_counter == 0 or self.irq_reload:
            self.irq_counter = self.irq_latch
            self.irq_reload = False
        else:
            self.irq_counter = (self.irq_counter - 1) & 0xFF
        if self.irq_counter == 0 and self.irq_enabled:
            self.irq_pending = True


class Mapper65(Mapper):
    """Irem H3001."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.prg = [0, 1, 0xFE]
        self.chr = [0] * 8
        self.irq_enabled = False
        self.irq_counter = 0
        self.irq_latch = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        banks = [self.prg[0] % count, self.prg[1] % count, self.prg[2] % count, count - 1]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        if address == 0x8000:
            self.prg[0] = value
        elif address == 0xA000:
            self.prg[1] = value
        elif address == 0xC000:
            self.prg[2] = value
        elif 0xB000 <= address <= 0xB007:
            self.chr[address & 7] = value
        elif address == 0x9001:
            self.mirror = "horizontal" if value & 0x80 else "vertical"
        elif address == 0x9003:
            self.irq_enabled = bool(value & 0x80)
            self.irq_pending = False
        elif address == 0x9004:
            self.irq_counter = self.irq_latch
            self.irq_pending = False
        elif address == 0x9005:
            self.irq_latch = (self.irq_latch & 0x00FF) | (value << 8)
        elif address == 0x9006:
            self.irq_latch = (self.irq_latch & 0xFF00) | value
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not self.irq_enabled:
            return
        for _ in range(cycles):
            if self.irq_counter == 0:
                self.irq_pending = True
                self.irq_enabled = False
            else:
                self.irq_counter = (self.irq_counter - 1) & 0xFFFF


class Mapper68(Mapper):
    """Sunsoft-4."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr = [0, 0, 0, 0]
        self.nt = [0, 0]
        self.mirror_reg = 0
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        region = address & 0xF000
        if region == 0x8000:
            self.chr[0] = value
        elif region == 0x9000:
            self.chr[1] = value
        elif region == 0xA000:
            self.chr[2] = value
        elif region == 0xB000:
            self.chr[3] = value
        elif region == 0xC000:
            self.nt[0] = value | 0x80
        elif region == 0xD000:
            self.nt[1] = value | 0x80
        elif region == 0xE000:
            self.mirror_reg = value
            modes = ("vertical", "horizontal", "single0", "single1")
            self.mirror = modes[value & 3]
        elif region == 0xF000:
            self.prg_bank = value & 0x0F
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr[address // 0x800]
        return (bank * 0x800 + (address & 0x7FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper16(Mapper):
    """Bandai FCG-1/2 / LZ93D50 with minimal 24Cxx EEPROM bit-bang."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.prg_bank = 0
        self.chr = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_enabled = False
        self.irq_counter = 0
        # 24C01/02 style EEPROM (128–256 bytes); persisted via battery .sav tail.
        self.eeprom = bytearray(256)
        self._eeprom_bit = 1
        self._eeprom_latch = 0
        self._eeprom_addr = 0
        self._eeprom_state = 0  # 0 idle, 1 cmd, 2 addr, 3 data
        self._eeprom_bits = 0
        self._eeprom_shift = 0
        self._eeprom_read = False
        if cart.battery and len(cart.prg_ram) >= 0x2100:
            self.eeprom[:] = cart.prg_ram[0x2000:0x2100]

    def _persist_eeprom(self) -> None:
        if self.cart.battery and len(self.cart.prg_ram) >= 0x2100:
            self.cart.prg_ram[0x2000:0x2100] = self.eeprom

    def cpu_data(self, address: int) -> Optional[int]:
        if 0x6000 <= address < 0x8000:
            # Bit 4 = EEPROM data out (idle high).
            return 0x10 if self._eeprom_bit else 0x00
        return None

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, len(self.cart.prg) // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def _eeprom_clock(self, value: int) -> None:
        """Very small I2C subset — enough for Bandai commercial save boots."""
        scl = bool(value & 0x20)
        sda = bool(value & 0x40)
        prev = self._eeprom_latch
        prev_scl, prev_sda = bool(prev & 0x20), bool(prev & 0x40)
        self._eeprom_latch = value & 0x60
        # START: SDA falls while SCL high
        if prev_scl and scl and prev_sda and not sda:
            self._eeprom_state = 1
            self._eeprom_bits = 0
            self._eeprom_shift = 0
            self._eeprom_bit = 1
            return
        # STOP: SDA rises while SCL high
        if prev_scl and scl and (not prev_sda) and sda:
            self._eeprom_state = 0
            self._eeprom_bit = 1
            self._persist_eeprom()
            return
        if not (scl and not prev_scl):
            return
        # Rising SCL samples SDA
        if self._eeprom_state == 0:
            return
        if self._eeprom_read and self._eeprom_state == 3:
            bit = (self.eeprom[self._eeprom_addr & 0xFF] >> (7 - self._eeprom_bits)) & 1
            self._eeprom_bit = bit
            self._eeprom_bits += 1
            if self._eeprom_bits >= 8:
                self._eeprom_bits = 0
                self._eeprom_addr = (self._eeprom_addr + 1) & 0xFF
                self._eeprom_state = 1  # expect ACK from master next byte / stop
            return
        self._eeprom_shift = ((self._eeprom_shift << 1) | int(sda)) & 0xFF
        self._eeprom_bits += 1
        self._eeprom_bit = 0  # ACK low after each byte
        if self._eeprom_bits < 8:
            return
        self._eeprom_bits = 0
        byte = self._eeprom_shift
        if self._eeprom_state == 1:
            self._eeprom_read = bool(byte & 1)
            self._eeprom_state = 3 if self._eeprom_read else 2
        elif self._eeprom_state == 2:
            self._eeprom_addr = byte
            self._eeprom_state = 3
        elif self._eeprom_state == 3 and not self._eeprom_read:
            self.eeprom[self._eeprom_addr & 0xFF] = byte
            self._eeprom_addr = (self._eeprom_addr + 1) & 0xFF

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x6000:
            return False
        reg = address & 0x000F
        if reg < 8:
            self.chr[reg] = value
        elif reg == 8:
            self.prg_bank = value & 0x0F
        elif reg == 9:
            self.mirror = ("vertical", "horizontal", "single0", "single1")[value & 3]
        elif reg == 0xA:
            self.irq_enabled = bool(value & 1)
            self.irq_pending = False
        elif reg == 0xB:
            self.irq_counter = (self.irq_counter & 0xFF00) | value
        elif reg == 0xC:
            self.irq_counter = (self.irq_counter & 0x00FF) | (value << 8)
        elif reg in (0xD, 0xE, 0xF):
            self._eeprom_clock(value)
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not self.irq_enabled:
            return
        for _ in range(cycles):
            if self.irq_counter == 0:
                self.irq_pending = True
                self.irq_enabled = False
            else:
                self.irq_counter = (self.irq_counter - 1) & 0xFFFF


class Mapper153(Mapper16):
    """Bandai LZ93D50 + WRAM (Famicom Jump II)."""

    def prg_ram_enabled(self) -> bool:
        return True

    def cpu_data(self, address: int) -> Optional[int]:
        return None


class Mapper159(Mapper16):
    """Bandai LZ93D50 + 24C01 EEPROM (Dragon Ball Z, Crayon Shin-chan, …)."""


class Mapper18(Mapper):
    """Jaleco SS88006."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg = [0, 0, 0]
        self.chr = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_enabled = False
        self.irq_counter = 0
        self.irq_latch = 0
        self.irq_mask = 0xFFFF

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        banks = [self.prg[0] % count, self.prg[1] % count, self.prg[2] % count, count - 1]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    @staticmethod
    def _nibble(current: int, address: int, value: int) -> int:
        if address & 1:
            return (current & 0x0F) | (value << 4)
        return (current & 0xF0) | value

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        # Registers repeat every $1000 with two bits of sub-select.
        address = address & 0xF003
        value &= 0x0F
        if 0x8000 <= address <= 0x8003:
            slot = 0 if (address & 3) < 2 else 1
            self.prg[slot] = self._nibble(self.prg[slot], address, value)
        elif 0x9000 <= address <= 0x9001:
            self.prg[2] = self._nibble(self.prg[2], address, value)
        elif 0xA000 <= address <= 0xD003:
            chr_index = ((address - 0xA000) // 0x1000) * 2 + ((address >> 1) & 1)
            self.chr[chr_index] = self._nibble(self.chr[chr_index], address, value)
        elif address == 0xE000:
            self.irq_latch = (self.irq_latch & 0xFFF0) | value
        elif address == 0xE001:
            self.irq_latch = (self.irq_latch & 0xFF0F) | (value << 4)
        elif address == 0xE002:
            self.irq_latch = (self.irq_latch & 0xF0FF) | (value << 8)
        elif address == 0xE003:
            self.irq_latch = (self.irq_latch & 0x0FFF) | (value << 12)
        elif address == 0xF000:
            self.irq_counter = self.irq_latch
            self.irq_pending = False
        elif address == 0xF001:
            self.irq_enabled = bool(value & 1)
            self.irq_mask = (0xFFFF, 0x0FFF, 0x00FF, 0x000F)[(value >> 1) & 3]
            self.irq_pending = False
        elif address == 0xF002:
            self.mirror = ("horizontal", "vertical", "single0", "single1")[value & 3]
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not self.irq_enabled:
            return
        for _ in range(cycles):
            counter = self.irq_counter & self.irq_mask
            if counter == 0:
                self.irq_pending = True
            self.irq_counter = (self.irq_counter - 1) & 0xFFFF


class Mapper5(Mapper):
    """MMC5 (ExROM) — PRG/CHR banking, multiplier, scanline IRQ; ExAttr/audio simplified."""

    clocks_prerender = False

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_mode = 3
        self.chr_mode = 0
        self.prg_regs = [0xFF, 0xFF, 0xFF, 0xFF, 0xFF]
        self.chr_regs = [0] * 12
        self.mirror = cart.header_mirroring
        self.fill_tile = 0
        self.fill_attr = 0
        self.irq_scanline = 0
        self.irq_enabled = False
        self.irq_status = 0
        self.mul = [0xFF, 0xFF]
        self.exram = bytearray(0x400)
        self.exram_mode = 0
        self.protect = 0
        self.chr_hi = 0
        self._scan = 0
        self.split_mode = 0
        self.split_scroll = 0
        self.split_bank = 0

    def register_read(self, address: int) -> Optional[int]:
        if 0x5C00 <= address <= 0x5FFF:
            return self.exram[address & 0x3FF]
        if address == 0x5204:
            value = self.irq_status
            self.irq_status &= ~0x80
            self.irq_pending = False
            return value
        if address in (0x5205, 0x5206):
            product = self.mul[0] * self.mul[1]
            return (product >> (8 if address == 0x5206 else 0)) & 0xFF
        return None

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        mode = self.prg_mode & 3
        regs = [r & 0x7F for r in self.prg_regs]
        if mode == 0:
            bank = (regs[4] & 0x7C) % max(1, count)
            return bank * 0x2000 + (address & 0x7FFF)
        if mode == 1:
            if address < 0xC000:
                bank = (regs[2] & 0x7E) % count
                return bank * 0x2000 + (address & 0x3FFF)
            bank = (regs[4] & 0x7E) % count
            return bank * 0x2000 + (address & 0x3FFF)
        if mode == 2:
            if address < 0xC000:
                bank = (regs[2] & 0x7E) % count
                return bank * 0x2000 + (address & 0x3FFF)
            if address < 0xE000:
                bank = regs[3] % count
            else:
                bank = regs[4] % count
            return bank * 0x2000 + (address & 0x1FFF)
        # mode 3: 8KB
        banks = [regs[1] % count, regs[2] % count, regs[3] % count, regs[4] % count]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address == 0x5100:
            self.prg_mode = value & 3
            return True
        if address == 0x5101:
            self.chr_mode = value & 3
            return True
        if address == 0x5102:
            self.protect = (self.protect & 0x2) | (value & 1)
            return True
        if address == 0x5103:
            self.protect = (self.protect & 0x1) | ((value & 1) << 1)
            return True
        if address == 0x5104:
            self.exram_mode = value & 3
            return True
        if address == 0x5105:
            # $5105 packs one 2-bit nametable source per quadrant.
            known = {0x50: "horizontal", 0x44: "vertical", 0x00: "single0", 0x55: "single1"}
            self.mirror = known.get(value, "vertical" if (value & 3) != ((value >> 2) & 3) else "horizontal")
            return True
        if address == 0x5106:
            self.fill_tile = value
            return True
        if address == 0x5107:
            self.fill_attr = value & 3
            return True
        if 0x5113 <= address <= 0x5117:
            self.prg_regs[address - 0x5113] = value
            return True
        if 0x5120 <= address <= 0x512B:
            self.chr_regs[address - 0x5120] = value
            return True
        if address == 0x5130:
            self.chr_hi = value & 3
            return True
        if address == 0x5200:
            self.split_mode = value
            return True
        if address == 0x5201:
            self.split_scroll = value
            return True
        if address == 0x5202:
            self.split_bank = value
            return True
        if address == 0x5203:
            self.irq_scanline = value
            return True
        if address == 0x5204:
            self.irq_enabled = bool(value & 0x80)
            if not self.irq_enabled:
                self.irq_pending = False
            return True
        if address in (0x5205, 0x5206):
            self.mul[address - 0x5205] = value
            return True
        if 0x5C00 <= address <= 0x5FFF:
            if self.exram_mode <= 1:
                self.exram[address & 0x3FF] = value
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        mode = self.chr_mode & 3
        regs = self.chr_regs
        hi = self.chr_hi << 8
        if mode == 0:
            bank = (hi | regs[7]) * 8
            return ((bank + address // 0x400) * 0x400 + (address & 0x3FF)) % len(self.cart.chr)
        if mode == 1:
            idx = 3 if address < 0x1000 else 7
            bank = (hi | regs[idx]) * 4
            return ((bank + (address & 0xFFF) // 0x400) * 0x400 + (address & 0x3FF)) % len(self.cart.chr)
        if mode == 2:
            idx = (1 if address < 0x800 else 3 if address < 0x1000 else 5 if address < 0x1800 else 7)
            bank = (hi | regs[idx]) * 2
            return ((bank + ((address & 0x7FF) // 0x400)) * 0x400 + (address & 0x3FF)) % len(self.cart.chr)
        bank = hi | regs[address // 0x400]
        return (bank * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_scanline(self) -> None:
        # Visible in-frame lines only (clocks_prerender = False).
        self._scan += 1
        self.irq_status |= 0x40
        if self._scan == self.irq_scanline:
            self.irq_status |= 0x80
            if self.irq_enabled:
                self.irq_pending = True
        if self._scan >= 240:
            self._scan = 0
            self.irq_status &= ~0x40


class Mapper64(Mapper4):
    """Tengen RAMBO-1 — MMC3-style banking with a third PRG register and
    1 KiB CHR mode; the cycle-mode IRQ is approximated by the scanline
    counter inherited from Mapper4."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.regs = [0] * 16

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        last = count - 1
        r6, r7, r15 = self.regs[6] % count, self.regs[7] % count, self.regs[15] % count
        if self.select & 0x40:
            banks = (r15, r6, r7, last)
        else:
            banks = (r6, r7, r15, last)
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        even = not (address & 1)
        region = address & 0xE000
        if region == 0x8000:
            if even:
                self.select = value
            else:
                self.regs[self.select & 0x0F] = value
        elif region == 0xA000:
            if even and self.cart.header_mirroring != "four":
                self.mirror = "horizontal" if value & 1 else "vertical"
        elif region == 0xC000:
            if even:
                self.irq_latch = value
            else:
                self.irq_reload = True
        elif region == 0xE000:
            if even:
                self.irq_enabled = False
                self.irq_pending = False
            else:
                self.irq_enabled = True
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        regs = self.regs
        if self.select & 0x20:
            # 1 KiB CHR mode: R0,R8,R1,R9 cover $0000-$0FFF.
            low = (regs[0], regs[8], regs[1], regs[9])
            banks = low + (regs[2], regs[3], regs[4], regs[5])
        else:
            banks = (
                regs[0] & 0xFE, (regs[0] & 0xFE) + 1,
                regs[1] & 0xFE, (regs[1] & 0xFE) + 1,
                regs[2], regs[3], regs[4], regs[5],
            )
        logical = address ^ (0x1000 if self.select & 0x80 else 0)
        bank = banks[logical // 0x400]
        return (bank * 0x400 + (logical & 0x3FF)) % len(self.cart.chr)


class Mapper85(Mapper):
    """Konami VRC7 banking + IRQ (FM audio not mixed)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.needs_cpu_clock = True
        self.prg = [0, 0, 0]
        self.chr = [0] * 8
        self.mirror = cart.header_mirroring
        self.irq_latch = 0
        self.irq_control = 0
        self.irq_counter = 0
        self.irq_prescale = 341

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = max(1, len(self.cart.prg) // 0x2000)
        banks = [self.prg[0] % count, self.prg[1] % count, self.prg[2] % count, count - 1]
        slot = (address - 0x8000) // 0x2000
        return banks[slot] * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        # VRC7 uses sparse selects; accept broad masks
        if 0x8000 <= address <= 0x800F:
            self.prg[0] = value & 0x3F
        elif 0x8010 <= address <= 0x801F:
            self.prg[1] = value & 0x3F
        elif 0x9000 <= address <= 0x900F:
            self.prg[2] = value & 0x3F
        elif 0xA000 <= address <= 0xA00F:
            self.chr[0] = value
        elif 0xA010 <= address <= 0xA01F:
            self.chr[1] = value
        elif 0xB000 <= address <= 0xB00F:
            self.chr[2] = value
        elif 0xB010 <= address <= 0xB01F:
            self.chr[3] = value
        elif 0xC000 <= address <= 0xC00F:
            self.chr[4] = value
        elif 0xC010 <= address <= 0xC01F:
            self.chr[5] = value
        elif 0xD000 <= address <= 0xD00F:
            self.chr[6] = value
        elif 0xD010 <= address <= 0xD01F:
            self.chr[7] = value
        elif 0xE000 <= address <= 0xE00F:
            self.mirror = ("vertical", "horizontal", "single0", "single1")[value & 3]
        elif 0xE010 <= address <= 0xE01F:
            self.irq_latch = value
        elif 0xF000 <= address <= 0xF00F:
            self.irq_pending = False
            self.irq_control = value & 0x07
            if value & 2:
                self.irq_counter = self.irq_latch
                self.irq_prescale = 341
        elif 0xF010 <= address <= 0xF01F:
            self.irq_pending = False
            self.irq_control = (self.irq_control & ~2) | ((self.irq_control << 1) & 2)
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address // 0x400] * 0x400 + (address & 0x3FF)) % len(self.cart.chr)

    def mirror_mode(self) -> str:
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not (self.irq_control & 2):
            return
        for _ in range(cycles):
            if self.irq_control & 4:
                self.irq_counter = (self.irq_counter + 1) & 0xFF
                if self.irq_counter == 0:
                    self.irq_counter = self.irq_latch
                    if self.irq_control & 1:
                        self.irq_pending = True
            else:
                self.irq_prescale -= 3
                if self.irq_prescale <= 0:
                    self.irq_prescale += 341
                    if self.irq_counter == 0xFF:
                        self.irq_counter = self.irq_latch
                        if self.irq_control & 1:
                            self.irq_pending = True
                    else:
                        self.irq_counter = (self.irq_counter + 1) & 0xFF


class Mapper155(Mapper1):
    """MMC1A variant (PRG-RAM protect ignored)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_ram_disable = False

    def cpu_write(self, address: int, value: int) -> bool:
        # MMC1A ignores WRAM protect bit in the PRG register.
        handled = super().cpu_write(address, value)
        self.prg_ram_disable = False
        return handled


class Mapper210(Mapper19):
    """Namco 175/340 — Namco 163 without IRQ/audio."""

    def clock_cpu(self, cycles: int) -> None:
        pass


class Mapper70(Mapper):
    """Bandai — 16 KiB PRG + 8 KiB CHR (Family Trainer / Kamen no Ninja)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, self.cart.prg_len // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        self.chr_bank = value & 0x0F
        self.prg_bank = (value >> 4) & 0x0F
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        banks = max(1, self.cart.chr_len // 0x2000)
        return ((self.chr_bank % banks) * 0x2000 + address) % self.cart.chr_len


class Mapper72(Mapper):
    """Jaleco JF-17/19 — latched PRG/CHR (Pinball Quest, Moero Pro Tennis)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0
        self.latch = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, self.cart.prg_len // 0x4000)
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        if value & 0x80:
            self.prg_bank = self.latch & 0x0F
        if value & 0x40:
            self.chr_bank = self.latch & 0x0F
        self.latch = value
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        banks = max(1, self.cart.chr_len // 0x2000)
        return ((self.chr_bank % banks) * 0x2000 + address) % self.cart.chr_len


class Mapper76(Mapper):
    """Namco 109 — 2 KiB CHR banks (Digital Devil Story)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.bank_select = 0
        self.prg = [0, 1]
        self.chr = [0, 1, 2, 3]

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = self.cart.prg_8k
        if address < 0xA000:
            bank = self.prg[0] % count
        elif address < 0xC000:
            bank = self.prg[1] % count
        elif address < 0xE000:
            bank = (count - 2) % count
        else:
            bank = (count - 1) % count
        return bank * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        if (address & 1) == 0:
            self.bank_select = value & 7
        else:
            reg = self.bank_select
            if reg <= 3:
                self.chr[reg] = value
            elif reg in (6, 7):
                self.prg[reg - 6] = value
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = self.chr[address // 0x800] % max(1, self.cart.chr_len // 0x800)
        return bank * 0x800 + (address & 0x7FF)


class Mapper80(Mapper):
    """Taito X1-005 — CHR/PRG + $7F00–$7FFF RAM mirror."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg = [0, 0, 0]
        self.chr = [0] * 6
        self.mirror = cart.header_mirroring

    def cpu_read(self, address: int) -> Optional[int]:
        if 0x7F00 <= address <= 0x7FFF:
            return None  # 128B RAM mirror via prg_ram
        if address < 0x8000:
            return None
        count = self.cart.prg_8k
        if address < 0xA000:
            bank = self.prg[0] % count
        elif address < 0xC000:
            bank = self.prg[1] % count
        elif address < 0xE000:
            bank = self.prg[2] % count
        else:
            bank = count - 1
        return bank * 0x2000 + (address & 0x1FFF)

    def prg_ram_index(self, address: int) -> int:
        if 0x7F00 <= address <= 0x7FFF:
            return 0x1F00 + (address & 0x7F)
        return address & 0x1FFF

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x7E00 <= address <= 0x7EFF:
            reg = address & 0x0F
            if reg < 6:
                self.chr[reg] = value
            elif reg in (6, 7, 8):
                self.prg[reg - 6] = value & 0x1F
            elif reg == 0xE:
                self.mirror = "horizontal" if value & 1 else "vertical"
            return True
        if 0x7F00 <= address <= 0x7FFF:
            return False  # RAM
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        if address < 0x1000:
            bank = self.chr[address // 0x400]
            return (bank * 0x400 + (address & 0x3FF)) % self.cart.chr_len
        bank = self.chr[4 + (address - 0x1000) // 0x800]
        return (bank * 0x800 + (address & 0x7FF)) % self.cart.chr_len

    def mirror_mode(self) -> str:
        return self.mirror


class Mapper86(Mapper):
    """Jaleco JF-13 — Moero!! Pro Yakyuu / City Connection (JP)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, self.cart.prg_len // 0x8000)
        return (self.prg_bank % banks) * 0x8000 + (address & 0x7FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x6000 <= address <= 0x6FFF:
            self.prg_bank = (value >> 4) & 3
            self.chr_bank = (value & 3) | ((value >> 4) & 4)
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        banks = max(1, self.cart.chr_len // 0x2000)
        return ((self.chr_bank % banks) * 0x2000 + address) % self.cart.chr_len


class Mapper88(Mapper4):
    """Namco 118 — MMC3-like CHR with bit-6 nametable select quirk."""

    def mirror_mode(self) -> str:
        # CIRAM A10 from CHR bank bit 6 (approximate as single from CHR0).
        return "single1" if (self.regs[0] & 0x40) else "single0"

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        even = not (address & 1)
        region = address & 0xE000
        if region == 0x8000:
            if even:
                self.select = value
                self._chr_xor = 0x1000 if value & 0x80 else 0
            else:
                register = self.select & 7
                if register in (0, 1):
                    self.regs[register] = value & 0x3F
                elif register in (6, 7):
                    self.regs[register] = value & 0x0F
                else:
                    self.regs[register] = value & 0x3F
                if register <= 5:
                    self._rebuild_chr()
            return True
        if region == 0xA000:
            return True  # mirroring from CHR bits
        return super().cpu_write(address, value)


class Mapper95(Mapper4):
    """Namco TLSROM — CIRAM A10 from CHR bank bit 5."""

    def mirror_mode(self) -> str:
        return "single1" if (self.regs[0] & 0x20) else "single0"

    def cpu_write(self, address: int, value: int) -> bool:
        if (address & 0xE000) == 0xA000 and not (address & 1):
            return True  # ignore MMC3 mirror reg
        return super().cpu_write(address, value)


class Mapper232(Mapper):
    """BF9096 Quattro — Camerica multicarts (Quattro Adventure/Arcade/Sports)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.outer = 0
        self.inner = 0

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        if address < 0xC000:
            self.outer = (value >> 3) & 3
        else:
            self.inner = value & 3
        return True

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, self.cart.prg_len // 0x4000)
        block = (self.outer & 3) * 4
        if address < 0xC000:
            bank = (block + (self.inner & 3)) % banks
        else:
            bank = (block + 3) % banks
        return bank * 0x4000 + (address & 0x3FFF)

    def ppu_read(self, address: int) -> Optional[int]:
        if address < 0x2000:
            return address % self.cart.chr_len
        return None



# ---------------------------------------------------------------------------
# Additional / corrected boards (0.1.1a)
# ---------------------------------------------------------------------------
# A mapper's mirror_mode() may also return a 4-tuple of physical nametable
# pages (0-3) for boards that pick CIRAM A10 per quadrant.

class Mapper80(Mapper):
    """Taito X1-005 — 2x2K + 4x1K CHR, 3x8K PRG, 128 B RAM at $7F00."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr = [0, 2, 4, 5, 6, 7]
        self.prg = [0, 1, 2]
        self.mirror = cart.header_mirroring
        self.ram_enabled = True

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = self.cart.prg_8k
        slot = (address - 0x8000) >> 13
        bank = self.prg[slot] if slot < 3 else count - 1
        return (bank % count) * 0x2000 + (address & 0x1FFF)

    def prg_ram_enabled(self) -> bool:
        return self.ram_enabled

    def prg_ram_index(self, address: int) -> int:
        return 0x1F00 + (address & 0x7F) if address >= 0x7F00 else address & 0x1FFF

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x7EF0 <= address <= 0x7EFF:
            reg = address & 0x0F
            if reg <= 5:
                self.chr[reg] = value
            elif reg in (6, 7):
                self.mirror = "vertical" if value & 1 else "horizontal"
            elif reg in (8, 9):
                self.ram_enabled = value == 0xA3
            else:
                self.prg[(reg - 0x0A) >> 1] = value
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        clen = self.cart.chr_len
        if address < 0x1000:
            bank = self.chr[address >> 11] & 0xFE
            return (bank * 0x400 + (address & 0x7FF)) % clen
        bank = self.chr[2 + ((address - 0x1000) >> 10)]
        return (bank * 0x400 + (address & 0x3FF)) % clen

    def mirror_mode(self):
        return self.mirror


class Mapper207(Mapper80):
    """Taito X1-005 (alt.) — nametables chosen by CHR register bit 7."""

    def mirror_mode(self):
        a = (self.chr[0] >> 7) & 1
        b = (self.chr[1] >> 7) & 1
        return (a, a, b, b)


class Mapper82(Mapper):
    """Taito X1-017 — CHR A12 inversion, PRG regs >> 2, 5 KiB WRAM."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr = [0, 2, 4, 5, 6, 7]
        self.prg = [0, 1, 2]
        self.control = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        count = self.cart.prg_8k
        slot = (address - 0x8000) >> 13
        bank = self.prg[slot] if slot < 3 else count - 1
        return (bank % count) * 0x2000 + (address & 0x1FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x7EF0 <= address <= 0x7EFF:
            reg = address & 0x0F
            if reg <= 5:
                self.chr[reg] = value
            elif reg == 6:
                self.control = value
            elif 0x0A <= reg <= 0x0C:
                self.prg[reg - 0x0A] = value >> 2
            return True
        return False

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        clen = self.cart.chr_len
        logical = address ^ (0x1000 if self.control & 2 else 0)
        if logical < 0x1000:
            bank = self.chr[logical >> 11] & 0xFE
            return (bank * 0x400 + (logical & 0x7FF)) % clen
        bank = self.chr[2 + ((logical - 0x1000) >> 10)]
        return (bank * 0x400 + (logical & 0x3FF)) % clen

    def mirror_mode(self):
        return "vertical" if self.control & 1 else "horizontal"


class Mapper88(Mapper206):
    """Namco 118 (NAMCOT-3443) — CHR A16 high for the $1000 pattern table."""

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        regs = self.regs
        clen = self.cart.chr_len
        if address < 0x1000:
            bank = (regs[address >> 11] & 0x3E) | ((address >> 10) & 1)
        else:
            bank = (regs[2 + ((address - 0x1000) >> 10)] & 0x3F) | 0x40
        return (bank * 0x400 + (address & 0x3FF)) % clen

    def mirror_mode(self):
        return self.cart.header_mirroring


class Mapper154(Mapper88):
    """Namco 118 with one-screen mirroring from data bit 6 (Devil Man)."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.single = 0

    def cpu_write(self, address: int, value: int) -> bool:
        if address >= 0x8000:
            self.single = (value >> 6) & 1
        return super().cpu_write(address, value)

    def mirror_mode(self):
        return "single1" if self.single else "single0"


class Mapper95(Mapper206):
    """Namco 3425 (Dragon Buster) — CIRAM A10 from CHR register bit 5."""

    def mirror_mode(self):
        a = (self.regs[0] >> 5) & 1
        b = (self.regs[1] >> 5) & 1
        return (a, a, b, b)


class Mapper47(Mapper4):
    """NES-QJ multicart — MMC3 with a 128 KiB outer bank at $6000."""

    def __init__(self, cart: "Cartridge") -> None:
        self.outer = 0
        super().__init__(cart)

    def reset(self) -> None:
        super().reset()
        self.outer = 0

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x6000 <= address < 0x8000:
            self.outer = value & 1
            self._rebuild_chr()
            return True
        return super().cpu_write(address, value)

    def cpu_read(self, address: int) -> Optional[int]:
        mapped = super().cpu_read(address)
        if mapped is None:
            return None
        bank = (mapped >> 13) & 0x0F
        return ((self.outer << 4 | bank) % self.cart.prg_8k) * 0x2000 + (mapped & 0x1FFF)

    def ppu_read(self, address: int) -> Optional[int]:
        mapped = super().ppu_read(address)
        if mapped is None:
            return None
        bank = (mapped >> 10) & 0x7F
        return ((self.outer << 7 | bank) * 0x400 + (mapped & 0x3FF)) % self.cart.chr_len


class Mapper92(Mapper72):
    """Jaleco JF-19/21 — like mapper 72 but the $C000 bank is switchable."""

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = max(1, self.cart.prg_len // 0x4000)
        bank = 0 if address < 0xC000 else self.prg_bank % banks
        return bank * 0x4000 + (address & 0x3FFF)


class Mapper30(Mapper):
    """UNROM 512 (homebrew) — 16 KiB PRG, 4x8 KiB banked CHR-RAM, 1-screen."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0
        self.single = 0

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = self.cart.prg_16k
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        self.prg_bank = value & 0x1F
        self.chr_bank = (value >> 5) & 3
        self.single = (value >> 7) & 1
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr_bank * 0x2000 + address) % self.cart.chr_len

    def mirror_mode(self):
        if self.cart.header_mirroring == "four":
            return "single1" if self.single else "single0"
        return self.cart.header_mirroring


class Mapper67(Mapper):
    """Sunsoft-3 (Fantasy Zone II, After Burner) — 2K CHR, 16-bit CPU IRQ."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.chr = [0, 1, 2, 3]
        self.prg_bank = 0
        self.mirror = cart.header_mirroring
        self.irq_counter = 0
        self.irq_enabled = False
        self.irq_toggle = False
        self.needs_cpu_clock = True

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = self.cart.prg_16k
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        reg = address & 0xF800
        if reg in (0x8800, 0x9800, 0xA800, 0xB800):
            self.chr[(reg - 0x8800) >> 12] = value
        elif reg == 0xC800:
            if self.irq_toggle:
                self.irq_counter = (self.irq_counter & 0xFF00) | value
            else:
                self.irq_counter = (self.irq_counter & 0x00FF) | (value << 8)
            self.irq_toggle = not self.irq_toggle
        elif reg == 0xD800:
            self.irq_enabled = bool(value & 0x10)
            self.irq_toggle = False
            self.irq_pending = False
        elif reg == 0xE800:
            self.mirror = ("vertical", "horizontal", "single0", "single1")[value & 3]
        elif reg == 0xF800:
            self.prg_bank = value & 0x0F
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return (self.chr[address >> 11] * 0x800 + (address & 0x7FF)) % self.cart.chr_len

    def mirror_mode(self):
        return self.mirror

    def clock_cpu(self, cycles: int) -> None:
        if not self.irq_enabled:
            return
        counter = self.irq_counter - cycles
        if counter < 0:
            counter &= 0xFFFF
            self.irq_enabled = False
            self.irq_pending = True
        self.irq_counter = counter


class Mapper73(Mapper):
    """Konami VRC3 (Salamander JP) — 16K PRG, 16/8-bit CPU-cycle IRQ."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.irq_latch = 0
        self.irq_counter = 0
        self.irq_control = 0
        self.needs_cpu_clock = True

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        banks = self.cart.prg_16k
        bank = self.prg_bank % banks if address < 0xC000 else banks - 1
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        reg = address & 0xF000
        if reg <= 0xB000:
            shift = ((reg - 0x8000) >> 12) * 4
            self.irq_latch = (self.irq_latch & ~(0xF << shift)) | ((value & 0xF) << shift)
        elif reg == 0xC000:
            self.irq_control = value & 7
            self.irq_pending = False
            if value & 2:
                self.irq_counter = self.irq_latch
        elif reg == 0xD000:
            self.irq_pending = False
            ctl = self.irq_control
            self.irq_control = (ctl & ~2) | ((ctl & 1) << 1)
        elif reg == 0xF000:
            self.prg_bank = value & 7
        return True

    def clock_cpu(self, cycles: int) -> None:
        if not self.irq_control & 2:
            return
        if self.irq_control & 4:          # 8-bit mode: only the low byte counts
            low = (self.irq_counter & 0xFF) + cycles
            if low > 0xFF:
                self.irq_counter = (self.irq_counter & 0xFF00) | (self.irq_latch & 0xFF)
                self.irq_pending = True
            else:
                self.irq_counter = (self.irq_counter & 0xFF00) | low
        else:
            value = self.irq_counter + cycles
            if value > 0xFFFF:
                self.irq_counter = self.irq_latch
                self.irq_pending = True
            else:
                self.irq_counter = value


class Mapper77(Mapper):
    """Irem (Napoleon Senki) — 32K PRG, 2K CHR-ROM + 6K CHR-RAM, 4-screen."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.prg_bank = 0
        self.chr_bank = 0
        self.ram_base = len(cart.chr)
        cart.chr.extend(bytearray(0x2000))
        cart.chr_len = len(cart.chr)

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        return (self.prg_bank % self.cart.prg_32k) * 0x8000 + (address & 0x7FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if address < 0x8000:
            return False
        self.prg_bank = value & 0x0F
        self.chr_bank = (value >> 4) & 0x0F
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        if address < 0x800:
            return (self.chr_bank * 0x800 + address) % max(1, self.ram_base)
        return self.ram_base + address

    def ppu_write(self, address: int, value: int) -> bool:
        if 0x800 <= address < 0x2000:
            self.cart.chr[self.ram_base + address] = value
            return True
        return False

    def mirror_mode(self):
        return "four"


class Mapper158(Mapper64):
    """Tengen 800037 (Alien Syndrome) — RAMBO-1 with CHR-selected nametables."""

    def mirror_mode(self):
        regs = self.regs
        if self.select & 0x20:
            low = (regs[0], regs[8], regs[1], regs[9])
        else:
            low = (regs[0], regs[0], regs[1], regs[1])
        return tuple((bank >> 7) & 1 for bank in low)


class Mapper228(Mapper):
    """Active Enterprises (Action 52, Cheetahmen II) — address-latched banks."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.addr_latch = 0
        self.data_latch = 0
        self.nibble_ram = bytearray(4)

    def reset(self) -> None:
        super().reset()
        self.addr_latch = 0
        self.data_latch = 0

    def register_read(self, address: int) -> Optional[int]:
        if address >= 0x5FF0:
            return self.nibble_ram[address & 3] & 0x0F
        return None

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        a = self.addr_latch
        chip = (a >> 11) & 3
        if chip == 3:
            chip = 2
        bank = chip * 32 + ((a >> 6) & 0x1F)
        if not (a & 0x20):
            bank = (bank & ~1) | ((address >> 14) & 1)
        return (bank % self.cart.prg_16k) * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x5FF0 <= address < 0x6000:
            self.nibble_ram[address & 3] = value & 0x0F
            return True
        if address < 0x8000:
            return False
        self.addr_latch = address & 0x3FFF
        self.data_latch = value
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        bank = ((self.addr_latch & 0x0F) << 2) | (self.data_latch & 3)
        return (bank * 0x2000 + address) % self.cart.chr_len

    def mirror_mode(self):
        return "horizontal" if self.addr_latch & 0x2000 else "vertical"


class Mapper118(Mapper4):
    """TxSROM (Armadillo, Pro Sport Hockey) — CIRAM A10 from CHR bank bit 7."""

    def cpu_write(self, address: int, value: int) -> bool:
        if (address & 0xE001) == 0xA000:
            return True                       # no MMC3 mirroring register
        return super().cpu_write(address, value)

    def mirror_mode(self):
        r = self.regs
        banks = (r[2], r[3], r[4], r[5]) if self.select & 0x80 else (r[0], r[0], r[1], r[1])
        return tuple((bank >> 7) & 1 for bank in banks)


class Mapper28(Mapper):
    """Action 53 (homebrew multicart) — outer/inner PRG, 4x8K CHR-RAM."""

    def __init__(self, cart: "Cartridge") -> None:
        super().__init__(cart)
        self.select = 0
        self.r00 = 0
        self.r01 = 0
        self.r80 = 0
        self.r81 = 0xFF

    def reset(self) -> None:
        super().reset()
        self.r81 = 0xFF

    def _bank16(self, a14: int) -> int:
        mode = (self.r80 >> 2) & 3
        mask = (2 << ((self.r80 >> 4) & 3)) - 1
        outer = self.r81 << 1
        if not mode & 2:
            inner = (self.r01 << 1) | a14
        elif (mode == 2 and a14 == 0) or (mode == 3 and a14 == 1):
            return outer | a14
        else:
            inner = self.r01
        return (outer & ~mask) | (inner & mask)

    def cpu_read(self, address: int) -> Optional[int]:
        if address < 0x8000:
            return None
        bank = self._bank16((address >> 14) & 1) % self.cart.prg_16k
        return bank * 0x4000 + (address & 0x3FFF)

    def cpu_write(self, address: int, value: int) -> bool:
        if 0x5000 <= address < 0x6000:
            self.select = value & 0x81
            return True
        if address < 0x8000:
            return False
        sel = self.select
        if sel == 0x00:
            self.r00 = value
        elif sel == 0x01:
            self.r01 = value
        elif sel == 0x80:
            self.r80 = value
        else:
            self.r81 = value
        if sel in (0x00, 0x01) and not (self.r80 & 2):
            self.r80 = (self.r80 & ~1) | ((value >> 4) & 1)
        return True

    def ppu_read(self, address: int) -> Optional[int]:
        if address >= 0x2000:
            return None
        return ((self.r00 & 3) * 0x2000 + address) % self.cart.chr_len

    def mirror_mode(self):
        return ("single0", "single1", "vertical", "horizontal")[self.r80 & 3]


MAPPERS: dict[int, type[Mapper]] = {
    0: Mapper0, 1: Mapper1, 2: Mapper2, 3: Mapper3, 4: Mapper4, 5: Mapper5,
    7: Mapper7, 9: Mapper9, 10: Mapper10, 11: Mapper11, 13: Mapper13,
    16: Mapper16, 18: Mapper18, 19: Mapper19, 21: Mapper21, 22: Mapper22,
    23: Mapper23, 24: Mapper24, 25: Mapper25, 26: Mapper26, 28: Mapper28, 30: Mapper30,
    32: Mapper32, 33: Mapper33, 34: Mapper34, 47: Mapper47, 48: Mapper48,
    64: Mapper64, 65: Mapper65, 66: Mapper66, 67: Mapper67, 68: Mapper68,
    69: Mapper69, 70: Mapper70, 71: Mapper71, 72: Mapper72, 73: Mapper73,
    75: Mapper75, 76: Mapper76, 77: Mapper77, 78: Mapper78, 79: Mapper79,
    80: Mapper80, 82: Mapper82, 85: Mapper85, 86: Mapper86, 87: Mapper87,
    88: Mapper88, 89: Mapper89, 92: Mapper92, 93: Mapper93, 94: Mapper94,
    95: Mapper95, 97: Mapper97, 113: Mapper113, 118: Mapper118, 119: Mapper119,
    140: Mapper140, 146: Mapper79, 151: Mapper75, 152: Mapper152, 153: Mapper153,
    154: Mapper154, 155: Mapper155, 158: Mapper158, 159: Mapper159, 180: Mapper180,
    184: Mapper184, 185: Mapper185, 206: Mapper206, 207: Mapper207, 210: Mapper210,
    228: Mapper228, 232: Mapper232,
}

# Boards that normally ship with CHR-RAM (used by the self-test's smoke load).
MAPPER_CHR_RAM_HINT = {2, 7, 13, 28, 30, 71, 73, 93, 94, 180, 232}


class Cartridge:
    def __init__(self, image: bytes, source: str = "<memory>") -> None:
        if len(image) < 16 or image[:4] != b"NES\x1a":
            raise CartridgeError("Not a valid iNES or NES 2.0 cartridge image.")
        self.source = source
        self.header = bytes(image[:16])
        flags6, flags7 = image[6], image[7]
        self.mapper_id = (flags6 >> 4) | (flags7 & 0xF0)
        self.nes2 = (flags7 & 0x0C) == 0x08
        if self.nes2:
            self.mapper_id |= (image[8] & 0x0F) << 8
        if flags6 & 0x08:
            self.header_mirroring = "four"
        else:
            self.header_mirroring = "vertical" if flags6 & 1 else "horizontal"
        self.battery = bool(flags6 & 2)
        has_trainer = bool(flags6 & 4)
        offset = 16 + (512 if has_trainer else 0)
        prg_banks = image[4]
        chr_banks = image[5]
        if self.nes2:
            prg_banks |= (image[9] & 0x0F) << 8
            chr_banks |= (image[9] & 0xF0) << 4
        prg_size = prg_banks * 0x4000
        chr_size = chr_banks * 0x2000
        if prg_size == 0 or offset + prg_size + chr_size > len(image):
            raise CartridgeError("The ROM is truncated or has an invalid bank count.")
        self.prg = bytes(image[offset:offset + prg_size])
        offset += prg_size
        self.chr_is_ram = chr_size == 0
        # CPROM (mapper 13) banks 16 KiB of CHR-RAM; everything else uses 8 KiB.
        chr_ram_size = {13: 0x4000, 28: 0x8000, 30: 0x8000}.get(self.mapper_id, 0x2000)
        if self.nes2 and image[11] & 0x0F:
            chr_ram_size = max(chr_ram_size, 64 << (image[11] & 0x0F))
        self.chr = bytearray(chr_ram_size if self.chr_is_ram else image[offset:offset + chr_size])
        # Cached sizes before WRAM sizing (mapper heuristics need PRG length).
        self.prg_len = len(self.prg)
        self.chr_len = len(self.chr)
        # SXROM (large MMC1) needs 32 KiB banked WRAM; Bandai EEPROM rides in a tail.
        prg_ram_size = 0x2000
        if self.mapper_id in (1, 155) and self.prg_len > 0x40000:
            prg_ram_size = 0x8000  # Final Fantasy III (JP), etc.
        if self.mapper_id in (16, 153, 159):
            prg_ram_size = max(prg_ram_size, 0x2100)  # +256B EEPROM image
        if self.mapper_id == 5:
            prg_ram_size = 0x10000  # MMC5 ExRAM-capable WRAM window
        self.prg_ram = bytearray(prg_ram_size)
        if has_trainer:
            # iNES trainer loads into $7000–$71FF of PRG-RAM.
            self.prg_ram[0x1000:0x1200] = image[16:528]
        self.write_cycle = 0
        self.battery_path: Optional[pathlib.Path] = None
        self.prg_8k = max(1, self.prg_len // 0x2000)
        self.prg_16k = max(1, self.prg_len // 0x4000)
        self.prg_32k = max(1, self.prg_len // 0x8000)
        mapper_type = MAPPERS.get(self.mapper_id)
        if mapper_type is None:
            supported = ", ".join(str(number) for number in sorted(MAPPERS))
            raise CartridgeError(
                f"Mapper {self.mapper_id} is not supported in this build. "
                f"Supported mappers: {supported}."
            )
        self.mapper = mapper_type(self)

    @classmethod
    def from_file(cls, path: str | pathlib.Path) -> "Cartridge":
        file_path = pathlib.Path(path)
        cart = cls(file_path.read_bytes(), str(file_path))
        if cart.battery:
            cart.battery_path = file_path.with_suffix(".sav")
            cart.load_battery()
        return cart

    def load_battery(self) -> None:
        path = self.battery_path
        if not path or not path.is_file():
            return
        try:
            data = path.read_bytes()
        except OSError:
            return
        n = min(len(data), len(self.prg_ram))
        self.prg_ram[:n] = data[:n]

    def save_battery(self) -> None:
        path = self.battery_path
        if not self.battery or not path:
            return
        try:
            path.write_bytes(bytes(self.prg_ram))
        except OSError:
            pass

    def cpu_read(self, address: int) -> int:
        if 0x4020 <= address < 0x6000:
            value = self.mapper.register_read(address)
            return value & 0xFF if value is not None else 0
        if 0x6000 <= address < 0x8000:
            direct = self.mapper.cpu_data(address)
            if direct is not None:
                return direct & 0xFF
            mapped = self.mapper.cpu_read(address)
            if mapped is not None:
                return self.prg[mapped % self.prg_len]
            if not self.mapper.prg_ram_enabled():
                return 0
            return self.prg_ram[self.mapper.prg_ram_index(address) % len(self.prg_ram)]
        mapped = self.mapper.cpu_read(address)
        return self.prg[mapped % self.prg_len] if mapped is not None else 0

    def cpu_write(self, address: int, value: int) -> None:
        if 0x4020 <= address < 0x6000:
            self.mapper.cpu_write(address, value)
        elif 0x6000 <= address < 0x8000:
            if not self.mapper.cpu_write(address, value):
                if self.mapper.prg_ram_writable():
                    self.prg_ram[self.mapper.prg_ram_index(address) % len(self.prg_ram)] = value
        else:
            self.mapper.cpu_write(address, value)

    def ppu_read(self, address: int) -> int:
        mapped = self.mapper.ppu_read(address)
        return self.chr[mapped] if mapped is not None else 0

    def ppu_write(self, address: int, value: int) -> None:
        self.mapper.ppu_write(address, value)


LENGTH_TABLE = (
    10, 254, 20, 2, 40, 4, 80, 6, 160, 8, 60, 10, 14, 12, 26, 14,
    12, 16, 24, 18, 48, 20, 96, 22, 192, 24, 72, 26, 16, 28, 32, 30,
)


class Envelope:
    """2A03 divider/decay envelope shared by pulse and noise channels."""

    def __init__(self) -> None:
        self.loop = False
        self.constant = False
        self.period = 0
        self.start = False
        self.divider = 0
        self.decay = 0

    def write(self, value: int) -> None:
        self.loop = bool(value & 0x20)
        self.constant = bool(value & 0x10)
        self.period = value & 0x0F

    def restart(self) -> None:
        self.start = True

    def clock(self) -> None:
        if self.start:
            self.start = False
            self.decay = 15
            self.divider = self.period
        elif self.divider:
            self.divider -= 1
        else:
            self.divider = self.period
            if self.decay:
                self.decay -= 1
            elif self.loop:
                self.decay = 15

    @property
    def output(self) -> int:
        return self.period if self.constant else self.decay


class PulseChannel:
    DUTY_TABLE = (
        (0, 1, 0, 0, 0, 0, 0, 0),
        (0, 1, 1, 0, 0, 0, 0, 0),
        (0, 1, 1, 1, 1, 0, 0, 0),
        (1, 0, 0, 1, 1, 1, 1, 1),
    )

    def __init__(self, channel: int) -> None:
        self.channel = channel
        self.enabled = False
        self.duty = 0
        self.sequence = 0
        self.timer_period = 0
        self.timer = 0
        self.length = 0
        self.envelope = Envelope()
        self.sweep_enabled = False
        self.sweep_period = 0
        self.sweep_negate = False
        self.sweep_shift = 0
        self.sweep_reload = False
        self.sweep_divider = 0

    def write(self, register: int, value: int) -> None:
        if register == 0:
            self.duty = (value >> 6) & 3
            self.envelope.write(value)
        elif register == 1:
            self.sweep_enabled = bool(value & 0x80)
            self.sweep_period = (value >> 4) & 7
            self.sweep_negate = bool(value & 0x08)
            self.sweep_shift = value & 7
            self.sweep_reload = True
        elif register == 2:
            self.timer_period = (self.timer_period & 0x700) | value
        else:
            self.timer_period = (self.timer_period & 0x0FF) | ((value & 7) << 8)
            if self.enabled:
                self.length = LENGTH_TABLE[value >> 3]
            self.sequence = 0
            self.envelope.restart()

    def clock_timer(self) -> None:
        if self.timer:
            self.timer -= 1
        else:
            self.timer = self.timer_period
            self.sequence = (self.sequence + 1) & 7

    def advance_timer(self, ticks: int) -> None:
        if ticks <= 0:
            return
        if ticks <= self.timer:
            self.timer -= ticks
            return
        ticks -= self.timer + 1
        interval = self.timer_period + 1
        events = 1 + ticks // interval
        remainder = ticks % interval
        self.sequence = (self.sequence + events) & 7
        self.timer = self.timer_period - remainder

    def target_period(self) -> int:
        change = self.timer_period >> self.sweep_shift if self.sweep_shift else 0
        if self.sweep_negate:
            return self.timer_period - change - (1 if self.channel == 1 else 0)
        return self.timer_period + change

    def sweep_muted(self) -> bool:
        return self.timer_period < 8 or self.target_period() > 0x7FF

    def clock_sweep(self) -> None:
        if (
            self.sweep_divider == 0
            and self.sweep_enabled
            and self.sweep_shift
            and not self.sweep_muted()
        ):
            self.timer_period = self.target_period() & 0x7FF
        if self.sweep_divider == 0 or self.sweep_reload:
            self.sweep_divider = self.sweep_period
            self.sweep_reload = False
        else:
            self.sweep_divider -= 1

    def clock_length(self) -> None:
        if self.length and not self.envelope.loop:
            self.length -= 1

    @property
    def output(self) -> int:
        if (
            not self.enabled
            or not self.length
            or self.sweep_muted()
            or not self.DUTY_TABLE[self.duty][self.sequence]
        ):
            return 0
        return self.envelope.output


class TriangleChannel:
    SEQUENCE = tuple(range(15, -1, -1)) + tuple(range(16))

    def __init__(self) -> None:
        self.enabled = False
        self.control = False
        self.linear_reload_value = 0
        self.linear_reload = False
        self.linear_counter = 0
        self.timer_period = 0
        self.timer = 0
        self.length = 0
        self.sequence = 0

    def write(self, register: int, value: int) -> None:
        if register == 0:
            self.control = bool(value & 0x80)
            self.linear_reload_value = value & 0x7F
        elif register == 2:
            self.timer_period = (self.timer_period & 0x700) | value
        elif register == 3:
            self.timer_period = (self.timer_period & 0x0FF) | ((value & 7) << 8)
            if self.enabled:
                self.length = LENGTH_TABLE[value >> 3]
            self.linear_reload = True

    def clock_timer(self) -> None:
        if self.timer:
            self.timer -= 1
        else:
            self.timer = self.timer_period
            if self.enabled and self.length and self.linear_counter and self.timer_period > 1:
                self.sequence = (self.sequence + 1) & 31

    def advance_timer(self, ticks: int) -> None:
        if ticks <= 0:
            return
        if ticks <= self.timer:
            self.timer -= ticks
            return
        ticks -= self.timer + 1
        interval = self.timer_period + 1
        events = 1 + ticks // interval
        remainder = ticks % interval
        if self.enabled and self.length and self.linear_counter and self.timer_period > 1:
            self.sequence = (self.sequence + events) & 31
        self.timer = self.timer_period - remainder

    def clock_linear(self) -> None:
        if self.linear_reload:
            self.linear_counter = self.linear_reload_value
        elif self.linear_counter:
            self.linear_counter -= 1
        if not self.control:
            self.linear_reload = False

    def clock_length(self) -> None:
        if self.length and not self.control:
            self.length -= 1

    @property
    def output(self) -> int:
        # The triangle DAC holds its last level when either counter halts.
        return self.SEQUENCE[self.sequence]


class NoiseChannel:
    PERIOD_TABLE = (
        4, 8, 16, 32, 64, 96, 128, 160,
        202, 254, 380, 508, 762, 1016, 2034, 4068,
    )

    def __init__(self) -> None:
        self.enabled = False
        self.mode = False
        self.period = self.PERIOD_TABLE[0]
        self.timer = 0
        self.length = 0
        self.shift = 1
        self.envelope = Envelope()

    def write(self, register: int, value: int) -> None:
        if register == 0:
            self.envelope.write(value)
        elif register == 2:
            self.mode = bool(value & 0x80)
            self.period = self.PERIOD_TABLE[value & 0x0F]
        elif register == 3:
            if self.enabled:
                self.length = LENGTH_TABLE[value >> 3]
            self.envelope.restart()

    def clock_timer(self) -> None:
        if self.timer:
            self.timer -= 1
        else:
            self.timer = self.period - 1
            tap = 6 if self.mode else 1
            feedback = (self.shift & 1) ^ ((self.shift >> tap) & 1)
            self.shift = (self.shift >> 1) | (feedback << 14)

    def advance_timer(self, ticks: int) -> None:
        while ticks > self.timer:
            ticks -= self.timer + 1
            self.timer = self.period - 1
            tap = 6 if self.mode else 1
            feedback = (self.shift & 1) ^ ((self.shift >> tap) & 1)
            self.shift = (self.shift >> 1) | (feedback << 14)
        self.timer -= ticks

    def clock_length(self) -> None:
        if self.length and not self.envelope.loop:
            self.length -= 1

    @property
    def output(self) -> int:
        if not self.enabled or not self.length or self.shift & 1:
            return 0
        return self.envelope.output


class DMCChannel:
    RATE_TABLE = (
        428, 380, 340, 320, 286, 254, 226, 214,
        190, 160, 142, 128, 106, 84, 72, 54,
    )

    def __init__(self, bus: "Bus") -> None:
        self.bus = bus
        self.enabled = False
        self.irq_enabled = False
        self.loop = False
        self.irq = False
        self.period = self.RATE_TABLE[0]
        self.timer = 0
        self.output = 0
        self.sample_address = 0xC000
        self.sample_length = 1
        self.current_address = 0xC000
        self.bytes_remaining = 0
        self.sample_buffer: Optional[int] = None
        self.shift = 0
        self.bits_remaining = 8
        self.silence = True

    def write(self, address: int, value: int) -> None:
        if address == 0x4010:
            self.irq_enabled = bool(value & 0x80)
            self.loop = bool(value & 0x40)
            self.period = self.RATE_TABLE[value & 0x0F]
            if not self.irq_enabled:
                self.irq = False
        elif address == 0x4011:
            self.output = value & 0x7F
        elif address == 0x4012:
            self.sample_address = 0xC000 | (value << 6)
        elif address == 0x4013:
            self.sample_length = (value << 4) | 1

    def set_enabled(self, enabled: bool) -> None:
        self.enabled = enabled
        self.irq = False
        if not enabled:
            self.bytes_remaining = 0
        elif self.bytes_remaining == 0:
            self.restart()

    def restart(self) -> None:
        self.current_address = self.sample_address
        self.bytes_remaining = self.sample_length

    def _fill_buffer(self) -> None:
        if self.sample_buffer is not None or not self.bytes_remaining:
            return
        self.sample_buffer = self.bus.peek(self.current_address)
        if hasattr(self.bus, "cpu"):
            self.bus.cpu.stall += 4
        self.current_address = 0x8000 if self.current_address == 0xFFFF else self.current_address + 1
        self.bytes_remaining -= 1
        if self.bytes_remaining == 0:
            if self.loop:
                self.restart()
            elif self.irq_enabled:
                self.irq = True

    def clock_timer(self) -> None:
        self._fill_buffer()
        if self.timer:
            self.timer -= 1
            return
        self.timer = self.period - 1
        if not self.silence:
            if self.shift & 1:
                if self.output <= 125:
                    self.output += 2
            elif self.output >= 2:
                self.output -= 2
        self.shift >>= 1
        self.bits_remaining -= 1
        if self.bits_remaining == 0:
            self.bits_remaining = 8
            if self.sample_buffer is None:
                self.silence = True
            else:
                self.silence = False
                self.shift = self.sample_buffer
                self.sample_buffer = None
        self._fill_buffer()

    def advance_timer(self, ticks: int) -> None:
        self._fill_buffer()
        while ticks > self.timer:
            ticks -= self.timer + 1
            self.timer = self.period - 1
            if not self.silence:
                if self.shift & 1:
                    if self.output <= 125:
                        self.output += 2
                elif self.output >= 2:
                    self.output -= 2
            self.shift >>= 1
            self.bits_remaining -= 1
            if self.bits_remaining == 0:
                self.bits_remaining = 8
                if self.sample_buffer is None:
                    self.silence = True
                else:
                    self.silence = False
                    self.shift = self.sample_buffer
                    self.sample_buffer = None
            self._fill_buffer()
        self.timer -= ticks
        self._fill_buffer()



# 15-bit noise LFSR (mode 0, taps 0/1) is maximal length: every non-zero state
# lies on one 32767-step cycle, so advancing N steps is a table lookup.
_LFSR_SEQ = array("H", bytes(2 * 32767))
_LFSR_POS = array("H", bytes(2 * 32768))


def _build_lfsr() -> None:
    state = 1
    for index in range(32767):
        _LFSR_SEQ[index] = state
        _LFSR_POS[state] = index
        state = (state >> 1) | (((state ^ (state >> 1)) & 1) << 14)


_build_lfsr()


def _noise_advance_timer(self, ticks: int) -> None:
    timer = self.timer
    if ticks <= timer:
        self.timer = timer - ticks
        return
    ticks -= timer + 1
    period = self.period
    steps = 1 + ticks // period
    self.timer = period - 1 - ticks % period
    shift = self.shift
    if not self.mode:
        if shift:
            self.shift = _LFSR_SEQ[(_LFSR_POS[shift] + steps) % 32767]
        return
    for _ in range(steps if steps < 93 else 93 + steps % 93):
        shift = (shift >> 1) | ((((shift >> 6) ^ shift) & 1) << 14)
    self.shift = shift


NoiseChannel.advance_timer = _noise_advance_timer  # type: ignore[method-assign]


class APU:
    """NTSC/PAL 2A03 APU — all five channels, run in batches ("catch-up").

    The scheduler advances the APU once per scanline (and whenever the CPU
    touches $4000-$4017), so the per-instruction cost of the old design is
    gone.  Inside a batch the loop jumps straight from one event (sample
    point, frame-sequencer step) to the next using closed-form timer
    advances, and mixes with the standard non-linear 2A03 lookup tables.
    """

    SAMPLE_RATE = 44_100
    _PULSE_TABLE = tuple(95.52 / (8128.0 / n + 100.0) if n else 0.0 for n in range(31))
    _TND_TABLE = tuple(163.67 / (24329.0 / n + 100.0) if n else 0.0 for n in range(203))
    _DUTY = PulseChannel.DUTY_TABLE
    _TRI_SEQ = TriangleChannel.SEQUENCE

    def __init__(self, bus: "Bus", sample_rate: Optional[int] = None) -> None:
        self.bus = bus
        if sample_rate:
            self.SAMPLE_RATE = sample_rate
        self.clock = getattr(bus, "cpu_clock", CPU_CLOCK)
        self.pulse1 = PulseChannel(1)
        self.pulse2 = PulseChannel(2)
        self.triangle = TriangleChannel()
        self.noise = NoiseChannel()
        self.dmc = DMCChannel(bus)
        self.frame_cycle = 0
        self.cpu_cycle = 0          # APU-local cycle counter (pulse parity)
        self.position = 0           # absolute CPU cycle the APU has reached
        self.five_step = False
        self.irq_inhibit = False
        self.frame_irq = False
        self.frame_reset_delay = 0
        self.sample_phase = 0
        self.samples = array("h")
        self.previous_mixed = 0.0
        self.high_pass = 0.0
        self.low_pass = 0.0
        self.volumes = getattr(self, "volumes", [255, 255, 255, 255, 255, 255])
        self._rebuild_volume_tables()

    # ---------------------------------------------------------------- config
    def _rebuild_volume_tables(self) -> None:
        master, sq1, sq2, tri, noi, pcm = self.volumes
        self._v_sq1 = tuple(round(n * sq1 / 255) for n in range(16))
        self._v_sq2 = tuple(round(n * sq2 / 255) for n in range(16))
        self._v_tri = tuple(round(n * tri / 255) for n in range(16))
        self._v_noi = tuple(round(n * noi / 255) for n in range(16))
        self._v_pcm = tuple(round(n * pcm / 255) for n in range(128))
        self._gain = 47_000 * master / 255

    def set_volumes(self, master: int, square1: int, square2: int, triangle: int,
                    noise: int, pcm: int) -> None:
        self.volumes = [master, square1, square2, triangle, noise, pcm]
        self._rebuild_volume_tables()

    @property
    def irq_pending(self) -> bool:
        return self.frame_irq or self.dmc.irq

    def reset(self) -> None:
        volumes = self.volumes
        rate = self.SAMPLE_RATE
        position = self.position
        self.__init__(self.bus, rate)
        self.volumes = volumes
        self._rebuild_volume_tables()
        self.position = position

    # ------------------------------------------------------------- registers
    def write(self, address: int, value: int) -> None:
        value &= 0xFF
        if 0x4000 <= address <= 0x4003:
            self.pulse1.write(address & 3, value)
        elif 0x4004 <= address <= 0x4007:
            self.pulse2.write(address & 3, value)
        elif address in (0x4008, 0x400A, 0x400B):
            self.triangle.write(address & 3, value)
        elif address in (0x400C, 0x400E, 0x400F):
            self.noise.write(address & 3, value)
        elif 0x4010 <= address <= 0x4013:
            self.dmc.write(address, value)
        elif address == 0x4015:
            self.pulse1.enabled = bool(value & 0x01)
            self.pulse2.enabled = bool(value & 0x02)
            self.triangle.enabled = bool(value & 0x04)
            self.noise.enabled = bool(value & 0x08)
            if not self.pulse1.enabled:
                self.pulse1.length = 0
            if not self.pulse2.enabled:
                self.pulse2.length = 0
            if not self.triangle.enabled:
                self.triangle.length = 0
            if not self.noise.enabled:
                self.noise.length = 0
            self.dmc.set_enabled(bool(value & 0x10))
        elif address == 0x4017:
            self.five_step = bool(value & 0x80)
            self.irq_inhibit = bool(value & 0x40)
            if self.irq_inhibit:
                self.frame_irq = False
            self.frame_reset_delay = 3 if self.cpu_cycle & 1 else 4

    def read_status(self) -> int:
        value = (
            (1 if self.pulse1.length else 0)
            | (2 if self.pulse2.length else 0)
            | (4 if self.triangle.length else 0)
            | (8 if self.noise.length else 0)
            | (0x10 if self.dmc.bytes_remaining else 0)
            | (0x40 if self.frame_irq else 0)
            | (0x80 if self.dmc.irq else 0)
        )
        self.frame_irq = False
        return value

    # -------------------------------------------------------- frame counter
    def _quarter_frame(self) -> None:
        self.pulse1.envelope.clock()
        self.pulse2.envelope.clock()
        self.noise.envelope.clock()
        self.triangle.clock_linear()

    def _half_frame(self) -> None:
        self.pulse1.clock_length()
        self.pulse2.clock_length()
        self.triangle.clock_length()
        self.noise.clock_length()
        self.pulse1.clock_sweep()
        self.pulse2.clock_sweep()

    # Frame-sequencer events in CPU cycles after a reset.  4-step: quarter at
    # 7457/22371, quarter+half at 14913/29829, IRQ flag raised on 29828-29830,
    # sequence restarts at 29830.  5-step: quarter+half at 14913/37281, no IRQ.
    _SEQ_NTSC = ((7457, 14913, 22371, 29828, 29829, 29830), (7457, 14913, 22371, 37281, 37282))
    _SEQ_PAL = ((8313, 16627, 24939, 33252, 33253, 33254), (8313, 16627, 24939, 41565, 41566))

    def _sequence(self):
        return self._SEQ_PAL if self.clock == 1_662_607 else self._SEQ_NTSC

    def _next_frame_event(self) -> int:
        four, five = self._sequence()
        events = five if self.five_step else four
        fc = self.frame_cycle
        for event in events:
            if event > fc:
                return event
        return events[-1]

    def _handle_frame_event(self) -> None:
        four, five = self._sequence()
        fc = self.frame_cycle
        if self.five_step:
            if fc == five[0] or fc == five[2]:
                self._quarter_frame()
            elif fc == five[1] or fc == five[3]:
                self._quarter_frame()
                self._half_frame()
            elif fc >= five[4]:
                self.frame_cycle = fc - five[4]
            return
        if fc == four[0] or fc == four[2]:
            self._quarter_frame()
        elif fc == four[1]:
            self._quarter_frame()
            self._half_frame()
        elif fc == four[3]:
            if not self.irq_inhibit:
                self.frame_irq = True
        elif fc == four[4]:
            self._quarter_frame()
            self._half_frame()
            if not self.irq_inhibit:
                self.frame_irq = True
        elif fc >= four[5]:
            if not self.irq_inhibit:
                self.frame_irq = True
            self.frame_cycle = fc - four[5]

    # ---------------------------------------------------------- catch-up run
    def catch_up(self, cpu_cycle: int) -> None:
        delta = cpu_cycle - self.position
        if delta > 0:
            self.position = cpu_cycle
            self.step(delta)

    def step(self, cpu_cycles: int) -> None:
        """Advance the APU by `cpu_cycles`, emitting samples as they fall due."""
        p1 = self.pulse1
        p2 = self.pulse2
        tri = self.triangle
        noi = self.noise
        dmc = self.dmc
        duty = self._DUTY
        tri_seq = self._TRI_SEQ
        ptab = self._PULSE_TABLE
        ttab = self._TND_TABLE
        v1 = self._v_sq1
        v2 = self._v_sq2
        vt = self._v_tri
        vn = self._v_noi
        vd = self._v_pcm
        gain = self._gain
        clock = self.clock
        rate = self.SAMPLE_RATE
        out = self.samples
        phase = self.sample_phase
        remaining = cpu_cycles
        fevent = self._next_frame_event()
        while remaining > 0:
            to_sample = (clock - phase + rate - 1) // rate
            if to_sample <= 0:
                to_sample = 1
            to_frame = fevent - self.frame_cycle
            if self.frame_reset_delay and self.frame_reset_delay < to_frame:
                to_frame = self.frame_reset_delay
            step = remaining
            if to_sample < step:
                step = to_sample
            if to_frame < step:
                step = to_frame
            if step <= 0:
                step = 1
            # ---- pulse timers tick every other CPU cycle
            old = self.cpu_cycle
            self.cpu_cycle = old + step
            ticks = ((old & 1) + step) >> 1
            if ticks:
                if p1.enabled:
                    tm = p1.timer
                    if ticks <= tm:
                        p1.timer = tm - ticks
                    else:
                        k = ticks - tm - 1
                        per = p1.timer_period + 1
                        p1.sequence = (p1.sequence + 1 + k // per) & 7
                        p1.timer = p1.timer_period - k % per
                if p2.enabled:
                    tm = p2.timer
                    if ticks <= tm:
                        p2.timer = tm - ticks
                    else:
                        k = ticks - tm - 1
                        per = p2.timer_period + 1
                        p2.sequence = (p2.sequence + 1 + k // per) & 7
                        p2.timer = p2.timer_period - k % per
            # ---- triangle (CPU rate)
            if tri.enabled:
                tm = tri.timer
                if step <= tm:
                    tri.timer = tm - step
                else:
                    k = step - tm - 1
                    per = tri.timer_period + 1
                    if tri.length and tri.linear_counter and tri.timer_period > 1:
                        tri.sequence = (tri.sequence + 1 + k // per) & 31
                    tri.timer = tri.timer_period - k % per
            # ---- noise
            if noi.enabled:
                if step <= noi.timer:
                    noi.timer -= step
                else:
                    noi.advance_timer(step)
            # ---- DMC
            if dmc.bytes_remaining or dmc.sample_buffer is not None or not dmc.silence:
                dmc.advance_timer(step)
            self.frame_cycle += step
            phase += step * rate
            remaining -= step
            if self.frame_reset_delay:
                self.frame_reset_delay -= step
                if self.frame_reset_delay <= 0:
                    self.frame_reset_delay = 0
                    self.frame_cycle = 0
                    if self.five_step:
                        self._quarter_frame()
                        self._half_frame()
                    fevent = self._next_frame_event()
            if self.frame_cycle >= fevent:
                self._handle_frame_event()
                fevent = self._next_frame_event()
            if phase >= clock:
                phase -= clock
                # ---- mix one output sample
                o1 = 0
                if p1.enabled and p1.length and duty[p1.duty][p1.sequence]:
                    tp = p1.timer_period
                    if tp >= 8 and (p1.sweep_negate or tp + (tp >> p1.sweep_shift if p1.sweep_shift else 0) <= 0x7FF):
                        env = p1.envelope
                        o1 = v1[env.period if env.constant else env.decay]
                o2 = 0
                if p2.enabled and p2.length and duty[p2.duty][p2.sequence]:
                    tp = p2.timer_period
                    if tp >= 8 and (p2.sweep_negate or tp + (tp >> p2.sweep_shift if p2.sweep_shift else 0) <= 0x7FF):
                        env = p2.envelope
                        o2 = v2[env.period if env.constant else env.decay]
                ot = vt[tri_seq[tri.sequence]]
                on = 0
                if noi.enabled and noi.length and not (noi.shift & 1):
                    env = noi.envelope
                    on = vn[env.period if env.constant else env.decay]
                mixed = ptab[o1 + o2] + ttab[3 * ot + 2 * on + vd[dmc.output & 0x7F]]
                hp = mixed - self.previous_mixed + 0.996 * self.high_pass
                self.previous_mixed = mixed
                self.high_pass = hp
                lp = self.low_pass + 0.45 * (hp - self.low_pass)
                self.low_pass = lp
                sample = int(lp * gain)
                if sample > 32767:
                    sample = 32767
                elif sample < -32768:
                    sample = -32768
                out.append(sample)
        self.sample_phase = phase

    def drain_samples(self) -> bytes:
        if not self.samples:
            return b""
        samples = self.samples
        self.samples = array("h")
        if sys.byteorder != "little":
            samples.byteswap()
        return samples.tobytes()

    # ------------------------------------------------------------ save state
    def state(self) -> dict:
        def chan(obj):
            d = {}
            for k, val in obj.__dict__.items():
                if k == "bus":
                    continue
                if k == "envelope":
                    d[k] = dict(val.__dict__)
                else:
                    d[k] = val
            return d
        st = {k: getattr(self, k) for k in (
            "frame_cycle", "cpu_cycle", "position", "five_step", "irq_inhibit",
            "frame_irq", "frame_reset_delay", "sample_phase")}
        for name in ("pulse1", "pulse2", "triangle", "noise", "dmc"):
            st[name] = chan(getattr(self, name))
        return st

    def load_state(self, st: dict) -> None:
        for k, val in st.items():
            if k in ("pulse1", "pulse2", "triangle", "noise", "dmc"):
                obj = getattr(self, k)
                for ck, cv in val.items():
                    if ck == "envelope":
                        obj.envelope.__dict__.update(cv)
                    else:
                        setattr(obj, ck, cv)
            else:
                setattr(self, k, val)
        self.samples = array("h")


# ---------------------------------------------------------------------------
# PPU — Ricoh 2C02, scanline renderer driven by loopy v/t registers
# ---------------------------------------------------------------------------
# Each visible line is drawn at dot 0 from the current loopy `v` (exactly the
# value hardware latched by the dot-257 / 321-336 fetches of the previous
# line), then the scheduler applies the dot-256 Y increment and dot-257
# horizontal copy at the right CPU cycle.  Tile rows are decoded once into
# 8-byte palette-index strings and cached, so a whole background line is a
# single bytes.join of 33 cached rows.  Sprite-0 hit is resolved to the exact
# dot it happens on and becomes visible to $2002 reads at that CPU cycle.

# ATTR_TT[p] maps a 2-bit pixel (0-3) to a palette RAM index for palette p
# (0-3 = background, 4-7 = sprites); pixel 0 stays 0 = transparent.
ATTR_TT = tuple(
    bytes([0, p * 4 + 1, p * 4 + 2, p * 4 + 3]) + bytes(252) for p in range(8)
)
# Raw 2-bit pixel rows, index = (high << 8) | low, leftmost pixel first.
_ROW_PIXELS = PIXEL_ROW_LUT
_ROW_PIXELS_FLIP = tuple(row[::-1] for row in PIXEL_ROW_LUT)


def _palette_mirror(index: int) -> int:
    index &= 0x1F
    if index & 0x13 == 0x10:
        index &= 0x0F
    return index


class PPU:
    def __init__(self, cart: "Cartridge") -> None:
        self.cart = cart
        self.bus: Optional["Bus"] = None
        self.vram = bytearray(0x1000)          # 2 KiB CIRAM (+2 KiB four-screen)
        self.palette = bytearray(32)
        self.oam = bytearray(256)
        self.framebuffer_idx = bytearray(SCREEN_W * SCREEN_H)   # NES colour 0-63
        # decoded tile-row caches: key = (hi << 11) | (lo << 3) | palette(0-7)
        self._row_cache: list = [None] * (1 << 19)
        self._row_cache_flip: list = [None] * (1 << 19)
        self._world_cache: dict = {}
        self.chr_gen = 0            # bumped on CHR-RAM writes (invalidates row cache)
        self.reset(power=True)

    # ------------------------------------------------------------------ state
    def reset(self, power: bool = False) -> None:
        self.ctrl = 0
        self.mask = 0
        self.write_latch = 0
        self.fine_x = 0
        self.temp_address = 0
        self.read_buffer = 0
        self._open_bus = 0
        if power:
            self.status = 0xA0
            self.oam_address = 0
            self.address = 0
            self.vram[:] = bytes(len(self.vram))
            self.palette[:] = bytes(
                (0x09, 0x01, 0x00, 0x01, 0x00, 0x02, 0x02, 0x0D, 0x08, 0x10, 0x08, 0x24,
                 0x00, 0x00, 0x04, 0x2C, 0x09, 0x01, 0x34, 0x03, 0x00, 0x04, 0x00, 0x14,
                 0x08, 0x3A, 0x00, 0x02, 0x00, 0x20, 0x2C, 0x08))
            self.oam[:] = bytes(256)
            self.frame_number = 0
        self.scanline = 0
        self.dot = 0
        self.odd_frame = False
        self.frame_ready = False
        self.s0_cycle = -1          # CPU cycle at which a pending sprite-0 hit lands
        self.vbl_cycle = -1         # CPU cycle at which this frame's VBL flag is due
        self.vbl_suppress = False
        self.vbl_clear_cycle = -1   # CPU cycle at which VBL/S0/overflow clear (pre-render dot 1)
        self._a12 = 0
        self.line_cycle = 0         # CPU cycle of the current line's dot 0
        self.pal_dirty = True
        self.spr_dirty = True
        self._pal_tt = bytes(256)
        self._spr_lines: list = [()] * 240
        self._spr_overflow = bytearray(240)
        self.emphasis = 0
        self._last_grey = 0

    @property
    def scroll_x(self) -> int:
        return ((self.temp_address & 0x1F) << 3) | self.fine_x | ((self.temp_address >> 2) & 0x100)

    @property
    def scroll_y(self) -> int:
        t = self.temp_address
        return ((t >> 5) & 0x1F) * 8 + ((t >> 12) & 7) + (240 if t & 0x800 else 0)

    @property
    def rendering(self) -> bool:
        return bool(self.mask & 0x18)

    # ------------------------------------------------------- memory helpers
    def memory_read(self, address: int) -> int:
        address &= 0x3FFF
        if address < 0x2000:
            return self.cart.ppu_read(address)
        if address < 0x3F00:
            bus = self.bus
            return self.vram[bus.nt_map[(address >> 10) & 3] + (address & 0x3FF)]
        return self.palette[_palette_mirror(address)] & 0x3F

    def memory_write(self, address: int, value: int) -> None:
        address &= 0x3FFF
        if address < 0x2000:
            self.cart.ppu_write(address, value)
            self.chr_gen += 1
        elif address < 0x3F00:
            bus = self.bus
            self.vram[bus.nt_map[(address >> 10) & 3] + (address & 0x3FF)] = value
        else:
            self.palette[_palette_mirror(address)] = value & 0x3F
            self.pal_dirty = True

    # ------------------------------------------------------------ registers
    def read_register(self, address: int, cyc: int = -1) -> int:
        reg = address & 7
        if reg == 2:
            if self.s0_cycle >= 0 and cyc >= self.s0_cycle:
                self.status |= 0x40
                self.s0_cycle = -1
            if self.vbl_clear_cycle >= 0 and cyc >= self.vbl_clear_cycle:
                self.status &= 0x1F
                self.vbl_clear_cycle = -1
            vc = self.vbl_cycle
            if vc >= 0:
                if cyc >= vc:
                    # flag lands during this instruction; reading it on the
                    # exact set cycle also cancels the NMI (race condition)
                    self.status |= 0x80
                    self.vbl_cycle = -1
                    if cyc == vc:
                        self.vbl_suppress = True
                elif cyc == vc - 1:
                    self.vbl_cycle = -1          # read one dot early: flag never sets
                    self.vbl_suppress = True
            value = (self.status & 0xE0) | (self._open_bus & 0x1F)
            self.status &= 0x7F
            self.write_latch = 0
            self._open_bus = value
            return value
        if reg == 4:
            value = self.oam[self.oam_address]
            if (self.oam_address & 3) == 2:
                value &= 0xE3
            self._open_bus = value
            return value
        if reg == 7:
            addr = self.address & 0x3FFF
            if addr >= 0x3F00:
                value = (self.palette[_palette_mirror(addr)] & 0x3F) | (self._open_bus & 0xC0)
                self.read_buffer = self.memory_read(addr - 0x1000)
            else:
                value = self.read_buffer
                self.read_buffer = self.memory_read(addr)
            self.address = (self.address + (32 if self.ctrl & 4 else 1)) & 0x7FFF
            self._open_bus = value
            self._a12_edge()
            return value
        return self._open_bus

    def write_register(self, address: int, value: int, cyc: int = -1) -> None:
        reg = address & 7
        value &= 0xFF
        self._open_bus = value
        if reg == 0:
            old = self.ctrl
            self.ctrl = value
            self.temp_address = (self.temp_address & 0x73FF) | ((value & 3) << 10)
            if (old ^ value) & 0x38:
                self.spr_dirty = True
            if not (old & 0x80) and value & 0x80 and self.status & 0x80 and self.bus:
                self.bus.nmi_line = True
                self.bus.wchk = 2          # NMI fires after the *next* instruction
        elif reg == 1:
            self.mask = value
            self.emphasis = value >> 5
            if (value ^ getattr(self, "_last_grey", 0)) & 1:
                self.pal_dirty = True
            self._last_grey = value & 1
        elif reg == 3:
            self.oam_address = value
        elif reg == 4:
            self.oam[self.oam_address] = value
            self.oam_address = (self.oam_address + 1) & 0xFF
            self.spr_dirty = True
        elif reg == 5:
            if self.write_latch == 0:
                self.fine_x = value & 7
                self.temp_address = (self.temp_address & 0x7FE0) | (value >> 3)
                self.write_latch = 1
            else:
                self.temp_address = ((self.temp_address & 0x0C1F)
                                     | ((value & 7) << 12) | ((value & 0xF8) << 2))
                self.write_latch = 0
        elif reg == 6:
            if self.write_latch == 0:
                self.temp_address = (self.temp_address & 0x00FF) | ((value & 0x3F) << 8)
                self.write_latch = 1
            else:
                self.temp_address = (self.temp_address & 0x7F00) | value
                self.address = self.temp_address
                self.write_latch = 0
                self._a12_edge()
        elif reg == 7:
            self.memory_write(self.address, value)
            self.address = (self.address + (32 if self.ctrl & 4 else 1)) & 0x7FFF
            self._a12_edge()

    def _a12_edge(self) -> None:
        """MMC3-family boards count rising edges of PPU A12; with rendering
        off, games (and test ROMs) can toggle it through PPUADDR/PPUDATA."""
        a12 = (self.address >> 12) & 1
        if a12 != self._a12:
            self._a12 = a12
            if a12 and not (self.mask & 0x18):
                mapper = self.cart.mapper
                if getattr(mapper, "a12_clocked", False):
                    mapper.clock_scanline()

    # --------------------------------------------------- loopy v increments
    def increment_y(self) -> None:
        v = self.address
        if (v & 0x7000) != 0x7000:
            v += 0x1000
        else:
            v &= ~0x7000
            y = (v & 0x03E0) >> 5
            if y == 29:
                y = 0
                v ^= 0x0800
            elif y == 31:
                y = 0
            else:
                y += 1
            v = (v & ~0x03E0) | (y << 5)
        self.address = v

    def copy_x(self) -> None:
        self.address = (self.address & ~0x041F) | (self.temp_address & 0x041F)

    def copy_y(self) -> None:
        self.address = (self.address & ~0x7BE0) | (self.temp_address & 0x7BE0)

    # ------------------------------------------------------------- caching
    def _rebuild_palette(self) -> None:
        grey = 0x30 if self.mask & 1 else 0x3F
        pal = self.palette
        table = bytearray(256)
        for index in range(32):
            table[index] = pal[_palette_mirror(index)] & grey
        self._pal_tt = bytes(table)
        self.pal_dirty = False

    def _rebuild_sprites(self) -> None:
        oam = self.oam
        height = 16 if self.ctrl & 0x20 else 8
        lines: list = [[] for _ in range(240)]
        overflow = bytearray(240)
        for n in range(64):
            top = oam[n << 2] + 1
            if top >= 240:
                continue
            end = top + height
            if end > 240:
                end = 240
            for line in range(top, end):
                bucket = lines[line]
                if len(bucket) < 8:
                    bucket.append(n)
                else:
                    overflow[line] = 1
        self._spr_lines = lines
        self._spr_overflow = overflow
        self.spr_dirty = False

    @staticmethod
    def _build_world_row(vram, la, ra, lat, rat, ay, pt, cart_chr, chr_off, cache, decode) -> bytes:
        rows = []
        push = rows.append
        for row_base, attr in ((la, lat), (ra, rat)):
            for cx in range(32):
                tile = vram[row_base + cx]
                pal = (vram[attr + (cx >> 2)] >> (ay | (cx & 2))) & 3
                pa = pt | (tile << 4)
                o = chr_off[pa >> 10] + (pa & 0x3FF)
                key = (cart_chr[o + 8] << 11) | (cart_chr[o] << 3) | pal
                row = cache[key]
                push(row if row is not None else decode(key, False))
        world = b"".join(rows)
        return world + world[:256]

    def _decode_row(self, key: int, flip: bool) -> bytes:
        pal = key & 7
        lo = (key >> 3) & 0xFF
        hi = key >> 11
        src = _ROW_PIXELS_FLIP if flip else _ROW_PIXELS
        row = src[(hi << 8) | lo].translate(ATTR_TT[pal])
        (self._row_cache_flip if flip else self._row_cache)[key] = row
        return row

    # ----------------------------------------------------------- rendering
    dot_num = 1          # CPU cycles per PPU dot = dot_num / dot_den (NTSC 1/3)
    dot_den = 3
    S0_DELAY = 3         # dots between a sprite-0 pixel and the $2002 flag

    def render_line(self, y: int, line_dot: int) -> None:
        """Draw visible scanline `y` (called at dot 0 with rendering enabled)."""
        bus = self.bus
        if bus.banks_dirty:
            bus.refresh_ppu_banks()
        if self.pal_dirty:
            self._rebuild_palette()
        mask = self.mask
        cart_chr = self.cart.chr
        chr_off = bus.chr_off
        slow_chr = bus.chr_slow
        cache = self._row_cache
        decode = self._decode_row
        if mask & 0x08:
            v = self.address
            vram = self.vram
            nt_map = bus.nt_map
            nt = (v >> 10) & 3
            coarse_y = (v >> 5) & 31
            cx = v & 31
            pt = (0x1000 if self.ctrl & 0x10 else 0) | ((v >> 12) & 7)
            row_base = coarse_y << 5
            attr_base = 0x3C0 + ((coarse_y >> 2) << 3)
            ay = (coarse_y & 2) << 1
            base = nt_map[nt]
            other = nt_map[nt ^ 1]
            rows = []
            push = rows.append
            if slow_chr:
                ppu_fetch = self.cart.ppu_read
                for _ in range(33):
                    if cx == 32:
                        cx = 0
                        base, other = other, base
                    tile = vram[base + row_base + cx]
                    pal = (vram[base + attr_base + (cx >> 2)] >> (ay | (cx & 2))) & 3
                    pa = pt | (tile << 4)
                    lo = ppu_fetch(pa)          # low plane first: MMC2/MMC4 latch on the high plane
                    key = (ppu_fetch(pa + 8) << 11) | (lo << 3) | pal
                    row = cache[key]
                    push(row if row is not None else decode(key, False))
                    cx += 1
                fx = self.fine_x
                line = bytearray(b"".join(rows)[fx:fx + 256])
            else:
                # Whole 512-pixel "world row" (both horizontal nametables) is
                # cached by content: the 64 tile bytes + 16 attribute bytes,
                # pattern base / fine Y, CHR bank layout and CHR-RAM version.
                left = nt_map[nt & 2]
                right = nt_map[(nt & 2) | 1]
                la = left + row_base
                ra = right + row_base
                lat = left + attr_base
                rat = right + attr_base
                key = (bytes(vram[la:la + 32] + vram[ra:ra + 32]
                             + vram[lat:lat + 8] + vram[rat:rat + 8]),
                       pt, bus.chr_key, self.chr_gen)
                world = self._world_cache.get(key)
                if world is None:
                    world = self._build_world_row(vram, la, ra, lat, rat, ay, pt,
                                                  cart_chr, chr_off, cache, decode)
                    wc = self._world_cache
                    if len(wc) > 6000:
                        wc.clear()
                    wc[key] = world
                start = ((nt & 1) << 8) | (cx << 3) | self.fine_x
                line = bytearray(world[start:start + 256])
            if not (mask & 0x02):
                line[0:8] = b"\0\0\0\0\0\0\0\0"
        else:
            line = bytearray(256)

        if self.spr_dirty:
            self._rebuild_sprites()
        if self._spr_overflow[y]:
            self.status |= 0x20       # evaluation runs whenever rendering is on
        if mask & 0x10:
            sprites = self._spr_lines[y]
            if sprites:
                oam = self.oam
                ctrl = self.ctrl
                tall = ctrl & 0x20
                spt = 0x1000 if ctrl & 0x08 else 0
                clip = not (mask & 0x04)
                owner = bytearray(256)
                fcache = self._row_cache_flip
                for n in sprites:
                    o4 = n << 2
                    row_y = y - oam[o4] - 1
                    tile = oam[o4 + 1]
                    attr = oam[o4 + 2]
                    sx = oam[o4 + 3]
                    if tall:
                        if attr & 0x80:
                            row_y = 15 - row_y
                        pa = ((tile & 1) << 12) | ((tile & 0xFE) << 4) | ((row_y & 8) << 1) | (row_y & 7)
                    else:
                        if attr & 0x80:
                            row_y = 7 - row_y
                        pa = spt | (tile << 4) | row_y
                    if slow_chr:
                        lo = self.cart.ppu_read(pa)
                        hi = self.cart.ppu_read(pa + 8)
                    else:
                        o = chr_off[pa >> 10] + (pa & 0x3FF)
                        lo = cart_chr[o]
                        hi = cart_chr[o + 8]
                    if not (lo | hi):
                        continue
                    key = (hi << 11) | (lo << 3) | (4 | (attr & 3))
                    if attr & 0x40:
                        row = fcache[key]
                        if row is None:
                            row = decode(key, True)
                    else:
                        row = cache[key]
                        if row is None:
                            row = decode(key, False)
                    behind = attr & 0x20
                    hit_check = n == 0 and self.s0_cycle < 0 and not (self.status & 0x40) and mask & 0x08
                    for k in range(8):
                        px = row[k]
                        if not px:
                            continue
                        xx = sx + k
                        if xx > 255:
                            break
                        if (clip and xx < 8) or owner[xx]:
                            continue
                        owner[xx] = 1
                        bg = line[xx] & 3
                        if hit_check and bg and xx != 255:
                            dn = self.dot_den
                            self.s0_cycle = ((line_dot + xx + self.S0_DELAY) * self.dot_num + dn - 1) // dn
                            hit_check = False
                        if bg and behind:
                            continue
                        line[xx] = px
        start = y << 8
        self.framebuffer_idx[start:start + 256] = line.translate(self._pal_tt)

    def blank_line(self, y: int) -> None:
        """Rendering disabled: the PPU outputs the backdrop (or $3Fxx colour)."""
        if self.pal_dirty:
            self._rebuild_palette()
        v = self.address
        if (v & 0x3F00) == 0x3F00:
            colour = self.palette[_palette_mirror(v)] & (0x30 if self.mask & 1 else 0x3F)
        else:
            colour = self._pal_tt[0]
        start = y << 8
        self.framebuffer_idx[start:start + 256] = bytes((colour,)) * 256

    def settle_sprite0(self) -> None:
        if self.s0_cycle >= 0:
            self.status |= 0x40
            self.s0_cycle = -1

    # ------------------------------------------------------- compatibility
    @property
    def framebuffer(self) -> bytes:
        """Packed RGB frame (256x240x3) using the active palette/emphasis."""
        return frame_to_rgb(self.framebuffer_idx, self.emphasis)

    def finish_frame(self) -> bytearray:
        return self.framebuffer_idx

    def render(self) -> bytes:
        """Debug helper: redraw the whole frame from the current state."""
        saved = self.address
        self.address = self.temp_address
        self.spr_dirty = True
        for y in range(SCREEN_H):
            if self.mask & 0x18:
                self.render_line(y, -10**9)
                self.increment_y()
                self.copy_x()
            else:
                self.blank_line(y)
        self.address = saved
        self.s0_cycle = -1
        return self.framebuffer

    def state(self) -> dict:
        keys = ("ctrl", "mask", "status", "oam_address", "address", "temp_address",
                "fine_x", "write_latch", "read_buffer", "_open_bus", "scanline",
                "odd_frame", "frame_number", "emphasis")
        st = {k: getattr(self, k) for k in keys}
        st["vram"] = bytes(self.vram)
        st["palette"] = bytes(self.palette)
        st["oam"] = bytes(self.oam)
        return st

    def load_state(self, st: dict) -> None:
        for k, val in st.items():
            if k in ("vram", "palette", "oam"):
                getattr(self, k)[:] = val
            else:
                setattr(self, k, val)
        self.pal_dirty = True
        self.spr_dirty = True
        self.s0_cycle = -1
        self.chr_gen += 1
        self._world_cache.clear()


# ----------------------------------------------------------- RGB conversion
def _build_rgb_tables(palette: tuple) -> list:
    """Per-emphasis (0-7) R/G/B translate tables for NES colour indices."""
    tables = []
    for emph in range(8):
        rt = bytearray(256)
        gt = bytearray(256)
        bt = bytearray(256)
        for idx in range(64):
            r, g, b = palette[idx]
            if emph:
                # 2C02 emphasis attenuates the non-emphasized channels (~0.75).
                if emph & 1:   # red
                    g = g * 3 // 4
                    b = b * 3 // 4
                if emph & 2:   # green
                    r = r * 3 // 4
                    b = b * 3 // 4
                if emph & 4:   # blue
                    r = r * 3 // 4
                    g = g * 3 // 4
            rt[idx], gt[idx], bt[idx] = r, g, b
        tables.append((bytes(rt), bytes(gt), bytes(bt)))
    return tables


_RGB_TABLES = _build_rgb_tables(NES_PALETTE)
_DISPLAY_PALETTE = NES_PALETTE


def set_display_palette(palette: tuple) -> None:
    global _RGB_TABLES, _DISPLAY_PALETTE
    _RGB_TABLES = _build_rgb_tables(palette)
    _DISPLAY_PALETTE = tuple(palette)


def frame_to_rgb(frame_idx: bytes, emphasis: int = 0, out: Optional[bytearray] = None) -> bytearray:
    rt, gt, bt = _RGB_TABLES[emphasis & 7]
    buf = out if out is not None else bytearray(len(frame_idx) * 3)
    buf[0::3] = frame_idx.translate(rt)
    buf[1::3] = frame_idx.translate(gt)
    buf[2::3] = frame_idx.translate(bt)
    return buf

# Status flags
C_FLAG = 0x01
Z_FLAG = 0x02
I_FLAG = 0x04
D_FLAG = 0x08
B_FLAG = 0x10
U_FLAG = 0x20
V_FLAG = 0x40
N_FLAG = 0x80


@dataclass(frozen=True, slots=True)
class Instruction:
    name: str
    mode: str
    cycles: int


# Every byte from $00 through $FF, row-major. The "KIL" entries are the
# hardware-jamming opcodes; unofficial NOPs retain their real operand lengths.
_OPCODE_ROWS = (
    "BRK IMP 7|ORA IZX 6|KIL IMP 2|SLO IZX 8|NOP ZP 3|ORA ZP 3|ASL ZP 5|SLO ZP 5|PHP IMP 3|ORA IMM 2|ASL ACC 2|ANC IMM 2|NOP ABS 4|ORA ABS 4|ASL ABS 6|SLO ABS 6",
    "BPL REL 2|ORA IZY 5|KIL IMP 2|SLO IZY 8|NOP ZPX 4|ORA ZPX 4|ASL ZPX 6|SLO ZPX 6|CLC IMP 2|ORA ABY 4|NOP IMP 2|SLO ABY 7|NOP ABX 4|ORA ABX 4|ASL ABX 7|SLO ABX 7",
    "JSR ABS 6|AND IZX 6|KIL IMP 2|RLA IZX 8|BIT ZP 3|AND ZP 3|ROL ZP 5|RLA ZP 5|PLP IMP 4|AND IMM 2|ROL ACC 2|ANC IMM 2|BIT ABS 4|AND ABS 4|ROL ABS 6|RLA ABS 6",
    "BMI REL 2|AND IZY 5|KIL IMP 2|RLA IZY 8|NOP ZPX 4|AND ZPX 4|ROL ZPX 6|RLA ZPX 6|SEC IMP 2|AND ABY 4|NOP IMP 2|RLA ABY 7|NOP ABX 4|AND ABX 4|ROL ABX 7|RLA ABX 7",
    "RTI IMP 6|EOR IZX 6|KIL IMP 2|SRE IZX 8|NOP ZP 3|EOR ZP 3|LSR ZP 5|SRE ZP 5|PHA IMP 3|EOR IMM 2|LSR ACC 2|ALR IMM 2|JMP ABS 3|EOR ABS 4|LSR ABS 6|SRE ABS 6",
    "BVC REL 2|EOR IZY 5|KIL IMP 2|SRE IZY 8|NOP ZPX 4|EOR ZPX 4|LSR ZPX 6|SRE ZPX 6|CLI IMP 2|EOR ABY 4|NOP IMP 2|SRE ABY 7|NOP ABX 4|EOR ABX 4|LSR ABX 7|SRE ABX 7",
    "RTS IMP 6|ADC IZX 6|KIL IMP 2|RRA IZX 8|NOP ZP 3|ADC ZP 3|ROR ZP 5|RRA ZP 5|PLA IMP 4|ADC IMM 2|ROR ACC 2|ARR IMM 2|JMP IND 5|ADC ABS 4|ROR ABS 6|RRA ABS 6",
    "BVS REL 2|ADC IZY 5|KIL IMP 2|RRA IZY 8|NOP ZPX 4|ADC ZPX 4|ROR ZPX 6|RRA ZPX 6|SEI IMP 2|ADC ABY 4|NOP IMP 2|RRA ABY 7|NOP ABX 4|ADC ABX 4|ROR ABX 7|RRA ABX 7",
    "NOP IMM 2|STA IZX 6|NOP IMM 2|SAX IZX 6|STY ZP 3|STA ZP 3|STX ZP 3|SAX ZP 3|DEY IMP 2|NOP IMM 2|TXA IMP 2|XAA IMM 2|STY ABS 4|STA ABS 4|STX ABS 4|SAX ABS 4",
    "BCC REL 2|STA IZY 6|KIL IMP 2|AHX IZY 6|STY ZPX 4|STA ZPX 4|STX ZPY 4|SAX ZPY 4|TYA IMP 2|STA ABY 5|TXS IMP 2|TAS ABY 5|SHY ABX 5|STA ABX 5|SHX ABY 5|AHX ABY 5",
    "LDY IMM 2|LDA IZX 6|LDX IMM 2|LAX IZX 6|LDY ZP 3|LDA ZP 3|LDX ZP 3|LAX ZP 3|TAY IMP 2|LDA IMM 2|TAX IMP 2|LAX IMM 2|LDY ABS 4|LDA ABS 4|LDX ABS 4|LAX ABS 4",
    "BCS REL 2|LDA IZY 5|KIL IMP 2|LAX IZY 5|LDY ZPX 4|LDA ZPX 4|LDX ZPY 4|LAX ZPY 4|CLV IMP 2|LDA ABY 4|TSX IMP 2|LAS ABY 4|LDY ABX 4|LDA ABX 4|LDX ABY 4|LAX ABY 4",
    "CPY IMM 2|CMP IZX 6|NOP IMM 2|DCP IZX 8|CPY ZP 3|CMP ZP 3|DEC ZP 5|DCP ZP 5|INY IMP 2|CMP IMM 2|DEX IMP 2|AXS IMM 2|CPY ABS 4|CMP ABS 4|DEC ABS 6|DCP ABS 6",
    "BNE REL 2|CMP IZY 5|KIL IMP 2|DCP IZY 8|NOP ZPX 4|CMP ZPX 4|DEC ZPX 6|DCP ZPX 6|CLD IMP 2|CMP ABY 4|NOP IMP 2|DCP ABY 7|NOP ABX 4|CMP ABX 4|DEC ABX 7|DCP ABX 7",
    "CPX IMM 2|SBC IZX 6|NOP IMM 3|ISC IZX 8|CPX ZP 3|SBC ZP 3|INC ZP 5|ISC ZP 5|INX IMP 2|SBC IMM 2|NOP IMP 2|SBC IMM 2|CPX ABS 4|SBC ABS 4|INC ABS 6|ISC ABS 6",
    "BEQ REL 2|SBC IZY 5|KIL IMP 2|ISC IZY 8|NOP ZPX 4|SBC ZPX 4|INC ZPX 6|ISC ZPX 6|SED IMP 2|SBC ABY 4|NOP IMP 2|ISC ABY 7|NOP ABX 4|SBC ABX 4|INC ABX 7|ISC ABX 7",
)


def _build_opcode_table() -> tuple[Instruction, ...]:
    entries: list[Instruction] = []
    for row in _OPCODE_ROWS:
        for item in row.split("|"):
            name, mode, cycles = item.split()
            entries.append(Instruction(name, mode, int(cycles)))
    if len(entries) != 256:
        raise RuntimeError(f"Opcode table has {len(entries)} entries, expected 256.")
    return tuple(entries)


OPCODES = _build_opcode_table()

# FCEUX x6502.cpp CycTable — base cycle counts for every opcode byte.
FCEUX_CYCLES: tuple[int, ...] = (
    7, 6, 2, 8, 3, 3, 5, 5, 3, 2, 2, 2, 4, 4, 6, 6,
    2, 5, 2, 8, 4, 4, 6, 6, 2, 4, 2, 7, 4, 4, 7, 7,
    6, 6, 2, 8, 3, 3, 5, 5, 4, 2, 2, 2, 4, 4, 6, 6,
    2, 5, 2, 8, 4, 4, 6, 6, 2, 4, 2, 7, 4, 4, 7, 7,
    6, 6, 2, 8, 3, 3, 5, 5, 3, 2, 2, 2, 3, 4, 6, 6,
    2, 5, 2, 8, 4, 4, 6, 6, 2, 4, 2, 7, 4, 4, 7, 7,
    6, 6, 2, 8, 3, 3, 5, 5, 4, 2, 2, 2, 5, 4, 6, 6,
    2, 5, 2, 8, 4, 4, 6, 6, 2, 4, 2, 7, 4, 4, 7, 7,
    2, 6, 2, 6, 3, 3, 3, 3, 2, 2, 2, 2, 4, 4, 4, 4,
    2, 6, 2, 6, 4, 4, 4, 4, 2, 5, 2, 5, 5, 5, 5, 5,
    2, 6, 2, 6, 3, 3, 3, 3, 2, 2, 2, 2, 4, 4, 4, 4,
    2, 5, 2, 5, 4, 4, 4, 4, 2, 4, 2, 4, 4, 4, 4, 4,
    2, 6, 2, 8, 3, 3, 5, 5, 2, 2, 2, 2, 4, 4, 6, 6,
    2, 5, 2, 8, 4, 4, 6, 6, 2, 4, 2, 7, 4, 4, 7, 7,
    2, 6, 3, 8, 3, 3, 5, 5, 2, 2, 2, 2, 4, 4, 6, 6,
    2, 5, 2, 8, 4, 4, 6, 6, 2, 4, 2, 7, 4, 4, 7, 7,
)

# FCEUX / NESDev alternate mnemonics (disassembler may show either form).
FCEUX_ALIASES: dict[str, tuple[str, ...]] = {
    "SLO": ("ASO", "SLO"),
    "SRE": ("LSE", "SRE"),
    "DCP": ("DCM", "DCP"),
    "ISC": ("ISB", "INS", "ISC"),
    "AHX": ("AXA", "SHA", "AHX"),
    "SHX": ("XAS", "SXA", "SHX"),
    "SHY": ("SAY", "SYA", "SHY"),
    "TAS": ("SHS", "XAS", "TAS"),
    "AXS": ("SBX", "AXS"),
    "ALR": ("ASR", "ALR"),
    "KIL": ("JAM", "HLT", "STP", "KIL"),
    "LAS": ("LAR", "LAS"),
    "XAA": ("ANE", "XAA"),
    "SAX": ("AAX", "SAX"),
}

# Interactive debugger prompt cheat-sheet (FCEUX-inspired).
PROMPT_HELP = """\
acnesemu debugger prompts (FCEUX-inspired)
--------------------------------------
  help / ?              this help
  opcodes / op          list all 256 FCEUX-aligned opcodes
  regs / r              CPU registers + flags
  dis [addr] [n]        disassemble n lines from addr (default PC)
  step / s [n]          step n CPU instructions (default 1)
  frame / f [n]         run n PPU frames (default 1)
  reset                 CPU/PPU/APU reset
  mem <addr> [len]      hex dump (default 16 bytes)
  peek <addr>           read one byte
  poke <addr> <val>     write one byte
  load <path.nes>       load cartridge
  run / gui             open the Tk GUI with the current ROM
  quit / q              leave the prompt
"""


def fceux_name(opcode: int) -> str:
    """Primary FCEUX-style mnemonic for an opcode byte."""
    name = OPCODES[opcode].name
    aliases = FCEUX_ALIASES.get(name)
    return aliases[0] if aliases else name


def assert_fceux_opcode_table() -> None:
    """Every byte must match FCEUX base cycles and have an execute path."""
    if len(OPCODES) != 256 or len(FCEUX_CYCLES) != 256:
        raise RuntimeError("Opcode / FCEUX cycle tables must be 256 entries.")
    for opcode, (ins, cycles) in enumerate(zip(OPCODES, FCEUX_CYCLES)):
        if ins.cycles != cycles:
            raise RuntimeError(
                f"Opcode ${opcode:02X} ({ins.name}) cycles {ins.cycles} != FCEUX {cycles}"
            )


MODE_LENGTH = {
    "IMP": 1, "ACC": 1, "IMM": 2, "ZP": 2, "ZPX": 2, "ZPY": 2,
    "IZX": 2, "IZY": 2, "REL": 2, "ABS": 3, "ABX": 3, "ABY": 3, "IND": 3,
}


# ---------------------------------------------------------------------------
# CPU — Ricoh 2A03 (NMOS 6502 core, no decimal mode)
# ---------------------------------------------------------------------------
# The interpreter loop is *generated* at import time: every one of the 256
# opcodes becomes an inline block inside a single function, reached through an
# 8-level binary decision tree on the opcode byte.  Registers and flags live in
# fast local variables for the whole run, RAM / PRG-ROM accesses are inlined,
# and only I/O ($2000-$7FFF) goes through a call into the bus.  This is the
# piece that lets a pure-Python NES reach full Famicom speed.
#
# Flags are kept unpacked:  c (0/1), v (truthy = V set), i, d, and `nz`, a
# lazily-evaluated result value where  Z = (nz & 0xFF) == 0  and
# N = (nz & 0x180) != 0  (bit 8 lets BIT/PLP express N=1 together with Z=1).

_RD_ABS = (
    "if t < 0x2000: m = ram[t & 0x7FF]\n"
    "elif t >= 0x8000: m = prg[t - 0x8000]\n"
    "else: m = rdio(t, cyc + {n})"
)
_WR_ABS = (
    "if t < 0x2000: ram[t & 0x7FF] = {val}\n"
    "else:\n"
    "    cyc += wrio(t, {val}, cyc + {n})\n"
    "    chk = bus.wchk\n"
    "    bus.wchk = 1"
)
# Read-modify-write: NMOS writes the old value back, then the new one, on two
# consecutive cycles (MMC1 relies on this to ignore the second write).
_RMW_WR = (
    "if t < 0x2000: ram[t & 0x7FF] = r\n"
    "else:\n"
    "    cyc += wrio(t, m, cyc + {n1})\n"
    "    cyc += wrio(t, r, cyc + {n})\n"
    "    chk = 1"
)
_PACK_P = (
    "((0x80 if nz & 0x180 else 0) | (0x40 if v else 0) | 0x20 | (8 if d else 0)"
    " | (4 if i else 0) | (0 if nz & 0xFF else 2) | c)"
)
_UNPACK_P = (
    "c = r & 1\n"
    "i = (r >> 2) & 1\n"
    "d = (r >> 3) & 1\n"
    "v = r & 0x40\n"
    "nz = (0x100 if r & 0x80 else 0) | (0 if r & 2 else 1)"
)

_READ_OPS = {
    "ADC": "s = a + m + c\nc = s >> 8\nv = (a ^ s) & (m ^ s) & 0x80\na = s & 0xFF\nnz = a",
    "SBC": "m ^= 0xFF\ns = a + m + c\nc = s >> 8\nv = (a ^ s) & (m ^ s) & 0x80\na = s & 0xFF\nnz = a",
    "AND": "a &= m\nnz = a",
    "ORA": "a |= m\nnz = a",
    "EOR": "a ^= m\nnz = a",
    "LDA": "a = m\nnz = m",
    "LDX": "x = m\nnz = m",
    "LDY": "y = m\nnz = m",
    "LAX": "a = x = m\nnz = m",
    "CMP": "s = a - m\nc = 0 if s < 0 else 1\nnz = s & 0xFF",
    "CPX": "s = x - m\nc = 0 if s < 0 else 1\nnz = s & 0xFF",
    "CPY": "s = y - m\nc = 0 if s < 0 else 1\nnz = s & 0xFF",
    "BIT": "nz = ((m & 0x80) << 1) | (a & m)\nv = m & 0x40",
    "NOP": "pass",
    "ANC": "a &= m\nnz = a\nc = a >> 7",
    "ALR": "a &= m\nc = a & 1\na >>= 1\nnz = a",
    "ARR": "a &= m\na = (a >> 1) | (c << 7)\nnz = a\nc = (a >> 6) & 1\nv = ((a >> 6) ^ (a >> 5)) & 1",
    "AXS": "s = (a & x) - m\nc = 0 if s < 0 else 1\nx = s & 0xFF\nnz = x",
    "XAA": "a = x & m\nnz = a",
    "LAS": "a = x = sp = m & sp\nnz = a",
}
_WRITE_OPS = {
    "STA": "a", "STX": "x", "STY": "y", "SAX": "(a & x)",
}
_RMW_OPS = {
    "ASL": "c = m >> 7\nr = (m << 1) & 0xFF\nnz = r",
    "LSR": "c = m & 1\nr = m >> 1\nnz = r",
    "ROL": "r = ((m << 1) | c) & 0xFF\nc = m >> 7\nnz = r",
    "ROR": "r = (m >> 1) | (c << 7)\nc = m & 1\nnz = r",
    "INC": "r = (m + 1) & 0xFF\nnz = r",
    "DEC": "r = (m - 1) & 0xFF\nnz = r",
    "SLO": "c = m >> 7\nr = (m << 1) & 0xFF\na |= r\nnz = a",
    "RLA": "r = ((m << 1) | c) & 0xFF\nc = m >> 7\na &= r\nnz = a",
    "SRE": "c = m & 1\nr = m >> 1\na ^= r\nnz = a",
    "RRA": ("r = (m >> 1) | (c << 7)\nc = m & 1\n"
            "s = a + r + c\nc = s >> 8\nv = (a ^ s) & (r ^ s) & 0x80\na = s & 0xFF\nnz = a"),
    "DCP": "r = (m - 1) & 0xFF\ns = a - r\nc = 0 if s < 0 else 1\nnz = s & 0xFF",
    "ISC": ("r = (m + 1) & 0xFF\nq = r ^ 0xFF\n"
            "s = a + q + c\nc = s >> 8\nv = (a ^ s) & (q ^ s) & 0x80\na = s & 0xFF\nnz = a"),
}
_ACC_OPS = {
    "ASL": "c = a >> 7\na = (a << 1) & 0xFF\nnz = a",
    "LSR": "c = a & 1\na >>= 1\nnz = a",
    "ROL": "r = ((a << 1) | c) & 0xFF\nc = a >> 7\na = r\nnz = a",
    "ROR": "r = (a >> 1) | (c << 7)\nc = a & 1\na = r\nnz = a",
}
_IMPLIED_OPS = {
    "CLC": "c = 0", "SEC": "c = 1", "CLV": "v = 0", "CLD": "d = 0", "SED": "d = 1",
    "SEI": "if not i:\n    ilat = 1\n    chk = chk or 1\ni = 1", "CLI": "i = 0\nchk = 2",
    "TAX": "x = a\nnz = a", "TAY": "y = a\nnz = a", "TXA": "a = x\nnz = a",
    "TYA": "a = y\nnz = a", "TSX": "x = sp\nnz = sp", "TXS": "sp = x",
    "INX": "x = (x + 1) & 0xFF\nnz = x", "INY": "y = (y + 1) & 0xFF\nnz = y",
    "DEX": "x = (x - 1) & 0xFF\nnz = x", "DEY": "y = (y - 1) & 0xFF\nnz = y",
    "NOP": "pass",
    "PHA": "ram[0x100 | sp] = a\nsp = (sp - 1) & 0xFF",
    "PHP": "ram[0x100 | sp] = " + _PACK_P + " | 0x10\nsp = (sp - 1) & 0xFF",
    "PLA": "sp = (sp + 1) & 0xFF\na = ram[0x100 | sp]\nnz = a",
    "PLP": ("sp = (sp + 1) & 0xFF\nr = ram[0x100 | sp]\nq = i\n" + _UNPACK_P
            + "\nif q and not i:\n    chk = 2\nelif i and not q:\n    ilat = 1\n    chk = chk or 1\nelse:\n    chk = chk or 1"),
}
_BRANCHES = {
    "BPL": "not (nz & 0x180)", "BMI": "nz & 0x180",
    "BVC": "not v", "BVS": "v",
    "BCC": "not c", "BCS": "c",
    "BNE": "nz & 0xFF", "BEQ": "not (nz & 0xFF)",
}
_PAGE_PENALTY = {"ORA", "AND", "EOR", "ADC", "LDA", "LDX", "LDY", "CMP", "SBC",
                 "LAX", "LAS", "NOP"}


def _opcode_block(op: int) -> str:
    """Python source (unindented) that executes opcode `op`.

    On entry: `pc` points at the opcode, `b1`/`b2` hold the next two bytes.
    """
    ins = OPCODES[op]
    name, mode, base = ins.name, ins.mode, ins.cycles
    if op == 0xE2:
        base = 2   # FCEUX's CycTable lists 3; real 2A03 hardware takes 2
    n = base - 1  # cycle offset of the bus access (the instruction's last cycle)
    out: list[str] = []
    emit = out.append

    if name in _BRANCHES:
        emit(f"if {_BRANCHES[name]}:")
        emit("    t = (pc + 2 + ((b1 ^ 0x80) - 0x80)) & 0xFFFF")
        emit("    cyc += 4 if (t ^ (pc + 2)) & 0xFF00 else 3")
        emit("    pc = t")
        emit("else:")
        emit("    pc += 2")
        emit("    cyc += 2")
        return "\n".join(out)
    if name == "JMP":
        if mode == "ABS":
            emit("pc = b1 | (b2 << 8)")
        else:
            emit("t = b1 | (b2 << 8)")
            emit(_RD_ABS.format(n=3))
            emit("q = m")
            emit("t = (t & 0xFF00) | ((t + 1) & 0xFF)")
            emit(_RD_ABS.format(n=4))
            emit("pc = q | (m << 8)")
        emit(f"cyc += {base}")
        return "\n".join(out)
    if name == "JSR":
        emit("t = pc + 2")
        emit("ram[0x100 | sp] = t >> 8")
        emit("sp = (sp - 1) & 0xFF")
        emit("ram[0x100 | sp] = t & 0xFF")
        emit("sp = (sp - 1) & 0xFF")
        emit("pc = b1 | (b2 << 8)")
        emit("cyc += 6")
        return "\n".join(out)
    if name == "RTS":
        emit("sp = (sp + 1) & 0xFF")
        emit("t = ram[0x100 | sp]")
        emit("sp = (sp + 1) & 0xFF")
        emit("pc = ((t | (ram[0x100 | sp] << 8)) + 1) & 0xFFFF")
        emit("cyc += 6")
        return "\n".join(out)
    if name == "RTI":
        emit("sp = (sp + 1) & 0xFF")
        emit("r = ram[0x100 | sp]")
        emit(_UNPACK_P)
        emit("sp = (sp + 1) & 0xFF")
        emit("t = ram[0x100 | sp]")
        emit("sp = (sp + 1) & 0xFF")
        emit("pc = t | (ram[0x100 | sp] << 8)")
        emit("cyc += 6")
        emit("chk = 1")
        return "\n".join(out)
    if name == "BRK":
        emit("t = (pc + 2) & 0xFFFF")
        emit("ram[0x100 | sp] = t >> 8")
        emit("sp = (sp - 1) & 0xFF")
        emit("ram[0x100 | sp] = t & 0xFF")
        emit("sp = (sp - 1) & 0xFF")
        emit("ram[0x100 | sp] = " + _PACK_P + " | 0x10")
        emit("sp = (sp - 1) & 0xFF")
        emit("i = 1")
        emit("pc = vec(0xFFFE)")
        emit("cyc += 7")
        return "\n".join(out)
    if name == "KIL":
        emit("self.jammed = True")
        emit("cyc = target if target > cyc else cyc + 2")
        return "\n".join(out)

    size = MODE_LENGTH[mode]
    if name in ("AHX", "SHX", "SHY", "TAS"):
        # Unstable stores: value = reg & (base high byte + 1); on a page
        # crossing that value also replaces the target's high byte.
        if mode == "IZY":
            emit("q = ram[b1] + y")
            emit("h = ram[(b1 + 1) & 0xFF]")
        else:
            emit(f"q = b1 + {'x' if mode == 'ABX' else 'y'}")
            emit("h = b2")
        emit("t = ((h << 8) + q) & 0xFFFF")
        src = {"AHX": "a & x", "SHX": "x", "SHY": "y", "TAS": "a & x"}[name]
        if name == "TAS":
            emit("sp = a & x")
        emit(f"r = ({src}) & ((h + 1) & 0xFF)")
        emit("if q > 0xFF: t = (r << 8) | (t & 0xFF)")
        emit(_WR_ABS.format(val="r", n=n))
        emit(f"pc += {size}")
        emit(f"cyc += {base}")
        return "\n".join(out)
    # ---- effective address ------------------------------------------------
    penalty = name in _PAGE_PENALTY
    zp = False
    if mode in ("IMP", "ACC"):
        pass
    elif mode == "IMM":
        pass
    elif mode == "ZP":
        emit("t = b1")
        zp = True
    elif mode == "ZPX":
        emit("t = (b1 + x) & 0xFF")
        zp = True
    elif mode == "ZPY":
        emit("t = (b1 + y) & 0xFF")
        zp = True
    elif mode == "ABS":
        emit("t = b1 | (b2 << 8)")
    elif mode in ("ABX", "ABY"):
        reg = "x" if mode == "ABX" else "y"
        emit(f"t = ((b1 | (b2 << 8)) + {reg}) & 0xFFFF")
        if penalty:
            emit(f"if b1 + {reg} > 0xFF:")
            emit("    cyc += 1")
            if name != "NOP":
                emit("    if 0x2100 <= t < 0x4120: rdio(t - 0x100, cyc + %d)" % (n - 1))
    elif mode == "IZX":
        emit("q = (b1 + x) & 0xFF")
        emit("t = ram[q] | (ram[(q + 1) & 0xFF] << 8)")
    elif mode == "IZY":
        emit("q = ram[b1]")
        if penalty:
            emit("if q + y > 0xFF: cyc += 1")
        emit("t = ((q | (ram[(b1 + 1) & 0xFF] << 8)) + y) & 0xFFFF")
    else:  # pragma: no cover - table guarantees coverage
        raise RuntimeError(f"unhandled mode {mode}")

    # ---- operation ----------------------------------------------------------
    if mode == "ACC":
        emit(_ACC_OPS[name])
    elif mode == "IMP":
        emit(_IMPLIED_OPS[name])
    elif name in _READ_OPS:
        if mode == "IMM":
            emit("m = b1")
        elif name == "NOP":
            pass  # unofficial NOP: operand fetch has no visible effect here
        elif zp:
            emit("m = ram[t]")
        else:
            emit(_RD_ABS.format(n=n))
        emit(_READ_OPS[name])
    elif name in _WRITE_OPS:
        val = _WRITE_OPS[name]
        if zp:
            emit(f"ram[t] = {val}")
        else:
            emit(_WR_ABS.format(val=val, n=n))
    elif name in _RMW_OPS:
        if zp:
            emit("m = ram[t]")
            emit(_RMW_OPS[name])
            emit("ram[t] = r")
        else:
            emit(_RD_ABS.format(n=n - 2))
            emit(_RMW_OPS[name])
            emit(_RMW_WR.format(n1=n - 1, n=n))
    else:  # pragma: no cover
        raise RuntimeError(f"opcode ${op:02X} {name} has no generator")
    emit(f"pc += {size}")
    emit(f"cyc += {base}")
    return "\n".join(out)


def _indent(src: str, level: int) -> str:
    pad = "    " * level
    return "\n".join(pad + line if line.strip() else line for line in src.split("\n"))


def _dispatch_tree(lo: int, hi: int, level: int) -> str:
    if hi - lo == 1:
        return _indent(_opcode_block(lo), level)
    mid = (lo + hi) // 2
    return (
        _indent(f"if op < {mid}:", level) + "\n"
        + _dispatch_tree(lo, mid, level + 1) + "\n"
        + _indent("else:", level) + "\n"
        + _dispatch_tree(mid, hi, level + 1)
    )


def _build_cpu_runner(mapper_clock: bool):
    """Compile the CPU interpreter loop.  Returns run(self, target) -> None."""
    body = [
        "def run(self, target):",
        "    bus = self.bus",
        "    ram = bus.ram",
        "    prg = bus.prg32",
        "    rdio = bus.read_io",
        "    wrio = bus.write_io",
        "    peek = bus.peek",
        "    vec = bus.read16",
        "    a = self.a; x = self.x; y = self.y; sp = self.sp; pc = self.pc",
        "    nz = self.nz; c = self.c; v = self.v; i = self.i; d = self.d",
        "    cyc = self.cycles",
        "    chk = 1",
        "    ilat = 0",
        "    m = r = s = t = q = h = 0",
    ]
    if mapper_clock:
        body += [
            "    mclock = bus.cart.mapper.clock_cpu",
            "    last = cyc",
        ]
    body += [
        "    while cyc < target:",
        "        if chk:",
        "            if chk > 1:",
        "                chk -= 1",
        "            else:",
        "                chk = 0",
        "                if bus.nmi_line:",
        "                    bus.nmi_line = False",
        "                    ram[0x100 | sp] = pc >> 8",
        "                    sp = (sp - 1) & 0xFF",
        "                    ram[0x100 | sp] = pc & 0xFF",
        "                    sp = (sp - 1) & 0xFF",
        "                    ram[0x100 | sp] = " + _PACK_P,
        "                    sp = (sp - 1) & 0xFF",
        "                    i = 1",
        "                    pc = vec(0xFFFA)",
        "                    cyc += 7",
        "                    self.jammed = False",
        "                    chk = 1",
        "                    continue",
        "                if (not i or ilat) and bus.irq_asserted():",
        "                    ilat = 0",
        "                    ram[0x100 | sp] = pc >> 8",
        "                    sp = (sp - 1) & 0xFF",
        "                    ram[0x100 | sp] = pc & 0xFF",
        "                    sp = (sp - 1) & 0xFF",
        "                    ram[0x100 | sp] = " + _PACK_P,
        "                    sp = (sp - 1) & 0xFF",
        "                    i = 1",
        "                    pc = vec(0xFFFE)",
        "                    cyc += 7",
        "                    self.jammed = False",
        "                    continue",
        "                ilat = 0",
        "                if self.jammed:",
        "                    cyc = target",
        "                    break",
        "        if 0x8000 <= pc < 0xFFFE:",
        "            t = pc - 0x8000",
        "            op = prg[t]; b1 = prg[t + 1]; b2 = prg[t + 2]",
        "        elif pc < 0x2000:",
        "            t = pc & 0x7FF",
        "            op = ram[t]; b1 = ram[(t + 1) & 0x7FF]; b2 = ram[(t + 2) & 0x7FF]",
        "        else:",
        "            pc &= 0xFFFF",
        "            op = peek(pc); b1 = peek((pc + 1) & 0xFFFF); b2 = peek((pc + 2) & 0xFFFF)",
        _dispatch_tree(0, 256, 2),
    ]
    if mapper_clock:
        body += [
            "        mclock(cyc - last)",
            "        last = cyc",
            "        chk = chk or 1",
        ]
    body += [
        "    self.a = a; self.x = x; self.y = y; self.sp = sp; self.pc = pc & 0xFFFF",
        "    self.nz = nz; self.c = c; self.v = v; self.i = i; self.d = d",
        "    self.cycles = cyc",
    ]
    src = "\n".join(body) + "\n"
    namespace: dict = {}
    exec(compile(src, f"<acnes-cpu{'-mclk' if mapper_clock else ''}>", "exec"), namespace)
    return namespace["run"], src


_CPU_RUN_FAST, _CPU_SRC = _build_cpu_runner(False)
_CPU_RUN_MCLK, _ = _build_cpu_runner(True)


class CPU:
    """2A03 CPU state + generated interpreter (see _build_cpu_runner)."""

    def __init__(self, bus: "Bus") -> None:
        self.bus = bus
        self.a = self.x = self.y = 0
        self.sp = 0xFD
        self.pc = 0
        self.nz = 1
        self.c = 0
        self.v = 0
        self.i = 1
        self.d = 0
        self.cycles = 0
        self.jammed = False
        self.stall = 0
        self._runner = _CPU_RUN_FAST

    # -- packed status register (debugger / save states / prompt) ----------
    @property
    def p(self) -> int:
        nz = self.nz
        return (
            (0x80 if nz & 0x180 else 0) | (0x40 if self.v else 0) | 0x20
            | (8 if self.d else 0) | (4 if self.i else 0)
            | (0 if nz & 0xFF else 2) | (self.c & 1)
        )

    @p.setter
    def p(self, value: int) -> None:
        self.c = value & 1
        self.i = (value >> 2) & 1
        self.d = (value >> 3) & 1
        self.v = value & 0x40
        self.nz = (0x100 if value & 0x80 else 0) | (0 if value & 2 else 1)

    @property
    def total_cycles(self) -> int:
        return self.cycles

    @property
    def nmi_pending(self) -> bool:
        return self.bus.nmi_line

    @nmi_pending.setter
    def nmi_pending(self, value: bool) -> None:
        self.bus.nmi_line = bool(value)

    def select_runner(self) -> None:
        mapper = self.bus.cart.mapper
        self._runner = _CPU_RUN_MCLK if mapper.needs_cpu_clock else _CPU_RUN_FAST

    def run(self, target: int) -> None:
        self._runner(self, target)

    def step(self) -> int:
        """Execute exactly one instruction (or interrupt entry)."""
        before = self.cycles
        self._runner(self, before + 1)
        return self.cycles - before

    def reset(self) -> None:
        self.sp = (self.sp - 3) & 0xFF
        self.i = 1
        self.jammed = False
        self.bus.nmi_line = False
        self.pc = self.bus.read16(0xFFFC)

    def power(self) -> None:
        self.a = self.x = self.y = 0
        self.sp = 0xFD
        self.p = 0x24
        self.jammed = False
        self.bus.nmi_line = False
        self.pc = self.bus.read16(0xFFFC)

    def state(self) -> dict:
        return {k: getattr(self, k) for k in
                ("a", "x", "y", "sp", "pc", "nz", "c", "v", "i", "d", "cycles", "jammed")}

    def load_state(self, st: dict) -> None:
        for k, val in st.items():
            setattr(self, k, val)


# ---------------------------------------------------------------------------
# Bus — CPU address space, bank caches, controllers, OAM DMA
# ---------------------------------------------------------------------------
class Bus:
    """CPU memory map.

    PRG-ROM is mirrored into a flat 32 KiB `prg32` view that is re-copied
    whenever the mapper's PRG banking changes, so the CPU core reads ROM with
    a single index.  CHR banking is cached as eight 1 KiB offsets into
    cart.chr (`chr_off`) for the renderer; mappers with PPU-read side effects
    (MMC2/MMC4 latches) use the slow per-fetch path instead.
    """

    def __init__(self, cart: "Cartridge", cpu_clock: int = CPU_CLOCK) -> None:
        self.cart = cart
        self.cpu_clock = cpu_clock
        self.ram = bytearray(0x800)
        self.prg32 = bytearray(0x8003)       # +3 bytes so opcode prefetch never overruns
        self.nmi_line = False
        self.wchk = 1                    # interrupt-poll delay requested by the last I/O write
        self.open_bus = 0
        self.controller_state = [0, 0]
        self.controller_shift = [0, 0]
        self.controller_strobe = False
        self.input_read = False
        self.zapper = None
        self.nt_map = [0, 0x400, 0, 0x400]
        self.chr_off = [0] * 8
        self.chr_key = (0,) * 8
        self.chr_slow = False
        self.banks_dirty = True
        self.wram_fast = False
        self.wram_writable = True
        self.cheats: list = []           # dicts: addr, value, compare, enabled, name
        self.read_hooks: Optional[dict] = None
        self._prg_off = [-1, -1, -1, -1]
        self.ppu = PPU(cart)
        self.ppu.bus = self
        self.apu = APU(self)
        self.cpu = CPU(self)
        self.refresh_banks(force=True)
        self.cpu.select_runner()

    # ------------------------------------------------------------- caching
    def refresh_banks(self, force: bool = False) -> None:
        cart = self.cart
        mapper = cart.mapper
        prg = cart.prg
        plen = cart.prg_len
        view = self.prg32
        changed = False
        for w in range(4):
            base = 0x8000 + (w << 13)
            off = mapper.cpu_read(base)
            if off is None:
                key = -2
            else:
                off %= plen
                end = mapper.cpu_read(base + 0x1FFF)
                key = off if (end is not None and end % plen == off + 0x1FFF) else -3
            if key != self._prg_off[w] or force:
                self._prg_off[w] = key
                changed = True
                start = w << 13
                if key >= 0:
                    view[start:start + 0x2000] = prg[key:key + 0x2000]
                elif key == -2:
                    view[start:start + 0x2000] = bytes(0x2000)
                else:
                    for k in range(0x2000):
                        mapped = mapper.cpu_read(base + k)
                        view[start + k] = prg[mapped % plen] if mapped is not None else 0
        view[0x8000:0x8003] = view[0:3]
        if changed and self.cheats:
            self._apply_rom_cheats()
        mode = mapper.mirror_mode()
        remap = mode if isinstance(mode, tuple) else MIRROR_REMAP.get(mode, (0, 1, 0, 1))
        self.nt_map = [table << 10 for table in remap]
        cls = type(mapper)
        self.wram_fast = (
            cls.cpu_data is Mapper.cpu_data
            and cls.prg_ram_index is Mapper.prg_ram_index
            and mapper.cpu_read(0x6000) is None
            and mapper.prg_ram_enabled()
            and len(cart.prg_ram) >= 0x2000
        )
        self.wram_writable = mapper.prg_ram_writable()
        self.banks_dirty = True

    def refresh_ppu_banks(self) -> None:
        cart = self.cart
        mapper = cart.mapper
        self.banks_dirty = False
        mode = mapper.mirror_mode()
        remap = mode if isinstance(mode, tuple) else MIRROR_REMAP.get(mode, (0, 1, 0, 1))
        self.nt_map = [table << 10 for table in remap]
        if getattr(mapper, "chr_latch", False):
            self.chr_slow = True
            return
        slow = False
        clen = cart.chr_len
        offs = self.chr_off
        for s in range(8):
            base = s << 10
            off = mapper.ppu_read(base)
            if off is None:
                slow = True
                break
            end = mapper.ppu_read(base + 0x3FF)
            if end is None or end != off + 0x3FF or off + 0x400 > clen:
                slow = True
                break
            offs[s] = off
        self.chr_slow = slow
        self.chr_key = tuple(offs)

    # --------------------------------------------------------------- cheats
    def _apply_rom_cheats(self) -> None:
        view = self.prg32
        for cheat in self.cheats:
            if not cheat.get("enabled", True):
                continue
            addr = cheat["addr"]
            if addr < 0x8000:
                continue
            idx = addr - 0x8000
            window = idx >> 13
            key = self._prg_off[window]
            original = self.cart.prg[key + (idx & 0x1FFF)] if key >= 0 else view[idx]
            compare = cheat.get("compare")
            if compare is None or original == compare:
                view[idx] = cheat["value"]
        view[0x8000:0x8003] = view[0:3]

    def set_cheats(self, cheats: list) -> None:
        self.cheats = cheats
        self.refresh_banks(force=True)

    def apply_ram_cheats(self) -> None:
        for cheat in self.cheats:
            if cheat.get("enabled", True) and cheat["addr"] < 0x8000:
                compare = cheat.get("compare")
                addr = cheat["addr"]
                if compare is None or self.peek(addr) == compare:
                    self.write(addr, cheat["value"])

    # ---------------------------------------------------------------- reads
    def irq_asserted(self) -> bool:
        apu = self.apu
        return bool(self.cart.mapper.irq_pending or apu.frame_irq or apu.dmc.irq)

    def read16(self, address: int) -> int:
        return self.peek(address) | (self.peek((address + 1) & 0xFFFF) << 8)

    def read_io(self, address: int, cyc: int) -> int:
        if address < 0x4000:
            value = self.ppu.read_register(address, cyc)
        elif address < 0x4020:
            if address == 0x4016 or address == 0x4017:
                self.input_read = True
                port = address & 1
                if self.controller_strobe:
                    bit = self.controller_state[port] & 1
                else:
                    bit = self.controller_shift[port] & 1
                    self.controller_shift[port] = (self.controller_shift[port] >> 1) | 0x80
                value = (self.open_bus & 0xE0) | bit
                if port == 1 and self.zapper is not None:
                    value |= self.zapper.read_bits()
            elif address == 0x4015:
                self.apu.catch_up(cyc)
                value = self.apu.read_status() | (self.open_bus & 0x20)
            else:
                value = self.open_bus
        elif address >= 0x6000 and self.wram_fast:
            value = self.cart.prg_ram[address & 0x1FFF]
        else:
            value = self.cart.cpu_read(address)
        self.open_bus = value
        return value

    def read(self, address: int) -> int:
        address &= 0xFFFF
        if address < 0x2000:
            return self.ram[address & 0x7FF]
        if address >= 0x8000:
            return self.prg32[address - 0x8000]
        return self.read_io(address, self.cpu.cycles)

    def peek(self, address: int) -> int:
        """Side-effect free read (debugger, DMC, opcode fetch outside ROM)."""
        address &= 0xFFFF
        if address < 0x2000:
            return self.ram[address & 0x7FF]
        if address >= 0x8000:
            return self.prg32[address - 0x8000]
        if address >= 0x6000:
            if self.wram_fast:
                return self.cart.prg_ram[address & 0x1FFF]
            return self.cart.cpu_read(address)
        return self.open_bus

    # --------------------------------------------------------------- writes
    def write_io(self, address: int, value: int, cyc: int) -> int:
        """Handle a CPU write outside RAM; returns extra CPU stall cycles."""
        self.open_bus = value
        if address < 0x4000:
            self.ppu.write_register(address, value, cyc)
            return 0
        if address < 0x4020:
            if address == 0x4014:
                self._oam_dma(value)
                return 513 + (cyc & 1)
            if address == 0x4016:
                old = self.controller_strobe
                self.controller_strobe = bool(value & 1)
                if self.controller_strobe or old:
                    self.controller_shift[0] = self.controller_state[0]
                    self.controller_shift[1] = self.controller_state[1]
                return 0
            if address < 0x4018:
                self.apu.catch_up(cyc)
                self.apu.write(address, value)
            return 0
        cart = self.cart
        cart.write_cycle = cyc
        mapper = cart.mapper
        if address >= 0x8000:
            mapper.cpu_write(address, value)
            self.refresh_banks()
        elif address >= 0x6000:
            if mapper.cpu_write(address, value):
                self.refresh_banks()
            elif self.wram_writable:
                if self.wram_fast:
                    cart.prg_ram[address & 0x1FFF] = value
                elif mapper.prg_ram_writable():
                    cart.prg_ram[mapper.prg_ram_index(address) % len(cart.prg_ram)] = value
        else:
            mapper.cpu_write(address, value)
            self.refresh_banks()
        return 0

    def write(self, address: int, value: int) -> None:
        address &= 0xFFFF
        value &= 0xFF
        if address < 0x2000:
            self.ram[address & 0x7FF] = value
        else:
            self.cpu.cycles += self.write_io(address, value, self.cpu.cycles)

    def _oam_dma(self, page: int) -> None:
        base = page << 8
        if base < 0x2000:
            start = base & 0x7FF
            data = bytes(self.ram[start:start + 256])
        elif base >= 0x8000:
            start = base - 0x8000
            data = bytes(self.prg32[start:start + 256])
        else:
            data = bytes(self.read((base + k) & 0xFFFF) for k in range(256))
        ppu = self.ppu
        offset = ppu.oam_address
        if offset:
            data = data[256 - offset:] + data[:256 - offset]
        ppu.oam[:] = data
        ppu.spr_dirty = True

    # ----------------------------------------------------------- save state
    def state(self) -> dict:
        return {
            "ram": bytes(self.ram),
            "nmi_line": self.nmi_line,
            "open_bus": self.open_bus,
            "controller_shift": list(self.controller_shift),
            "controller_strobe": self.controller_strobe,
        }

    def load_state(self, st: dict) -> None:
        self.ram[:] = st["ram"]
        self.nmi_line = st["nmi_line"]
        self.open_bus = st["open_bus"]
        self.controller_shift = list(st["controller_shift"])
        self.controller_strobe = st["controller_strobe"]


# ---------------------------------------------------------------------------
# NES — frame scheduler, regions, power/reset, save states
# ---------------------------------------------------------------------------
REGIONS = {
    # name: (cpu numerator, ppu-dot denominator, total lines, vblank line, fps, cpu clock)
    "NTSC": (1, 3, 262, 241, NTSC_FPS, CPU_CLOCK),
    "PAL": (5, 16, 312, 241, 50.0070, 1_662_607),
    "Dendy": (1, 3, 312, 291, 50.0, 1_773_448),
}
RAM_INIT_MODES = ("Default", "Fill $FF", "Fill $00", "Random")


class NES:
    """A powered console: cartridge + bus + scanline scheduler."""

    STATE_VERSION = 2

    def __init__(self, cart: Cartridge, region: str = "NTSC", ram_init: str = "Default") -> None:
        self.cart = cart
        self.region = region if region in REGIONS else "NTSC"
        self.ram_init = ram_init
        clock = REGIONS[self.region][5]
        self.bus = Bus(cart, clock)
        self.frame_dot = 0
        self.lag_frame = False
        self.lag_count = 0
        self.frame_count = 0
        self.debug: Optional["DebugHooks"] = None
        self._frame_gen = None
        self.power()

    # ----------------------------------------------------------- lifecycle
    def _fill_ram(self) -> None:
        ram = self.bus.ram
        mode = self.ram_init
        if mode == "Fill $FF":
            ram[:] = b"\xff" * 0x800
        elif mode == "Fill $00":
            ram[:] = bytes(0x800)
        elif mode == "Random":
            ram[:] = os.urandom(0x800)
        else:
            # FCEUX default: alternating $00/$FF blocks of 4 bytes.
            ram[:] = (b"\x00\x00\x00\x00\xff\xff\xff\xff" * 256)

    def power(self) -> None:
        bus = self.bus
        self._fill_ram()
        bus.ppu.reset(power=True)
        bus.apu.reset()
        self.cart.mapper.reset()
        bus.nmi_line = False
        bus.refresh_banks(force=True)
        bus.refresh_ppu_banks()
        bus.cpu.select_runner()
        bus.cpu.power()
        bus.cpu.cycles = 7
        bus.apu.position = 7
        bus.apu.cpu_cycle = 7
        self.frame_dot = 0
        self.frame_count = 0
        self.lag_count = 0
        self._frame_gen = None

    def reset(self) -> None:
        bus = self.bus
        self.cart.mapper.reset()
        bus.refresh_banks(force=True)
        bus.refresh_ppu_banks()
        bus.ppu.reset()
        bus.apu.write(0x4015, 0)
        bus.apu.frame_irq = False
        bus.apu.dmc.irq = False
        bus.cpu.reset()
        bus.cpu.cycles += 7
        # restart the frame so the PPU warm-up behaves like a fresh frame
        self._frame_gen = None
        self.frame_dot = bus.cpu.cycles * 3

    # ----------------------------------------------------------- scheduler
    def run_frame(self) -> bool:
        """Emulate up to the end of the current frame.

        Returns True when the frame finished, False when a debugger
        breakpoint halted the CPU mid-frame (call again to resume).
        """
        gen = self._frame_gen
        if gen is None:
            gen = self._frame_gen = self._frame_body()
        try:
            next(gen)
        except StopIteration:
            self._frame_gen = None
            return True
        return False

    def _dbg_wait(self, target: int):
        cpu = self.bus.cpu
        while cpu.cycles < target:
            yield
            cpu._runner(cpu, target)

    def _frame_body(self):
        bus = self.bus
        cpu = bus.cpu
        ppu = bus.ppu
        apu = bus.apu
        mapper = self.cart.mapper
        runner = cpu._runner
        dbg = self.debug is not None
        num, den, total_lines, vbl_line, _fps, _clock = REGIONS[self.region]
        rnd = den - 1
        ppu.dot_num = num
        ppu.dot_den = den
        fd = self.frame_dot
        if bus.cheats:
            bus.apply_ram_cheats()
        bus.input_read = False
        ppu.frame_ready = False
        render_line = ppu.render_line
        catch_up = apu.catch_up
        if bus.banks_dirty:
            bus.refresh_ppu_banks()

        # ---- visible lines 0-239
        for y in range(240):
            ld = fd + y * 341
            if ppu.mask & 0x18:
                ppu.line_cycle = (ld * num + rnd) // den
                render_line(y, ld)
                t = ((ld + 256) * num + rnd) // den
                runner(cpu, t)
                if dbg:
                    yield from self._dbg_wait(t)
                if ppu.mask & 0x18:
                    ppu.increment_y()
                    ppu.copy_x()
                if ppu.s0_cycle >= 0:
                    ppu.settle_sprite0()
                t = ((ld + 260) * num + rnd) // den
                runner(cpu, t)
                if dbg:
                    yield from self._dbg_wait(t)
                if ppu.mask & 0x18:
                    mapper.clock_scanline()
            else:
                ppu.blank_line(y)
            t = ((ld + 341) * num + rnd) // den
            runner(cpu, t)
            if dbg:
                yield from self._dbg_wait(t)
            catch_up(cpu.cycles)
            if cpu.stall:
                cpu.cycles += cpu.stall
                cpu.stall = 0

        # ---- post-render + vertical blank
        for y in range(240, total_lines - 1):
            ld = fd + y * 341
            if y == vbl_line:
                vc = ((ld + 1) * num + rnd) // den
                ppu.vbl_cycle = vc
                ppu.vbl_suppress = False
                runner(cpu, vc)
                if dbg:
                    yield from self._dbg_wait(vc)
                if ppu.vbl_cycle >= 0:
                    ppu.status |= 0x80
                    ppu.vbl_cycle = -1
                ppu.frame_number += 1
                ppu.frame_ready = True
                if ppu.ctrl & 0x80 and not ppu.vbl_suppress:
                    bus.nmi_line = True
            t = ((ld + 341) * num + rnd) // den
            runner(cpu, t)
            if dbg:
                yield from self._dbg_wait(t)
            catch_up(cpu.cycles)
            if cpu.stall:
                cpu.cycles += cpu.stall
                cpu.stall = 0

        # ---- pre-render line
        y = total_lines - 1
        ld = fd + y * 341
        cc = ((ld + 1) * num + rnd) // den
        ppu.vbl_clear_cycle = cc
        runner(cpu, cc)
        if dbg:
            yield from self._dbg_wait(cc)
        ppu.status &= 0x1F
        ppu.vbl_clear_cycle = -1
        ppu.s0_cycle = -1
        t = ((ld + 256) * num + rnd) // den
        runner(cpu, t)
        if dbg:
            yield from self._dbg_wait(t)
        if ppu.mask & 0x18:
            ppu.increment_y()
            ppu.copy_x()
        t = ((ld + 260) * num + rnd) // den
        runner(cpu, t)
        if dbg:
            yield from self._dbg_wait(t)
        if ppu.mask & 0x18 and getattr(mapper, "clocks_prerender", True):
            mapper.clock_scanline()
        t = ((ld + 280) * num + rnd) // den
        runner(cpu, t)
        if dbg:
            yield from self._dbg_wait(t)
        if ppu.mask & 0x18:
            ppu.copy_y()
        t = ((ld + 337) * num + rnd) // den
        runner(cpu, t)
        if dbg:
            yield from self._dbg_wait(t)
        skip = 1 if (self.region == "NTSC" and ppu.odd_frame and ppu.mask & 0x18) else 0
        end = ld + 341 - skip
        t = (end * num + rnd) // den
        runner(cpu, t)
        if dbg:
            yield from self._dbg_wait(t)
        catch_up(cpu.cycles)
        if cpu.stall:
            cpu.cycles += cpu.stall
            cpu.stall = 0
        ppu.odd_frame = not ppu.odd_frame
        self.frame_dot = end
        self.frame_count += 1
        self.lag_frame = not bus.input_read
        if self.lag_frame:
            self.lag_count += 1
        if not ppu.frame_ready:
            ppu.frame_ready = True

    # ----------------------------------------------------------- debugging
    def set_debug(self, hooks: Optional["DebugHooks"]) -> None:
        self.debug = hooks
        cpu = self.bus.cpu
        cpu.select_runner()
        if hooks is not None:
            base = cpu._runner
            nes = self

            def debug_runner(cpu_obj, target, _base=base):
                h = nes.debug
                while cpu_obj.cycles < target:
                    if h is None:
                        _base(cpu_obj, target)
                        return
                    if h.halted:
                        return
                    pc = cpu_obj.pc
                    if h.breakpoints and pc in h.breakpoints and not h.skip_once:
                        h.halted = True
                        if h.on_break:
                            h.on_break(pc)
                        return
                    h.skip_once = False
                    if h.trace is not None:
                        h.trace(cpu_obj)
                    _base(cpu_obj, cpu_obj.cycles + 1)

            cpu._runner = debug_runner
        # a frame generator started with the other runner must restart cleanly
        if self._frame_gen is not None:
            self._finish_frame_fast()

    def _finish_frame_fast(self) -> None:
        gen = self._frame_gen
        self._frame_gen = None
        hooks = self.debug
        if hooks is not None:
            hooks.halted = False
        try:
            while True:
                next(gen)
                if hooks is not None:
                    hooks.halted = False
                    hooks.skip_once = True
        except StopIteration:
            pass

    def step_instruction(self) -> None:
        cpu = self.bus.cpu
        base = _CPU_RUN_MCLK if self.cart.mapper.needs_cpu_clock else _CPU_RUN_FAST
        base(cpu, cpu.cycles + 1)
        if cpu.stall:
            cpu.cycles += cpu.stall
            cpu.stall = 0

    @property
    def fps(self) -> float:
        return REGIONS[self.region][4]

    def set_region(self, region: str) -> None:
        if region not in REGIONS:
            return
        self.region = region
        clock = REGIONS[region][5]
        self.bus.cpu_clock = clock
        self.bus.apu.clock = clock

    # --------------------------------------------------------- save states
    def save_state(self) -> bytes:
        if self._frame_gen is not None:
            self._finish_frame_fast()
        mapper = self.cart.mapper
        mapper_state = {k: copy.deepcopy(v) for k, v in mapper.__dict__.items() if k != "cart"}
        st = {
            "version": self.STATE_VERSION,
            "app": APP_TITLE,
            "mapper_id": self.cart.mapper_id,
            "prg_crc": zlib.crc32(self.cart.prg),
            "region": self.region,
            "frame_dot": self.frame_dot,
            "frame_count": self.frame_count,
            "cpu": self.bus.cpu.state(),
            "ppu": self.bus.ppu.state(),
            "apu": self.bus.apu.state(),
            "bus": self.bus.state(),
            "mapper": mapper_state,
            "prg_ram": bytes(self.cart.prg_ram),
            "chr_ram": bytes(self.cart.chr) if self.cart.chr_is_ram or self.cart.mapper_id == 119 else None,
        }
        return zlib.compress(pickle.dumps(st, protocol=4), 6)

    def load_state(self, blob: bytes) -> None:
        st = pickle.loads(zlib.decompress(blob))
        if st.get("version") != self.STATE_VERSION:
            raise ValueError("Save state was made by a different emulator version.")
        if st.get("prg_crc") != zlib.crc32(self.cart.prg):
            raise ValueError("Save state belongs to a different ROM.")
        mapper = self.cart.mapper
        for k, v in st["mapper"].items():
            setattr(mapper, k, copy.deepcopy(v))
        self.cart.prg_ram[:] = st["prg_ram"]
        if st.get("chr_ram") is not None and len(st["chr_ram"]) == len(self.cart.chr):
            self.cart.chr[:] = st["chr_ram"]
        self.region = st.get("region", self.region)
        self.frame_dot = st["frame_dot"]
        self.frame_count = st["frame_count"]
        self.bus.load_state(st["bus"])
        self.bus.ppu.load_state(st["ppu"])
        self.bus.apu.load_state(st["apu"])
        self.bus.cpu.load_state(st["cpu"])
        self.bus.refresh_banks(force=True)
        self.bus.refresh_ppu_banks()
        self._frame_gen = None
        self.set_debug(self.debug)


class DebugHooks:
    """Breakpoints / trace hook shared by the Debugger and Trace Logger."""

    def __init__(self) -> None:
        self.breakpoints: set = set()
        self.halted = False
        self.skip_once = False
        self.trace: Optional[Callable] = None
        self.on_break: Optional[Callable] = None


# ---------------------------------------------------------------------------
# Game Genie
# ---------------------------------------------------------------------------
_GG_LETTERS = "APZLGITYEOXUKSVN"


def game_genie_decode(code: str) -> tuple[int, int, Optional[int]]:
    """Decode a 6- or 8-letter Game Genie code -> (address, value, compare)."""
    code = code.strip().upper()
    if len(code) not in (6, 8) or any(ch not in _GG_LETTERS for ch in code):
        raise ValueError("Game Genie codes are 6 or 8 letters from APZLGITYEOXUKSVN.")
    n = [_GG_LETTERS.index(ch) for ch in code]
    address = 0x8000 + (
        ((n[3] & 7) << 12) | ((n[5] & 7) << 8) | ((n[4] & 8) << 8)
        | ((n[2] & 7) << 4) | ((n[1] & 8) << 4) | (n[4] & 7) | (n[3] & 8)
    )
    if len(code) == 6:
        value = ((n[1] & 7) << 4) | ((n[0] & 8) << 4) | (n[0] & 7) | (n[5] & 8)
        return address, value, None
    value = ((n[1] & 7) << 4) | ((n[0] & 8) << 4) | (n[0] & 7) | (n[7] & 8)
    compare = ((n[7] & 7) << 4) | ((n[6] & 8) << 4) | (n[6] & 7) | (n[5] & 8)
    return address, value, compare


def game_genie_encode(address: int, value: int, compare: Optional[int] = None) -> str:
    """Encode an address/value(/compare) as a Game Genie code."""
    address &= 0x7FFF
    n = [0] * (8 if compare is not None else 6)
    n[0] = (value & 7) | ((value >> 4) & 8)
    n[1] = ((value >> 4) & 7) | ((address >> 4) & 8)
    n[2] = (address >> 4) & 7
    n[3] = ((address >> 12) & 7) | (address & 8)
    n[4] = (address & 7) | ((address >> 8) & 8)
    n[5] = (address >> 8) & 7
    if compare is None:
        n[5] |= value & 8
    else:
        n[2] |= 8
        n[5] |= compare & 8
        n[6] = (compare & 7) | ((compare >> 4) & 8)
        n[7] = ((compare >> 4) & 7) | (value & 8)
    return "".join(_GG_LETTERS[x] for x in n)


def parse_cheat(text: str) -> tuple[int, int, Optional[int]]:
    """Accept 'AAAA:VV', 'AAAA:VV:CC', 'AAAA?CC:VV' or a Game Genie code."""
    text = text.strip()
    if ":" not in text and "?" not in text:
        return game_genie_decode(text)
    compare = None
    if "?" in text:
        addr_part, rest = text.split("?", 1)
        cmp_part, val_part = rest.split(":", 1)
        compare = int(cmp_part, 16)
    else:
        parts = text.split(":")
        addr_part, val_part = parts[0], parts[1]
        if len(parts) > 2:
            compare = int(parts[2], 16)
    return int(addr_part, 16) & 0xFFFF, int(val_part, 16) & 0xFF, compare

def disassemble(bus: Bus, start: int, lines: int = 12, *, fceux_names: bool = True) -> list[str]:
    output: list[str] = []
    pc = start & 0xFFFF
    for _ in range(lines):
        opcode = bus.peek(pc)
        ins = OPCODES[opcode]
        length = MODE_LENGTH[ins.mode]
        operands = [bus.peek((pc + i) & 0xFFFF) for i in range(1, length)]
        raw = " ".join(f"{b:02X}" for b in [opcode, *operands]).ljust(8)
        if ins.mode == "IMM":
            operand = f"#$%02X" % operands[0]
        elif ins.mode == "ZP":
            operand = f"$%02X" % operands[0]
        elif ins.mode == "ZPX":
            operand = f"$%02X,X" % operands[0]
        elif ins.mode == "ZPY":
            operand = f"$%02X,Y" % operands[0]
        elif ins.mode == "IZX":
            operand = f"($%02X,X)" % operands[0]
        elif ins.mode == "IZY":
            operand = f"($%02X),Y" % operands[0]
        elif ins.mode in ("ABS", "ABX", "ABY", "IND"):
            target = operands[0] | (operands[1] << 8)
            suffix = {"ABS": "", "ABX": ",X", "ABY": ",Y", "IND": ")"}[ins.mode]
            operand = f"${target:04X}{suffix}" if ins.mode != "IND" else f"(${target:04X})"
        elif ins.mode == "REL":
            offset = operands[0] - 0x100 if operands[0] & 0x80 else operands[0]
            operand = f"${(pc + 2 + offset) & 0xFFFF:04X}"
        elif ins.mode == "ACC":
            operand = "A"
        else:
            operand = ""
        mnemonic = fceux_name(opcode) if fceux_names else ins.name
        output.append(f"{pc:04X}  {raw} {mnemonic} {operand}".rstrip())
        pc = (pc + length) & 0xFFFF
    return output


def list_all_opcodes() -> list[str]:
    """Human-readable dump of the full FCEUX-aligned 256-opcode map."""
    lines: list[str] = []
    for opcode, ins in enumerate(OPCODES):
        aliases = FCEUX_ALIASES.get(ins.name, ())
        alias_txt = f"  aliases={','.join(aliases)}" if aliases else ""
        lines.append(
            f"${opcode:02X}  {fceux_name(opcode):<4}  {ins.mode:<3}  "
            f"{ins.cycles}c  ({ins.name}){alias_txt}"
        )
    return lines


def run_prompt(rom: Optional[str] = None) -> int:
    """Interactive FCEUX-inspired debugger prompt (no GUI required)."""
    nes: Optional[NES] = None
    if rom:
        try:
            nes = NES(Cartridge.from_file(rom))
            print(f"loaded {rom}")
        except Exception as exc:
            print(f"load failed: {exc}")
    print(f"{APP_TITLE}")
    print("type 'help' for prompts, 'opcodes' for the full FCEUX opcode map")
    while True:
        try:
            line = input("acnesemu> ").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            return 0
        if not line:
            continue
        parts = line.split()
        cmd = parts[0].lower()
        args = parts[1:]

        if cmd in ("q", "quit", "exit"):
            return 0
        if cmd in ("help", "?"):
            print(PROMPT_HELP)
            continue
        if cmd in ("opcodes", "op", "ops"):
            for row in list_all_opcodes():
                print(row)
            print(f"— {len(OPCODES)}/256 opcodes, cycles match FCEUX CycTable")
            continue
        if cmd == "load":
            if not args:
                print("usage: load <path.nes>")
                continue
            try:
                nes = NES(Cartridge.from_file(args[0]))
                print(f"loaded {args[0]}")
            except Exception as exc:
                print(f"load failed: {exc}")
            continue
        if cmd in ("run", "gui"):
            path = args[0] if args else (rom if rom else None)
            if path is None and nes is None:
                print("load a ROM first (load <path.nes>)")
                continue
            if path:
                root = tk.Tk()
                EmulatorGUI(root, path)
                root.mainloop()
            else:
                print("GUI needs a ROM path; use: run <path.nes>")
            continue
        if nes is None:
            print("no cartridge — use: load <path.nes>")
            continue

        cpu = nes.bus.cpu
        if cmd in ("r", "regs"):
            flags = "".join(
                name if cpu.p & bit else name.lower()
                for name, bit in (
                    ("N", N_FLAG), ("V", V_FLAG), ("U", U_FLAG), ("B", B_FLAG),
                    ("D", D_FLAG), ("I", I_FLAG), ("Z", Z_FLAG), ("C", C_FLAG),
                )
            )
            print(
                f"A={cpu.a:02X} X={cpu.x:02X} Y={cpu.y:02X} SP={cpu.sp:02X} "
                f"PC={cpu.pc:04X} P={cpu.p:02X}[{flags}] cy={cpu.total_cycles}"
            )
            continue
        if cmd in ("s", "step"):
            count = int(args[0], 0) if args else 1
            for _ in range(max(1, count)):
                cpu.step()
            print("\n".join(disassemble(nes.bus, cpu.pc, 8)))
            continue
        if cmd in ("f", "frame"):
            count = int(args[0], 0) if args else 1
            for _ in range(max(1, count)):
                nes.run_frame()
            print(f"frame={nes.bus.ppu.frame_number} PC=${cpu.pc:04X}")
            continue
        if cmd == "reset":
            nes.reset()
            print(f"reset PC=${cpu.pc:04X}")
            continue
        if cmd in ("d", "dis", "disasm"):
            addr = int(args[0], 0) if args else cpu.pc
            n = int(args[1], 0) if len(args) > 1 else 12
            print("\n".join(disassemble(nes.bus, addr, n)))
            continue
        if cmd == "peek":
            if not args:
                print("usage: peek <addr>")
                continue
            addr = int(args[0], 0) & 0xFFFF
            print(f"${addr:04X} = ${nes.bus.peek(addr):02X}")
            continue
        if cmd == "poke":
            if len(args) < 2:
                print("usage: poke <addr> <val>")
                continue
            addr = int(args[0], 0) & 0xFFFF
            val = int(args[1], 0) & 0xFF
            nes.bus.write(addr, val)
            print(f"${addr:04X} := ${val:02X}")
            continue
        if cmd in ("m", "mem", "dump"):
            if not args:
                print("usage: mem <addr> [len]")
                continue
            addr = int(args[0], 0) & 0xFFFF
            length = int(args[1], 0) if len(args) > 1 else 16
            length = max(1, min(length, 256))
            bytes_ = [nes.bus.peek((addr + i) & 0xFFFF) for i in range(length)]
            for i in range(0, length, 16):
                chunk = bytes_[i:i + 16]
                hex_part = " ".join(f"{b:02X}" for b in chunk)
                print(f"{(addr + i) & 0xFFFF:04X}: {hex_part}")
            continue
        print(f"unknown prompt '{cmd}' — type help")
    return 0



# ---------------------------------------------------------------------------
# Front-end support: audio sink, PNG / WAV writers, input + hotkey defaults
# ---------------------------------------------------------------------------
def png_bytes(width: int, height: int, rgb: bytes) -> bytes:
    """Encode packed 8-bit RGB as a PNG (no external libraries)."""
    stride = width * 3
    raw = b"".join(b"\x00" + rgb[y * stride:(y + 1) * stride] for y in range(height))

    def chunk(tag: bytes, data: bytes) -> bytes:
        return (struct.pack(">I", len(data)) + tag + data
                + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF))

    return (b"\x89PNG\r\n\x1a\n"
            + chunk(b"IHDR", struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(raw, 6))
            + chunk(b"IEND", b""))


def ppm_bytes(width: int, height: int, rgb: bytes) -> bytes:
    return b"P6\n%d %d\n255\n" % (width, height) + bytes(rgb)


class WavWriter:
    """Streams 16-bit mono PCM into a .wav file (header patched on close)."""

    def __init__(self, path: str, rate: int) -> None:
        self.path = path
        self.rate = rate
        self.fh = open(path, "wb")
        self.frames = 0
        self.fh.write(self._header(0))

    def _header(self, nbytes: int) -> bytes:
        return (b"RIFF" + struct.pack("<I", 36 + nbytes) + b"WAVEfmt "
                + struct.pack("<IHHIIHH", 16, 1, 1, self.rate, self.rate * 2, 2, 16)
                + b"data" + struct.pack("<I", nbytes))

    def write(self, pcm: bytes) -> None:
        if self.fh:
            self.fh.write(pcm)
            self.frames += len(pcm) // 2

    def close(self) -> None:
        if self.fh:
            self.fh.seek(0)
            self.fh.write(self._header(self.frames * 2))
            self.fh.close()
            self.fh = None


class AudioOutput:
    """Real-time PCM sink: sounddevice (callback ring buffer) -> pygame-ce -> silent.

    `level_ms()` reports how much audio is queued so the frame pacer can
    keep emulation locked to the sound card (no drift, no crackle).
    """

    MAX_MS = 180

    def __init__(self, rate: int = 44_100) -> None:
        self.rate = rate
        self.backend = "none"
        self.available = False
        self.muted = False
        self.error = ""
        self._buf = bytearray()
        self._lock = threading.Lock()
        self._stream = None
        self._pygame = None
        self._channel = None
        self._queued_until = 0.0
        self._open()

    def _open(self) -> None:
        try:
            import sounddevice as sd  # type: ignore[import-not-found]

            self._stream = sd.RawOutputStream(
                samplerate=self.rate, channels=1, dtype="int16",
                blocksize=512, latency="low", callback=self._callback)
            self._stream.start()
            self.backend = "sounddevice"
            self.available = True
            return
        except Exception as exc:  # noqa: BLE001 - any backend failure falls through
            self.error = f"sounddevice: {exc}"
            self._stream = None
        try:
            os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")
            import pygame  # type: ignore[import-not-found]

            try:
                pygame.mixer.init(frequency=self.rate, size=-16, channels=1,
                                  buffer=512, allowedchanges=0)
            except TypeError:
                pygame.mixer.init(frequency=self.rate, size=-16, channels=1, buffer=512)
            self._pygame = pygame
            self._channel = pygame.mixer.Channel(0)
            self.backend = "pygame"
            self.available = True
        except Exception as exc:  # noqa: BLE001
            self.error += f"; pygame: {exc}"
            self._pygame = None

    # -- sounddevice callback thread
    def _callback(self, outdata, frames, _time, _status) -> None:
        need = frames * 2
        with self._lock:
            take = bytes(self._buf[:need])
            del self._buf[:need]
        if len(take) < need:
            take += bytes(need - len(take))
        outdata[:] = take

    def submit(self, pcm: bytes) -> None:
        if not pcm or not self.available or self.muted:
            return
        limit = self.rate * 2 * self.MAX_MS // 1000
        if self._stream is not None:
            with self._lock:
                self._buf += pcm
                if len(self._buf) > limit:
                    del self._buf[:len(self._buf) - limit]
            return
        if self._pygame is not None:
            self._buf += pcm
            if len(self._buf) > limit:
                del self._buf[:len(self._buf) - limit]
            chan = self._channel
            if chan.get_queue() is None and len(self._buf) >= self.rate // 30 * 2:
                sound = self._pygame.mixer.Sound(buffer=bytes(self._buf))
                seconds = len(self._buf) / (self.rate * 2)
                self._buf = bytearray()
                now = time.perf_counter()
                if not chan.get_busy():
                    chan.play(sound)
                    self._queued_until = now + seconds
                else:
                    chan.queue(sound)
                    self._queued_until = max(self._queued_until, now) + seconds

    def level_ms(self) -> float:
        if not self.available or self.muted:
            return -1.0
        if self._stream is not None:
            return len(self._buf) * 500.0 / self.rate
        pending = len(self._buf) * 500.0 / self.rate
        return pending + max(0.0, self._queued_until - time.perf_counter()) * 1000.0

    def clear(self) -> None:
        with self._lock:
            self._buf = bytearray()
        if self._channel is not None:
            try:
                self._channel.stop()
            except Exception:  # noqa: BLE001
                pass
        self._queued_until = 0.0

    def close(self) -> None:
        if self._stream is not None:
            try:
                self._stream.stop()
                self._stream.close()
            except Exception:  # noqa: BLE001
                pass
        if self._pygame is not None:
            try:
                self._pygame.mixer.quit()
            except Exception:  # noqa: BLE001
                pass


# NES controller bit order used by the bus: A B Select Start Up Down Left Right
NES_BUTTONS = ("A", "B", "Select", "Start", "Up", "Down", "Left", "Right")
TURBO_BUTTONS = ("Turbo A", "Turbo B")

# FCEUX default keyboard layout for gamepad 1 (port 2 unbound).
DEFAULT_PAD_KEYS = [
    {"A": "f", "B": "d", "Select": "s", "Start": "Return",
     "Up": "Up", "Down": "Down", "Left": "Left", "Right": "Right",
     "Turbo A": "", "Turbo B": ""},
    {name: "" for name in NES_BUTTONS + TURBO_BUTTONS},
]

# FCEUX (Qt) default hotkeys.  Format: "Ctrl+Shift+Alt+key" with Tk keysyms.
DEFAULT_HOTKEYS = collections.OrderedDict([
    ("Open ROM", "Ctrl+o"),
    ("Close ROM", "Ctrl+c"),
    ("Screenshot", "F12"),
    ("Soft Reset", "Ctrl+r"),
    ("Hard Reset", "Ctrl+Shift+r"),
    ("Power", ""),
    ("Pause", "Pause"),
    ("Quit", "Ctrl+q"),
    ("Toggle Input Display", "comma"),
    ("Toggle Lag Counter Display", "slash"),
    ("Toggle Frame Display", "period"),
    ("Hide Menu", "Alt+slash"),
    ("Fullscreen", "Alt+Return"),
    ("Save State", "i"),
    ("Load State", "p"),
    ("Save State Slot 0", "Shift+F10"),
    ("Save State Slot 1", "Shift+F1"),
    ("Save State Slot 2", "Shift+F2"),
    ("Save State Slot 3", "Shift+F3"),
    ("Save State Slot 4", "Shift+F4"),
    ("Save State Slot 5", "Shift+F5"),
    ("Save State Slot 6", "Shift+F6"),
    ("Save State Slot 7", "Shift+F7"),
    ("Save State Slot 8", "Shift+F8"),
    ("Save State Slot 9", "Shift+F9"),
    ("Load State Slot 0", "F10"),
    ("Load State Slot 1", "F1"),
    ("Load State Slot 2", "F2"),
    ("Load State Slot 3", "F3"),
    ("Load State Slot 4", "F4"),
    ("Load State Slot 5", "F5"),
    ("Load State Slot 6", "F6"),
    ("Load State Slot 7", "F7"),
    ("Load State Slot 8", "F8"),
    ("Load State Slot 9", "F9"),
] + [(f"Select State Slot {n}", str(n)) for n in range(10)] + [
    ("Decrease Speed", "minus"),
    ("Increase Speed", "equal"),
    ("Frame Advance", "backslash"),
    ("Turbo", "Tab"),
    ("Toggle Movie Read-Only", "q"),
    ("Mute", ""),
])

SPEED_STEPS = (6.25, 12.5, 25.0, 50.0, 75.0, 100.0, 125.0, 150.0, 200.0, 300.0,
               400.0, 800.0, 1600.0)

AUTOFIRE_PATTERNS = [(on, off) for on in range(1, 6) for off in range(1, 7 - on)]


# ---------------------------------------------------------------------------
# Tool / config windows (FCEUX-style)
# ---------------------------------------------------------------------------
MONO_FONT = ("Courier New", 10) if sys.platform.startswith("win") else (
    ("Menlo", 11) if sys.platform == "darwin" else ("DejaVu Sans Mono", 9))


class ToolWindow:
    """Base class: one Toplevel per tool, refreshed by the main loop."""

    title = "Tool"
    key = "tool"
    refresh_every = 6        # frames between refresh() calls while running

    def __init__(self, app: "EmulatorGUI") -> None:
        self.app = app
        self.top = tk.Toplevel(app.root)
        self.top.title(self.title)
        self.top.protocol("WM_DELETE_WINDOW", self.close)
        self.top.bind("<Escape>", lambda _e: self.close())
        self.frame = ttk.Frame(self.top, padding=8)
        self.frame.pack(fill=tk.BOTH, expand=True)
        self.build()
        self.refresh()

    # subclasses override
    def build(self) -> None:
        pass

    def refresh(self) -> None:
        pass

    @property
    def nes(self) -> Optional["NES"]:
        return self.app.nes

    def alive(self) -> bool:
        try:
            return bool(self.top.winfo_exists())
        except tk.TclError:
            return False

    def close(self) -> None:
        self.app.tools.pop(self.key, None)
        self.on_close()
        try:
            self.top.destroy()
        except tk.TclError:
            pass

    def on_close(self) -> None:
        pass

    def lift(self) -> None:
        try:
            self.top.deiconify()
            self.top.lift()
            self.top.focus_force()
        except tk.TclError:
            pass

    # small helpers
    def button(self, parent, text, command, **kw) -> ttk.Button:
        return ttk.Button(parent, text=text, command=command, **kw)


def _parse_hex(text: str, default: Optional[int] = None) -> Optional[int]:
    text = text.strip().lstrip("$").replace("0x", "").replace("0X", "")
    if not text:
        return default
    try:
        return int(text, 16)
    except ValueError:
        return default


def chr_reader(nes: "NES"):
    """Fast side-effect free CHR read function for viewers."""
    bus = nes.bus
    cart = nes.cart
    if bus.banks_dirty:
        bus.refresh_ppu_banks()
    if bus.chr_slow or getattr(cart.mapper, "chr_latch", False):
        mapper = cart.mapper
        saved = copy.deepcopy({k: v for k, v in mapper.__dict__.items() if k != "cart"})

        def read(addr: int) -> int:
            value = cart.ppu_read(addr)
            return value

        def restore() -> None:
            mapper.__dict__.update(saved)
        return read, restore
    chr_ = cart.chr
    offs = list(bus.chr_off)

    def read(addr: int) -> int:
        return chr_[offs[addr >> 10] + (addr & 0x3FF)]
    return read, (lambda: None)


def nes_rgb(colour: int) -> tuple:
    return _DISPLAY_PALETTE[colour & 0x3F]


# ------------------------------------------------------------------ Debugger
class DebuggerWindow(ToolWindow):
    title = "Debugger"
    key = "debugger"
    refresh_every = 10

    def build(self) -> None:
        f = self.frame
        left = ttk.Frame(f)
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        right = ttk.Frame(f)
        right.pack(side=tk.LEFT, fill=tk.Y, padx=(8, 0))
        self.dis = tk.Text(left, width=46, height=30, font=MONO_FONT, wrap=tk.NONE)
        self.dis.pack(fill=tk.BOTH, expand=True)
        self.dis.tag_configure("pc", background="#c8d8ff")
        self.dis.tag_configure("bp", foreground="#c00000")
        bar = ttk.Frame(left)
        bar.pack(fill=tk.X, pady=(6, 0))
        for text, cmd in (("Run", self.run), ("Step Into", self.step_into),
                          ("Step Over", self.step_over), ("Step Out", self.step_out),
                          ("Run Line", self.run_line), ("Break", self.brk)):
            self.button(bar, text, cmd).pack(side=tk.LEFT, padx=1)
        reg = ttk.LabelFrame(right, text="Registers", padding=6)
        reg.pack(fill=tk.X)
        self.reg_var = tk.StringVar()
        ttk.Label(reg, textvariable=self.reg_var, font=MONO_FONT, justify=tk.LEFT).pack(anchor=tk.W)
        ppu = ttk.LabelFrame(right, text="PPU / Timing", padding=6)
        ppu.pack(fill=tk.X, pady=6)
        self.ppu_var = tk.StringVar()
        ttk.Label(ppu, textvariable=self.ppu_var, font=MONO_FONT, justify=tk.LEFT).pack(anchor=tk.W)
        bpf = ttk.LabelFrame(right, text="Breakpoints (PC)", padding=6)
        bpf.pack(fill=tk.BOTH, expand=True)
        self.bp_list = tk.Listbox(bpf, height=8, font=MONO_FONT)
        self.bp_list.pack(fill=tk.BOTH, expand=True)
        row = ttk.Frame(bpf)
        row.pack(fill=tk.X, pady=(4, 0))
        self.bp_entry = ttk.Entry(row, width=8)
        self.bp_entry.pack(side=tk.LEFT)
        self.bp_entry.bind("<Return>", lambda _e: self.add_bp())
        self.button(row, "Add", self.add_bp).pack(side=tk.LEFT, padx=2)
        self.button(row, "Delete", self.del_bp).pack(side=tk.LEFT)
        seek = ttk.Frame(right)
        seek.pack(fill=tk.X, pady=(6, 0))
        ttk.Label(seek, text="Seek To:").pack(side=tk.LEFT)
        self.seek_entry = ttk.Entry(seek, width=8)
        self.seek_entry.pack(side=tk.LEFT, padx=2)
        self.button(seek, "Go", self.refresh).pack(side=tk.LEFT)
        self.button(seek, "Seek PC", self.seek_pc).pack(side=tk.LEFT, padx=2)

    def hooks(self) -> "DebugHooks":
        return self.app.ensure_debug_hooks()

    def add_bp(self) -> None:
        addr = _parse_hex(self.bp_entry.get())
        if addr is None:
            return
        self.hooks().breakpoints.add(addr & 0xFFFF)
        self.bp_entry.delete(0, tk.END)
        self.refresh()

    def del_bp(self) -> None:
        sel = self.bp_list.curselection()
        if not sel:
            return
        addr = int(self.bp_list.get(sel[0]).strip("$"), 16)
        self.hooks().breakpoints.discard(addr)
        self.app.maybe_release_debug_hooks()
        self.refresh()

    def seek_pc(self) -> None:
        self.seek_entry.delete(0, tk.END)
        self.refresh()

    def run(self) -> None:
        self.app.debug_continue()

    def brk(self) -> None:
        self.app.debug_break()

    def step_into(self) -> None:
        self.app.debug_step()

    def step_over(self) -> None:
        nes = self.nes
        if not nes:
            return
        pc = nes.bus.cpu.pc
        if nes.bus.peek(pc) == 0x20:          # JSR: run until the return address
            self.app.debug_run_to((pc + 3) & 0xFFFF)
        else:
            self.app.debug_step()

    def step_out(self) -> None:
        nes = self.nes
        if not nes:
            return
        cpu = nes.bus.cpu
        sp = cpu.sp
        lo = nes.bus.ram[0x100 | ((sp + 1) & 0xFF)]
        hi = nes.bus.ram[0x100 | ((sp + 2) & 0xFF)]
        self.app.debug_run_to(((lo | (hi << 8)) + 1) & 0xFFFF)

    def run_line(self) -> None:
        self.app.frame_advance()

    def refresh(self) -> None:
        nes = self.nes
        hooks = self.app.debug_hooks
        self.bp_list.delete(0, tk.END)
        if hooks:
            for addr in sorted(hooks.breakpoints):
                self.bp_list.insert(tk.END, f"${addr:04X}")
        if not nes:
            self.reg_var.set("No game loaded")
            return
        cpu = nes.bus.cpu
        ppu = nes.bus.ppu
        flags = "".join(ch if cpu.p & bit else "-" for ch, bit in zip(
            "NVUBDIZC", (0x80, 0x40, 0x20, 0x10, 8, 4, 2, 1)))
        self.reg_var.set(
            f"PC: ${cpu.pc:04X}   A: ${cpu.a:02X}\n"
            f"X:  ${cpu.x:02X}     Y: ${cpu.y:02X}\n"
            f"SP: ${cpu.sp:02X}     P: ${cpu.p:02X}\n"
            f"{flags}\n"
            f"CPU cycles: {cpu.cycles}")
        self.ppu_var.set(
            f"Frame:   {nes.frame_count}\n"
            f"Lag:     {nes.lag_count}\n"
            f"PPUCTRL: ${ppu.ctrl:02X}\n"
            f"PPUMASK: ${ppu.mask:02X}\n"
            f"STATUS:  ${ppu.status:02X}\n"
            f"V/T:     ${ppu.address:04X}/${ppu.temp_address:04X}\n"
            f"Fine X:  {ppu.fine_x}\n"
            f"Mapper:  {nes.cart.mapper_id}  ({nes.cart.mapper.mirror_mode()})\n"
            f"{'HALTED' if hooks and hooks.halted else 'running'}")
        start = _parse_hex(self.seek_entry.get(), cpu.pc)
        lines = disassemble(nes.bus, start, 30)
        self.dis.configure(state=tk.NORMAL)
        self.dis.delete("1.0", tk.END)
        for i, line in enumerate(lines):
            addr = int(line[:4], 16)
            mark = ">" if addr == cpu.pc else " "
            bp = "*" if hooks and addr in hooks.breakpoints else " "
            tag = ("pc",) if addr == cpu.pc else (("bp",) if bp == "*" else ())
            self.dis.insert(tk.END, f"{bp}{mark}{line}\n", tag)
        self.dis.configure(state=tk.DISABLED)


# ---------------------------------------------------------------- Hex editor
class HexEditorWindow(ToolWindow):
    title = "Hex Editor"
    key = "hex"
    refresh_every = 8
    SOURCES = ("NES Memory", "PPU Memory", "OAM Memory", "ROM File")

    def build(self) -> None:
        f = self.frame
        top = ttk.Frame(f)
        top.pack(fill=tk.X)
        self.source = tk.StringVar(value=self.SOURCES[0])
        ttk.Combobox(top, textvariable=self.source, values=self.SOURCES, state="readonly",
                     width=12).pack(side=tk.LEFT)
        ttk.Label(top, text="  Address:").pack(side=tk.LEFT)
        self.addr = ttk.Entry(top, width=8)
        self.addr.insert(0, "0000")
        self.addr.pack(side=tk.LEFT)
        self.addr.bind("<Return>", lambda _e: self.refresh())
        self.button(top, "Go", self.refresh).pack(side=tk.LEFT, padx=2)
        self.button(top, "<<", lambda: self.page(-0x100)).pack(side=tk.LEFT)
        self.button(top, ">>", lambda: self.page(0x100)).pack(side=tk.LEFT)
        self.text = tk.Text(f, width=76, height=17, font=MONO_FONT, wrap=tk.NONE)
        self.text.pack(fill=tk.BOTH, expand=True, pady=6)
        poke = ttk.Frame(f)
        poke.pack(fill=tk.X)
        ttk.Label(poke, text="Write  address:").pack(side=tk.LEFT)
        self.poke_addr = ttk.Entry(poke, width=8)
        self.poke_addr.pack(side=tk.LEFT)
        ttk.Label(poke, text=" value:").pack(side=tk.LEFT)
        self.poke_val = ttk.Entry(poke, width=4)
        self.poke_val.pack(side=tk.LEFT)
        self.poke_val.bind("<Return>", lambda _e: self.poke())
        self.button(poke, "Write", self.poke).pack(side=tk.LEFT, padx=4)
        self.source.trace_add("write", lambda *_a: self.refresh())

    def page(self, delta: int) -> None:
        base = (_parse_hex(self.addr.get(), 0) + delta) & self.limit()
        self.addr.delete(0, tk.END)
        self.addr.insert(0, f"{base:04X}")
        self.refresh()

    def limit(self) -> int:
        src = self.source.get()
        if src == "PPU Memory":
            return 0x3FFF
        if src == "OAM Memory":
            return 0xFF
        if src == "ROM File" and self.nes:
            return len(self.nes.cart.prg) + len(self.nes.cart.chr) - 1
        return 0xFFFF

    def read(self, addr: int) -> int:
        nes = self.nes
        src = self.source.get()
        if src == "PPU Memory":
            ppu = nes.bus.ppu
            if addr < 0x2000:
                read, restore = chr_reader(nes)
                value = read(addr)
                restore()
                return value
            if addr < 0x3F00:
                return ppu.vram[nes.bus.nt_map[(addr >> 10) & 3] + (addr & 0x3FF)]
            return ppu.palette[_palette_mirror(addr)]
        if src == "OAM Memory":
            return nes.bus.ppu.oam[addr & 0xFF]
        if src == "ROM File":
            prg = nes.cart.prg
            return prg[addr] if addr < len(prg) else nes.cart.chr[addr - len(prg)]
        return nes.bus.peek(addr)

    def poke(self) -> None:
        nes = self.nes
        addr = _parse_hex(self.poke_addr.get())
        val = _parse_hex(self.poke_val.get())
        if not nes or addr is None or val is None:
            return
        src = self.source.get()
        val &= 0xFF
        if src == "PPU Memory":
            nes.bus.ppu.memory_write(addr, val)
        elif src == "OAM Memory":
            nes.bus.ppu.oam[addr & 0xFF] = val
            nes.bus.ppu.spr_dirty = True
        elif src == "ROM File":
            self.app.log("ROM File editing is read-only in this build.")
            return
        else:
            if addr < 0x2000:
                nes.bus.ram[addr & 0x7FF] = val
            elif 0x6000 <= addr < 0x8000:
                nes.cart.prg_ram[(addr - 0x6000) % len(nes.cart.prg_ram)] = val
            else:
                nes.bus.write(addr, val)
        self.refresh()

    def refresh(self) -> None:
        nes = self.nes
        self.text.configure(state=tk.NORMAL)
        self.text.delete("1.0", tk.END)
        if not nes:
            self.text.insert(tk.END, "No game loaded")
            self.text.configure(state=tk.DISABLED)
            return
        base = _parse_hex(self.addr.get(), 0) & ~0xF & self.limit()
        lim = self.limit()
        self.text.insert(tk.END, "        00 01 02 03 04 05 06 07 08 09 0A 0B 0C 0D 0E 0F\n")
        for row in range(16):
            a = base + row * 16
            if a > lim:
                break
            vals = [self.read(a + k) if a + k <= lim else 0 for k in range(16)]
            hexs = " ".join(f"{v:02X}" for v in vals)
            text = "".join(chr(v) if 32 <= v < 127 else "." for v in vals)
            self.text.insert(tk.END, f"{a:06X}  {hexs}  {text}\n")
        self.text.configure(state=tk.DISABLED)


# ---------------------------------------------------------------- PPU viewer
class PPUViewerWindow(ToolWindow):
    title = "PPU Viewer"
    key = "ppu"
    refresh_every = 10

    def build(self) -> None:
        f = self.frame
        tables = ttk.Frame(f)
        tables.pack()
        self.images = []
        for side in range(2):
            box = ttk.LabelFrame(tables, text=f"Pattern Table {side} (${side * 0x1000:04X})", padding=4)
            box.pack(side=tk.LEFT, padx=4)
            img = tk.PhotoImage(width=256, height=256)
            ttk.Label(box, image=img).pack()
            self.images.append(img)
        self.small = tk.PhotoImage(width=128, height=128)
        pal = ttk.LabelFrame(f, text="Palettes", padding=4)
        pal.pack(fill=tk.X, pady=6)
        self.pal_img = tk.PhotoImage(width=16 * 24, height=2 * 24)
        ttk.Label(pal, image=self.pal_img).pack()
        row = ttk.Frame(f)
        row.pack(fill=tk.X)
        ttk.Label(row, text="Display palette:").pack(side=tk.LEFT)
        self.palsel = tk.IntVar(value=0)
        for n in range(8):
            ttk.Radiobutton(row, text=str(n), value=n, variable=self.palsel,
                            command=self.refresh).pack(side=tk.LEFT)

    def refresh(self) -> None:
        nes = self.nes
        if not nes:
            return
        ppu = nes.bus.ppu
        read, restore = chr_reader(nes)
        p = self.palsel.get() & 7
        colours = [nes_rgb(ppu.palette[_palette_mirror(p * 4 + k)] if k else ppu.palette[0])
                   for k in range(4)]
        lut = [bytes(c) for c in colours]
        for side in range(2):
            rgb = bytearray(128 * 128 * 3)
            base = side * 0x1000
            for tile in range(256):
                tx = (tile & 15) * 8
                ty = (tile >> 4) * 8
                ta = base + tile * 16
                for r in range(8):
                    lo = read(ta + r)
                    hi = read(ta + r + 8)
                    row = PIXEL_ROW_LUT[(hi << 8) | lo]
                    o = ((ty + r) * 128 + tx) * 3
                    rgb[o:o + 24] = b"".join(lut[px] for px in row)
            self.small.tk.call(self.small, "put", ppm_bytes(128, 128, rgb), "-format", "ppm")
            img = self.images[side]
            img.tk.call(img, "copy", self.small, "-zoom", 2, 2)
        restore()
        prgb = bytearray(16 * 24 * 2 * 24 * 3)
        for idx in range(32):
            c = bytes(nes_rgb(ppu.palette[_palette_mirror(idx)]))
            cx = (idx & 15) * 24
            cy = (idx >> 4) * 24
            for yy in range(cy, cy + 24):
                o = (yy * 16 * 24 + cx) * 3
                prgb[o:o + 72] = c * 24
        self.pal_img.tk.call(self.pal_img, "put", ppm_bytes(384, 48, prgb), "-format", "ppm")


# ------------------------------------------------------------- Sprite viewer
class SpriteViewerWindow(ToolWindow):
    title = "Sprite Viewer"
    key = "sprites"
    refresh_every = 10

    def build(self) -> None:
        f = self.frame
        cols = ("#", "X", "Y", "Tile", "Attr", "Pal", "Pri", "Flip")
        self.tree = ttk.Treeview(f, columns=cols, show="headings", height=20)
        for c in cols:
            self.tree.heading(c, text=c)
            self.tree.column(c, width=48, anchor=tk.CENTER)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        side = ttk.Frame(f)
        side.pack(side=tk.LEFT, padx=8, fill=tk.Y)
        self.preview = tk.PhotoImage(width=64, height=128)
        self.small = tk.PhotoImage(width=8, height=16)
        ttk.Label(side, text="Selected sprite").pack()
        ttk.Label(side, image=self.preview).pack(pady=4)
        self.info = tk.StringVar()
        ttk.Label(side, textvariable=self.info, font=MONO_FONT, justify=tk.LEFT).pack()
        for n in range(64):
            self.tree.insert("", tk.END, iid=str(n), values=(n,) + ("",) * 7)
        self.tree.selection_set("0")
        self.tree.bind("<<TreeviewSelect>>", lambda _e: self.refresh())

    def refresh(self) -> None:
        nes = self.nes
        if not nes:
            return
        ppu = nes.bus.ppu
        oam = ppu.oam
        for n in range(64):
            y, tile, attr, x = oam[n * 4:n * 4 + 4]
            self.tree.item(str(n), values=(
                n, x, y, f"${tile:02X}", f"${attr:02X}", attr & 3,
                "back" if attr & 0x20 else "front",
                ("H" if attr & 0x40 else "") + ("V" if attr & 0x80 else "")))
        sel = self.tree.selection()
        n = int(sel[0]) if sel else 0
        y, tile, attr, x = oam[n * 4:n * 4 + 4]
        tall = bool(ppu.ctrl & 0x20)
        read, restore = chr_reader(nes)
        pal = 4 + (attr & 3)
        lut = [bytes(nes_rgb(ppu.palette[0]))] + [
            bytes(nes_rgb(ppu.palette[_palette_mirror(pal * 4 + k)])) for k in (1, 2, 3)]
        rgb = bytearray(8 * 16 * 3)
        rows = 16 if tall else 8
        for r in range(rows):
            if tall:
                base = ((tile & 1) << 12) | ((tile & 0xFE) << 4)
                addr = base + ((r & 8) << 1) + (r & 7)
            else:
                addr = (0x1000 if ppu.ctrl & 0x08 else 0) + tile * 16 + r
            row = PIXEL_ROW_LUT[(read(addr + 8) << 8) | read(addr)]
            rgb[r * 24:(r + 1) * 24] = b"".join(lut[px] for px in row)
        restore()
        self.small.tk.call(self.small, "put", ppm_bytes(8, 16, rgb), "-format", "ppm")
        self.preview.blank()
        self.preview.tk.call(self.preview, "copy", self.small, "-zoom", 8, 8)
        self.info.set(f"Sprite {n}\nX={x} Y={y}\nTile ${tile:02X}\n{'8x16' if tall else '8x8'}")


# ---------------------------------------------------------- Name table viewer
class NameTableViewerWindow(ToolWindow):
    title = "Name Table Viewer"
    key = "nametables"
    refresh_every = 15

    def build(self) -> None:
        f = self.frame
        self.canvas = tk.Canvas(f, width=512, height=480, bg="black", highlightthickness=0)
        self.canvas.pack()
        self.img = tk.PhotoImage(width=512, height=480)
        self.canvas.create_image(0, 0, anchor=tk.NW, image=self.img)
        self.rect = self.canvas.create_rectangle(0, 0, 256, 240, outline="#ff3030", width=2)
        self.show_scroll = tk.BooleanVar(value=True)
        row = ttk.Frame(f)
        row.pack(fill=tk.X, pady=4)
        ttk.Checkbutton(row, text="Show Scroll Lines", variable=self.show_scroll,
                        command=self.refresh).pack(side=tk.LEFT)
        self.info = tk.StringVar()
        ttk.Label(row, textvariable=self.info).pack(side=tk.RIGHT)

    def refresh(self) -> None:
        nes = self.nes
        if not nes:
            return
        ppu = nes.bus.ppu
        bus = nes.bus
        read, restore = chr_reader(nes)
        if ppu.pal_dirty:
            ppu._rebuild_palette()
        pal_tt = ppu._pal_tt
        pt = 0x1000 if ppu.ctrl & 0x10 else 0
        cache = ppu._row_cache
        decode = ppu._decode_row
        frame = bytearray(512 * 480)
        vram = ppu.vram
        for table in range(4):
            base = bus.nt_map[table]
            ox = (table & 1) * 256
            oy = (table >> 1) * 240
            for ty in range(30):
                attr_row = base + 0x3C0 + (ty >> 2) * 8
                ay = (ty & 2) << 1
                for fy in range(8):
                    rows = []
                    for tx in range(32):
                        tile = vram[base + ty * 32 + tx]
                        palv = (vram[attr_row + (tx >> 2)] >> (ay | (tx & 2))) & 3
                        a = pt + tile * 16 + fy
                        key = (read(a + 8) << 11) | (read(a) << 3) | palv
                        row = cache[key]
                        rows.append(row if row is not None else decode(key, False))
                    o = (oy + ty * 8 + fy) * 512 + ox
                    frame[o:o + 256] = b"".join(rows)
        restore()
        rgb = frame_to_rgb(bytes(frame.translate(pal_tt)), 0)
        self.img.tk.call(self.img, "put", ppm_bytes(512, 480, rgb), "-format", "ppm")
        sx, sy = ppu.scroll_x, ppu.scroll_y
        if self.show_scroll.get():
            self.canvas.coords(self.rect, sx % 512, sy % 480, sx % 512 + 256, sy % 480 + 240)
            self.canvas.itemconfigure(self.rect, state=tk.NORMAL)
        else:
            self.canvas.itemconfigure(self.rect, state=tk.HIDDEN)
        self.info.set(f"Mirroring: {nes.cart.mapper.mirror_mode()}   Scroll: {sx}, {sy}")


# --------------------------------------------------------------- Trace logger
class TraceLoggerWindow(ToolWindow):
    title = "Trace Logger"
    key = "trace"
    refresh_every = 20

    def build(self) -> None:
        f = self.frame
        top = ttk.Frame(f)
        top.pack(fill=tk.X)
        self.toggle_btn = self.button(top, "Start Logging", self.toggle)
        self.toggle_btn.pack(side=tk.LEFT)
        ttk.Label(top, text="  Lines to keep:").pack(side=tk.LEFT)
        self.max_lines = ttk.Spinbox(top, from_=1000, to=1000000, increment=1000, width=9)
        self.max_lines.set("20000")
        self.max_lines.pack(side=tk.LEFT)
        self.button(top, "Clear", self.clear).pack(side=tk.LEFT, padx=4)
        self.button(top, "Save to File...", self.save).pack(side=tk.LEFT)
        self.text = tk.Text(f, width=96, height=28, font=MONO_FONT, wrap=tk.NONE)
        self.text.pack(fill=tk.BOTH, expand=True, pady=6)
        self.lines: collections.deque = collections.deque(maxlen=20000)
        self.logging = False
        self._shown = 0

    def toggle(self) -> None:
        if self.logging:
            self.stop()
        else:
            try:
                n = int(self.max_lines.get())
            except ValueError:
                n = 20000
            self.lines = collections.deque(self.lines, maxlen=max(1000, n))
            hooks = self.app.ensure_debug_hooks()
            hooks.trace = self.trace
            self.logging = True
            self.toggle_btn.configure(text="Stop Logging")

    def stop(self) -> None:
        hooks = self.app.debug_hooks
        if hooks:
            hooks.trace = None
        self.logging = False
        self.toggle_btn.configure(text="Start Logging")
        self.app.maybe_release_debug_hooks()
        self.refresh(force=True)

    def trace(self, cpu) -> None:
        bus = cpu.bus
        pc = cpu.pc
        line = disassemble(bus, pc, 1)[0]
        self.lines.append(
            f"{line:<32} A:{cpu.a:02X} X:{cpu.x:02X} Y:{cpu.y:02X} S:{cpu.sp:02X} "
            f"P:{cpu.p:02X} CYC:{cpu.cycles}")

    def clear(self) -> None:
        self.lines.clear()
        self.refresh(force=True)

    def save(self) -> None:
        path = filedialog.asksaveasfilename(parent=self.top, defaultextension=".log",
                                            filetypes=(("Trace log", "*.log"), ("All files", "*.*")))
        if path:
            pathlib.Path(path).write_text("\n".join(self.lines) + "\n")

    def refresh(self, force: bool = False) -> None:
        if not (force or self.logging):
            return
        tail = list(self.lines)[-400:]
        self.text.configure(state=tk.NORMAL)
        self.text.delete("1.0", tk.END)
        self.text.insert(tk.END, "\n".join(tail))
        self.text.see(tk.END)
        self.text.configure(state=tk.DISABLED)

    def on_close(self) -> None:
        if self.logging:
            self.stop()


# ----------------------------------------------------------- RAM search core
class RamSearch:
    """Cheat-search style filtering over the 2 KiB of internal RAM (+WRAM)."""

    def __init__(self) -> None:
        self.candidates: list[int] = []
        self.previous: dict[int, int] = {}

    def reset(self, nes: "NES", include_wram: bool = False) -> None:
        addrs = list(range(0x800))
        if include_wram:
            addrs += list(range(0x6000, 0x8000))
        self.candidates = addrs
        self.previous = {a: nes.bus.peek(a) for a in addrs}

    def filter(self, nes: "NES", mode: str, value: Optional[int] = None) -> None:
        keep = []
        for a in self.candidates:
            cur = nes.bus.peek(a)
            old = self.previous.get(a, cur)
            if mode == "known":
                ok = cur == value
            elif mode == "eq":
                ok = cur == old
            elif mode == "ne":
                ok = cur != old
            elif mode == "gt":
                ok = cur > old
            elif mode == "lt":
                ok = cur < old
            else:
                ok = True
            if ok:
                keep.append(a)
        self.candidates = keep
        self.previous = {a: nes.bus.peek(a) for a in keep}


class RamSearchWindow(ToolWindow):
    title = "RAM Search"
    key = "ramsearch"
    refresh_every = 15

    def build(self) -> None:
        self.search = RamSearch()
        self._build_search(self.frame)

    def _build_search(self, parent) -> None:
        box = ttk.LabelFrame(parent, text="Search", padding=6)
        box.pack(fill=tk.BOTH, expand=True)
        row = ttk.Frame(box)
        row.pack(fill=tk.X)
        self.button(row, "Reset", self.do_reset).pack(side=tk.LEFT)
        self.wram = tk.BooleanVar(value=False)
        ttk.Checkbutton(row, text="Include $6000-$7FFF", variable=self.wram).pack(side=tk.LEFT, padx=6)
        row2 = ttk.Frame(box)
        row2.pack(fill=tk.X, pady=4)
        self.button(row2, "Known Value:", lambda: self.do_filter("known")).pack(side=tk.LEFT)
        self.known = ttk.Entry(row2, width=5)
        self.known.pack(side=tk.LEFT, padx=2)
        for text, mode in (("Equal", "eq"), ("Not Equal", "ne"), ("Greater Than", "gt"),
                           ("Less Than", "lt")):
            self.button(row2, text, lambda m=mode: self.do_filter(m)).pack(side=tk.LEFT, padx=1)
        self.result_label = tk.StringVar(value="Press Reset to begin a search")
        ttk.Label(box, textvariable=self.result_label).pack(anchor=tk.W)
        self.results = tk.Listbox(box, height=14, font=MONO_FONT)
        self.results.pack(fill=tk.BOTH, expand=True)
        self.results.bind("<Double-Button-1>", self.on_double)

    def do_reset(self) -> None:
        if self.nes:
            self.search.reset(self.nes, self.wram.get())
            self.refresh()

    def do_filter(self, mode: str) -> None:
        if not self.nes or not self.search.candidates:
            return
        value = None
        if mode == "known":
            value = _parse_hex(self.known.get())
            if value is None:
                return
        self.search.filter(self.nes, mode, value)
        self.refresh()

    def on_double(self, _event) -> None:
        sel = self.results.curselection()
        if not sel:
            return
        addr = int(self.results.get(sel[0]).split(":")[0].strip("$"), 16)
        self.app.open_tool(RamWatchWindow).add_address(addr)

    def refresh(self) -> None:
        nes = self.nes
        cand = self.search.candidates
        self.result_label.set(f"{len(cand)} possibilities")
        self.results.delete(0, tk.END)
        if not nes:
            return
        for a in cand[:500]:
            cur = nes.bus.peek(a)
            self.results.insert(tk.END, f"${a:04X}: {cur:3d} (${cur:02X})  prev {self.search.previous.get(a, cur):3d}")


# -------------------------------------------------------------------- Cheats
class CheatsWindow(RamSearchWindow):
    title = "Cheats"
    key = "cheats"

    def build(self) -> None:
        f = self.frame
        active = ttk.LabelFrame(f, text="Active Cheats", padding=6)
        active.pack(fill=tk.BOTH, expand=True)
        cols = ("On", "Code", "Name")
        self.tree = ttk.Treeview(active, columns=cols, show="headings", height=8)
        for c, w in zip(cols, (40, 140, 220)):
            self.tree.heading(c, text=c)
            self.tree.column(c, width=w)
        self.tree.pack(fill=tk.BOTH, expand=True)
        self.tree.bind("<Double-Button-1>", lambda _e: self.toggle())
        row = ttk.Frame(active)
        row.pack(fill=tk.X, pady=4)
        ttk.Label(row, text="Code:").pack(side=tk.LEFT)
        self.code = ttk.Entry(row, width=16)
        self.code.pack(side=tk.LEFT, padx=2)
        ttk.Label(row, text="Name:").pack(side=tk.LEFT)
        self.name = ttk.Entry(row, width=16)
        self.name.pack(side=tk.LEFT, padx=2)
        self.code.bind("<Return>", lambda _e: self.add())
        self.button(row, "Add", self.add).pack(side=tk.LEFT, padx=2)
        self.button(row, "Delete", self.delete).pack(side=tk.LEFT)
        self.button(row, "Toggle", self.toggle).pack(side=tk.LEFT, padx=2)
        ttk.Label(active, text="Codes: Game Genie (6/8 letters), AAAA:VV, AAAA:VV:CC or AAAA?CC:VV",
                  foreground="#555").pack(anchor=tk.W)
        self.search = RamSearch()
        self._build_search(f)
        self.load_tree()

    def load_tree(self) -> None:
        self.tree.delete(*self.tree.get_children())
        for i, c in enumerate(self.app.cheats):
            self.tree.insert("", tk.END, iid=str(i), values=(
                "Y" if c.get("enabled", True) else "", c["code"], c.get("name", "")))

    def add(self) -> None:
        text = self.code.get().strip()
        if not text:
            return
        try:
            addr, val, cmp_ = parse_cheat(text)
        except (ValueError, IndexError) as exc:
            messagebox.showerror("Cheats", f"Bad cheat code: {exc}", parent=self.top)
            return
        self.app.cheats.append({"code": text.upper(), "name": self.name.get().strip(),
                                "addr": addr, "value": val, "compare": cmp_, "enabled": True})
        self.code.delete(0, tk.END)
        self.name.delete(0, tk.END)
        self.app.apply_cheats()
        self.load_tree()

    def delete(self) -> None:
        for iid in sorted(self.tree.selection(), key=int, reverse=True):
            del self.app.cheats[int(iid)]
        self.app.apply_cheats()
        self.load_tree()

    def toggle(self) -> None:
        for iid in self.tree.selection():
            c = self.app.cheats[int(iid)]
            c["enabled"] = not c.get("enabled", True)
        self.app.apply_cheats()
        self.load_tree()

    def on_double(self, _event) -> None:
        sel = self.results.curselection()
        if not sel or not self.nes:
            return
        addr = int(self.results.get(sel[0]).split(":")[0].strip("$"), 16)
        self.code.delete(0, tk.END)
        self.code.insert(0, f"{addr:04X}:{self.nes.bus.peek(addr):02X}")


# ----------------------------------------------------------------- RAM watch
class RamWatchWindow(ToolWindow):
    title = "RAM Watch"
    key = "ramwatch"
    refresh_every = 4

    def build(self) -> None:
        f = self.frame
        cols = ("Address", "Value", "Hex", "Name")
        self.tree = ttk.Treeview(f, columns=cols, show="headings", height=14)
        for c, w in zip(cols, (80, 60, 60, 200)):
            self.tree.heading(c, text=c)
            self.tree.column(c, width=w)
        self.tree.pack(fill=tk.BOTH, expand=True)
        row = ttk.Frame(f)
        row.pack(fill=tk.X, pady=4)
        ttk.Label(row, text="Address:").pack(side=tk.LEFT)
        self.addr = ttk.Entry(row, width=7)
        self.addr.pack(side=tk.LEFT, padx=2)
        ttk.Label(row, text="Name:").pack(side=tk.LEFT)
        self.name = ttk.Entry(row, width=14)
        self.name.pack(side=tk.LEFT, padx=2)
        self.addr.bind("<Return>", lambda _e: self.add())
        self.button(row, "Add", self.add).pack(side=tk.LEFT, padx=2)
        self.button(row, "Remove", self.remove).pack(side=tk.LEFT)
        self.watches: list = self.app.watches

    def add_address(self, addr: int, name: str = "") -> None:
        self.watches.append((addr & 0xFFFF, name))
        self.refresh()

    def add(self) -> None:
        addr = _parse_hex(self.addr.get())
        if addr is None:
            return
        self.add_address(addr, self.name.get().strip())
        self.addr.delete(0, tk.END)
        self.name.delete(0, tk.END)

    def remove(self) -> None:
        for iid in sorted(self.tree.selection(), key=int, reverse=True):
            del self.watches[int(iid)]
        self.refresh()

    def refresh(self) -> None:
        nes = self.nes
        self.tree.delete(*self.tree.get_children())
        for i, (addr, name) in enumerate(self.watches):
            val = nes.bus.peek(addr) if nes else 0
            self.tree.insert("", tk.END, iid=str(i), values=(f"${addr:04X}", val, f"${val:02X}", name))


# -------------------------------------------------------------- Frame timing
class FrameTimingWindow(ToolWindow):
    title = "Frame Timing"
    key = "timing"
    refresh_every = 15

    def build(self) -> None:
        self.var = tk.StringVar()
        ttk.Label(self.frame, textvariable=self.var, font=MONO_FONT, justify=tk.LEFT).pack(anchor=tk.W)

    def refresh(self) -> None:
        app = self.app
        st = app.stats
        target = app.target_fps()
        self.var.set(
            f"Region:            {app.region.get()}\n"
            f"Target rate:       {target:8.3f} fps  ({app.speed_label()})\n"
            f"Measured rate:     {st['fps']:8.3f} fps\n"
            f"Emulation / frame: {st['emu_ms']:8.3f} ms\n"
            f"Display / frame:   {st['draw_ms']:8.3f} ms\n"
            f"Frame budget:      {1000.0 / max(target, 0.01):8.3f} ms\n"
            f"Frames skipped:    {st['skipped']:8d}\n"
            f"Audio backend:     {app.audio.backend}\n"
            f"Audio queued:      {max(0.0, app.audio.level_ms()):8.1f} ms")


# --------------------------------------------------------- Game Genie tool
class GameGenieWindow(ToolWindow):
    title = "Game Genie Encoder/Decoder Tool"
    key = "gamegenie"
    refresh_every = 1000

    def build(self) -> None:
        f = self.frame
        grid = ttk.Frame(f)
        grid.pack()
        self.entries = {}
        for r, label in enumerate(("Address", "Compare", "Value", "Game Genie Code")):
            ttk.Label(grid, text=label + ":").grid(row=r, column=0, sticky=tk.E, pady=2)
            e = ttk.Entry(grid, width=12)
            e.grid(row=r, column=1, sticky=tk.W, padx=4)
            self.entries[label] = e
        row = ttk.Frame(f)
        row.pack(pady=6)
        self.button(row, "Encode", self.encode).pack(side=tk.LEFT, padx=2)
        self.button(row, "Decode", self.decode).pack(side=tk.LEFT, padx=2)
        self.button(row, "Add To Cheat List", self.add).pack(side=tk.LEFT, padx=2)
        self.msg = tk.StringVar()
        ttk.Label(f, textvariable=self.msg).pack()

    def encode(self) -> None:
        addr = _parse_hex(self.entries["Address"].get())
        val = _parse_hex(self.entries["Value"].get())
        cmp_ = _parse_hex(self.entries["Compare"].get())
        if addr is None or val is None or addr < 0x8000:
            self.msg.set("Address must be $8000-$FFFF and a value is required")
            return
        code = game_genie_encode(addr, val & 0xFF, None if cmp_ is None else cmp_ & 0xFF)
        e = self.entries["Game Genie Code"]
        e.delete(0, tk.END)
        e.insert(0, code)
        self.msg.set("")

    def decode(self) -> None:
        try:
            addr, val, cmp_ = game_genie_decode(self.entries["Game Genie Code"].get())
        except ValueError as exc:
            self.msg.set(str(exc))
            return
        for label, v in (("Address", f"{addr:04X}"), ("Value", f"{val:02X}"),
                         ("Compare", "" if cmp_ is None else f"{cmp_:02X}")):
            e = self.entries[label]
            e.delete(0, tk.END)
            e.insert(0, v)
        self.msg.set("")

    def add(self) -> None:
        code = self.entries["Game Genie Code"].get().strip()
        if not code:
            self.encode()
            code = self.entries["Game Genie Code"].get().strip()
        try:
            addr, val, cmp_ = game_genie_decode(code)
        except ValueError as exc:
            self.msg.set(str(exc))
            return
        self.app.cheats.append({"code": code.upper(), "name": "Game Genie", "addr": addr,
                                "value": val, "compare": cmp_, "enabled": True})
        self.app.apply_cheats()
        self.msg.set(f"Added {code.upper()}")


# ------------------------------------------------------------ Header viewer
class HeaderEditorWindow(ToolWindow):
    title = "iNES Header Editor"
    key = "header"
    refresh_every = 1000

    def build(self) -> None:
        self.var = tk.StringVar()
        ttk.Label(self.frame, textvariable=self.var, font=MONO_FONT, justify=tk.LEFT).pack(anchor=tk.W)
        ttk.Label(self.frame, text="(read-only: the ROM file is never modified)",
                  foreground="#555").pack(anchor=tk.W, pady=(6, 0))

    def refresh(self) -> None:
        nes = self.nes
        if not nes:
            self.var.set("No game loaded")
            return
        cart = nes.cart
        h = cart.header
        chr_bytes = b"" if cart.chr_is_ram else bytes(cart.chr)
        doc = (type(cart.mapper).__doc__ or "").strip().split("\n")[0][:60]
        lines = [
            f"File:        {pathlib.Path(cart.source).name}",
            f"Format:      {'NES 2.0' if cart.nes2 else 'iNES'}",
            f"Header:      {' '.join(f'{b:02X}' for b in h)}",
            f"Mapper:      {cart.mapper_id}  {doc}",
            f"PRG ROM:     {cart.prg_len // 1024} KiB",
            f"CHR {'RAM' if cart.chr_is_ram else 'ROM'}:     {cart.chr_len // 1024} KiB",
            f"Mirroring:   {cart.header_mirroring}",
            f"Battery:     {'yes' if cart.battery else 'no'}",
            f"Trainer:     {'yes' if h[6] & 4 else 'no'}",
            f"PRG CRC32:   {zlib.crc32(cart.prg) & 0xFFFFFFFF:08X}",
            f"ROM CRC32:   {zlib.crc32(cart.prg + chr_bytes) & 0xFFFFFFFF:08X}",
        ]
        self.var.set("\n".join(lines))


# --------------------------------------------------------------- Message log
class MessageLogWindow(ToolWindow):
    title = "Message Log"
    key = "log"
    refresh_every = 30

    def build(self) -> None:
        self.text = tk.Text(self.frame, width=80, height=22, font=MONO_FONT, wrap=tk.WORD)
        self.text.pack(fill=tk.BOTH, expand=True)
        self._shown = -1

    def refresh(self) -> None:
        if self._shown == len(self.app.messages):
            return
        self._shown = len(self.app.messages)
        self.text.configure(state=tk.NORMAL)
        self.text.delete("1.0", tk.END)
        self.text.insert(tk.END, "\n".join(self.app.messages))
        self.text.see(tk.END)
        self.text.configure(state=tk.DISABLED)


# =========================================================== config dialogs
def _describe_key(keysym: str) -> str:
    return keysym if keysym else "<none>"


class KeyCapture:
    """Grab the next key press in a window and hand back its keysym."""

    def __init__(self, top: tk.Toplevel, done: Callable[[str], None], with_mods: bool = False) -> None:
        self.top = top
        self.done = done
        self.with_mods = with_mods
        self.bid = top.bind("<KeyPress>", self.on_key, add="+")
        top.focus_force()

    def on_key(self, event) -> str:
        sym = event.keysym
        if sym in ("Shift_L", "Shift_R", "Control_L", "Control_R", "Alt_L", "Alt_R",
                   "Meta_L", "Meta_R", "Super_L", "Super_R", "Option_L", "Option_R"):
            return "break"
        try:
            self.top.unbind("<KeyPress>", self.bid)
        except tk.TclError:
            pass
        if sym == "Escape":
            self.done("")
        elif self.with_mods:
            self.done(EmulatorGUI.chord_from_event(event))
        else:
            self.done(sym if len(sym) > 1 else sym.lower())
        return "break"


class InputConfigWindow(ToolWindow):
    title = "Input Configuration"
    key = "input"
    refresh_every = 1000

    def build(self) -> None:
        nb = ttk.Notebook(self.frame)
        nb.pack(fill=tk.BOTH, expand=True)
        self.labels = {}
        for port in range(2):
            page = ttk.Frame(nb, padding=8)
            nb.add(page, text=f"Gamepad {port + 1}")
            for r, name in enumerate(NES_BUTTONS + TURBO_BUTTONS):
                ttk.Label(page, text=name, width=10).grid(row=r, column=0, sticky=tk.W, pady=2)
                var = tk.StringVar(value=_describe_key(self.app.pad_keys[port].get(name, "")))
                ttk.Label(page, textvariable=var, width=14, relief=tk.SUNKEN).grid(row=r, column=1, padx=4)
                self.labels[(port, name)] = var
                ttk.Button(page, text="Change", command=lambda p=port, n=name: self.change(p, n)).grid(
                    row=r, column=2)
                ttk.Button(page, text="Clear", command=lambda p=port, n=name: self.set_key(p, n, "")).grid(
                    row=r, column=3, padx=2)
        bar = ttk.Frame(self.frame)
        bar.pack(fill=tk.X, pady=(6, 0))
        self.status = tk.StringVar(value="Click Change, then press a key (Esc cancels)")
        ttk.Label(bar, textvariable=self.status).pack(side=tk.LEFT)
        ttk.Button(bar, text="Defaults", command=self.defaults).pack(side=tk.RIGHT)
        ttk.Button(bar, text="Close", command=self.close).pack(side=tk.RIGHT, padx=4)

    def change(self, port: int, name: str) -> None:
        self.status.set(f"Press a key for Gamepad {port + 1} {name}...")
        KeyCapture(self.top, lambda sym: self.set_key(port, name, sym))

    def set_key(self, port: int, name: str, sym: str) -> None:
        self.app.pad_keys[port][name] = sym
        self.labels[(port, name)].set(_describe_key(sym))
        self.status.set(f"Gamepad {port + 1} {name} = {_describe_key(sym)}")
        self.app.rebuild_key_maps()

    def defaults(self) -> None:
        for port in range(2):
            for name, sym in DEFAULT_PAD_KEYS[port].items():
                self.app.pad_keys[port][name] = sym
                self.labels[(port, name)].set(_describe_key(sym))
        self.app.rebuild_key_maps()


class SoundConfigWindow(ToolWindow):
    title = "Sound Config"
    key = "sound"
    refresh_every = 1000

    def build(self) -> None:
        f = self.frame
        app = self.app
        self.enabled = tk.BooleanVar(value=not app.muted.get())
        ttk.Checkbutton(f, text="Enable Sound", variable=self.enabled, command=self.apply).pack(anchor=tk.W)
        info = ttk.Frame(f)
        info.pack(fill=tk.X, pady=4)
        ttk.Label(info, text=f"Output: {app.audio.backend}   Rate: {app.audio.rate} Hz").pack(anchor=tk.W)
        if not app.audio.available:
            ttk.Label(info, text="No audio backend — pip install sounddevice (or pygame-ce)",
                      foreground="#a00").pack(anchor=tk.W)
        box = ttk.LabelFrame(f, text="Volume", padding=6)
        box.pack(fill=tk.BOTH)
        self.vars = []
        for col, name in enumerate(("Master", "Square 1", "Square 2", "Triangle", "Noise", "PCM")):
            var = tk.IntVar(value=app.volumes[col])
            self.vars.append(var)
            ttk.Label(box, text=name).grid(row=0, column=col, padx=4)
            tk.Scale(box, from_=255, to=0, orient=tk.VERTICAL, variable=var, length=140,
                     command=lambda _v: self.apply()).grid(row=1, column=col)
        ttk.Button(f, text="Close", command=self.close).pack(anchor=tk.E, pady=(6, 0))

    def apply(self) -> None:
        app = self.app
        app.volumes = [v.get() for v in self.vars]
        app.muted.set(not self.enabled.get())
        app.apply_sound_settings()


class VideoConfigWindow(ToolWindow):
    title = "Video Config"
    key = "video"
    refresh_every = 1000

    def build(self) -> None:
        f = self.frame
        app = self.app
        box = ttk.LabelFrame(f, text="Window Size", padding=6)
        box.pack(fill=tk.X)
        for n in (1, 2, 3, 4):
            ttk.Radiobutton(box, text=f"{n}x ({256 * n}x{240 * n})", value=n, variable=app.scale,
                            command=app.apply_scale).pack(anchor=tk.W)
        opts = ttk.LabelFrame(f, text="Drawing Area", padding=6)
        opts.pack(fill=tk.X, pady=6)
        ttk.Checkbutton(opts, text="Clip Left and Right Sides (8 px)", variable=app.clip_sides).pack(anchor=tk.W)
        ttk.Checkbutton(opts, text="Show FPS", variable=app.show_fps).pack(anchor=tk.W)
        ttk.Checkbutton(opts, text="Show Frame Counter", variable=app.show_frame).pack(anchor=tk.W)
        ttk.Checkbutton(opts, text="Show Lag Counter", variable=app.show_lag).pack(anchor=tk.W)
        ttk.Checkbutton(opts, text="Show Input Display", variable=app.show_input).pack(anchor=tk.W)
        ttk.Button(f, text="Close", command=self.close).pack(anchor=tk.E)


class HotkeyConfigWindow(ToolWindow):
    title = "Hotkey Config"
    key = "hotkeys"
    refresh_every = 1000

    def build(self) -> None:
        f = self.frame
        self.tree = ttk.Treeview(f, columns=("Command", "Key"), show="headings", height=22)
        self.tree.heading("Command", text="Command")
        self.tree.heading("Key", text="Key")
        self.tree.column("Command", width=220)
        self.tree.column("Key", width=140)
        self.tree.pack(fill=tk.BOTH, expand=True)
        self.tree.bind("<Double-Button-1>", lambda _e: self.change())
        bar = ttk.Frame(f)
        bar.pack(fill=tk.X, pady=4)
        self.status = tk.StringVar(value="Double-click a command, then press the new key")
        ttk.Label(bar, textvariable=self.status).pack(side=tk.LEFT)
        ttk.Button(bar, text="Defaults", command=self.defaults).pack(side=tk.RIGHT)
        ttk.Button(bar, text="Clear", command=self.clear).pack(side=tk.RIGHT, padx=4)
        self.load()

    def load(self) -> None:
        self.tree.delete(*self.tree.get_children())
        for name, chord in self.app.hotkeys.items():
            self.tree.insert("", tk.END, iid=name, values=(name, chord or "<none>"))

    def change(self) -> None:
        sel = self.tree.selection()
        if not sel:
            return
        name = sel[0]
        self.status.set(f"Press the key for '{name}' (Esc clears)...")

        def done(chord: str) -> None:
            self.app.hotkeys[name] = chord
            self.app.rebuild_key_maps()
            self.status.set(f"{name} = {chord or '<none>'}")
            self.load()
        KeyCapture(self.top, done, with_mods=True)

    def clear(self) -> None:
        for name in self.tree.selection():
            self.app.hotkeys[name] = ""
        self.app.rebuild_key_maps()
        self.load()

    def defaults(self) -> None:
        self.app.hotkeys = collections.OrderedDict(DEFAULT_HOTKEYS)
        self.app.rebuild_key_maps()
        self.load()


class PaletteConfigWindow(ToolWindow):
    title = "Palette Config"
    key = "palette"
    refresh_every = 1000

    def build(self) -> None:
        f = self.frame
        self.img = tk.PhotoImage(width=16 * 20, height=4 * 20)
        ttk.Label(f, image=self.img).pack()
        row = ttk.Frame(f)
        row.pack(fill=tk.X, pady=6)
        ttk.Button(row, text="Load Palette File (.pal)...", command=self.load_file).pack(side=tk.LEFT)
        ttk.Button(row, text="Use Default", command=self.use_default).pack(side=tk.LEFT, padx=4)
        self.name = tk.StringVar(value=self.app.palette_name)
        ttk.Label(f, textvariable=self.name).pack(anchor=tk.W)
        ttk.Button(f, text="Close", command=self.close).pack(anchor=tk.E)

    def refresh(self) -> None:
        rgb = bytearray(320 * 80 * 3)
        for idx in range(64):
            c = bytes(_DISPLAY_PALETTE[idx])
            cx = (idx & 15) * 20
            cy = (idx >> 4) * 20
            for yy in range(cy, cy + 20):
                o = (yy * 320 + cx) * 3
                rgb[o:o + 60] = c * 20
        self.img.tk.call(self.img, "put", ppm_bytes(320, 80, rgb), "-format", "ppm")

    def load_file(self) -> None:
        path = filedialog.askopenfilename(parent=self.top, title="Load Palette",
                                          filetypes=(("Palette", "*.pal"), ("All files", "*.*")))
        if not path:
            return
        data = pathlib.Path(path).read_bytes()
        if len(data) < 192:
            messagebox.showerror("Palette Config", "A .pal file needs at least 192 bytes.", parent=self.top)
            return
        pal = tuple(tuple(data[i * 3:i * 3 + 3]) for i in range(64))
        self.app.set_palette(pal, pathlib.Path(path).name)
        self.name.set(self.app.palette_name)
        self.refresh()

    def use_default(self) -> None:
        self.app.set_palette(NES_PALETTE, "Default (built-in)")
        self.name.set(self.app.palette_name)
        self.refresh()


class SimpleOptionsWindow(ToolWindow):
    """Generic checkbox/option dialog used by GUI / Timing / Movie configs."""

    options: tuple = ()

    def build(self) -> None:
        for label, attr in self.options:
            ttk.Checkbutton(self.frame, text=label, variable=getattr(self.app, attr)).pack(anchor=tk.W, pady=1)
        self.extra()
        ttk.Button(self.frame, text="Close", command=self.close).pack(anchor=tk.E, pady=(8, 0))

    def extra(self) -> None:
        pass


class GuiConfigWindow(SimpleOptionsWindow):
    title = "GUI Config"
    key = "guiconfig"
    options = (("Pause when the window loses focus", "pause_on_focus_loss"),
               ("Show on-screen messages", "show_messages"))


class TimingConfigWindow(SimpleOptionsWindow):
    title = "Timing Config"
    key = "timingconfig"
    options = (("Sync emulation to the audio device", "audio_sync"),
               ("Skip drawing frames when the host falls behind", "allow_frameskip"))


class MovieOptionsWindow(SimpleOptionsWindow):
    title = "Movie Options"
    key = "movieopts"
    options = (("Always open movies read-only", "movie_readonly"),
               ("Display movie status", "show_movie_status"))


class StateRecorderConfigWindow(SimpleOptionsWindow):
    title = "State Recorder Config"
    key = "staterec"
    options = (("Enable state recorder", "state_recorder"),)

    def extra(self) -> None:
        row = ttk.Frame(self.frame)
        row.pack(fill=tk.X, pady=6)
        ttk.Label(row, text="Record every").pack(side=tk.LEFT)
        ttk.Spinbox(row, from_=10, to=600, textvariable=self.app.recorder_interval, width=5).pack(side=tk.LEFT, padx=4)
        ttk.Label(row, text="frames, keep").pack(side=tk.LEFT)
        ttk.Spinbox(row, from_=2, to=200, textvariable=self.app.recorder_depth, width=5).pack(side=tk.LEFT, padx=4)
        ttk.Label(row, text="states").pack(side=tk.LEFT)
        ttk.Button(self.frame, text="Load Previous Recorded State",
                   command=self.app.recorder_load_previous).pack(anchor=tk.W)


# ---------------------------------------------------------------------------
# Main window — mirrors the FCEUX 2.6 (Qt) console window
# ---------------------------------------------------------------------------
class EmulatorGUI:
    """FCEUX-style console: menu bar + black game client + tool windows."""

    MAX_RECENT = 10

    def __init__(self, root: "tk.Tk", initial_rom: Optional[str] = None) -> None:
        self.root = root
        root.title(APP_TITLE)
        root.configure(bg="#000000")
        self.nes: Optional[NES] = None
        self.rom_path: Optional[pathlib.Path] = None
        self.running = False
        self.paused = False
        self._alive = True
        # ---- options (FCEUX defaults)
        self.scale = tk.IntVar(value=2)
        self.muted = tk.BooleanVar(value=False)
        self.region = tk.StringVar(value="NTSC")
        self.ram_init = tk.StringVar(value="Default")
        self.game_genie = tk.BooleanVar(value=True)
        self.autofire = tk.IntVar(value=0)
        self.auto_resume = tk.BooleanVar(value=False)
        self.auto_hide_menu_fs = tk.BooleanVar(value=True)
        self.use_bg_palette = tk.BooleanVar(value=False)
        self.state_slot = tk.IntVar(value=1)
        self.show_fps = tk.BooleanVar(value=False)
        self.show_frame = tk.BooleanVar(value=False)
        self.show_lag = tk.BooleanVar(value=False)
        self.show_input = tk.BooleanVar(value=False)
        self.clip_sides = tk.BooleanVar(value=False)
        self.pause_on_focus_loss = tk.BooleanVar(value=False)
        self.show_messages = tk.BooleanVar(value=True)
        self.audio_sync = tk.BooleanVar(value=True)
        self.allow_frameskip = tk.BooleanVar(value=True)
        self.movie_readonly = tk.BooleanVar(value=True)
        self.show_movie_status = tk.BooleanVar(value=True)
        self.state_recorder = tk.BooleanVar(value=False)
        self.recorder_interval = tk.IntVar(value=60)
        self.recorder_depth = tk.IntVar(value=30)
        self.speed_pct = 100.0
        self.turbo_mode = False
        self.turbo_hold = False
        self.frame_advance_delay = 0
        self.bg_color = "#000000"
        self.volumes = [255, 255, 255, 255, 255, 255]
        self.palette_name = "Default (built-in)"
        self.pad_keys = copy.deepcopy(DEFAULT_PAD_KEYS)
        self.hotkeys = collections.OrderedDict(DEFAULT_HOTKEYS)
        self.cheats: list = []
        self.watches: list = []
        self.messages: list = []
        self.recent: list = []
        self.state_slots: dict = {}
        self.resume_states: dict = {}
        self.recorder: collections.deque = collections.deque(maxlen=30)
        self.tools: dict = {}
        self.debug_hooks: Optional[DebugHooks] = None
        self._temp_breaks: set = set()
        self._break_pc: Optional[int] = None
        self.movie_mode: Optional[str] = None
        self.movie_frames: list = []
        self.movie_index = 0
        self.movie_path: Optional[str] = None
        self.wav: Optional[WavWriter] = None
        self.wav_path: Optional[str] = None
        self.fullscreen = False
        self.menu_hidden = False
        self._focused = True
        self._pressed: set = set()
        self._osd_text = ""
        self._osd_until = 0.0
        self._next = time.perf_counter()
        self._frames = 0
        self._fps_t = time.perf_counter()
        self._fps_n = 0
        self._last_tool_refresh = 0.0
        self.stats = {"fps": 0.0, "emu_ms": 0.0, "draw_ms": 0.0, "skipped": 0}
        self.audio = AudioOutput(APU.SAMPLE_RATE)
        self._ppm_header = b"P6\n256 240\n255\n"
        self._zoom = 2
        self._rgb = bytearray(SCREEN_W * SCREEN_H * 3)
        self.rebuild_key_maps()
        self._build_menu()
        self._build_screen()
        self.apply_scale()
        root.bind_all("<KeyPress>", self._on_key_press, add="+")
        root.bind_all("<KeyRelease>", self._on_key_release, add="+")
        root.bind("<FocusIn>", lambda _e: self._set_focus(True))
        root.bind("<FocusOut>", lambda _e: self._set_focus(False))
        root.protocol("WM_DELETE_WINDOW", self.quit)
        self.log(f"{APP_TITLE} — {len(MAPPERS)} mappers, audio: {self.audio.backend}")
        if not self.audio.available:
            self.log("Audio unavailable (" + self.audio.error.strip("; ") + "). "
                     "Install sounddevice or pygame-ce for sound.")
        if initial_rom:
            self.load_rom(initial_rom)
        self._after = root.after(1, self._loop)

    # ================================================================ menus
    @staticmethod
    def _mn(text: str) -> dict:
        """'&Open ROM' -> label='Open ROM', underline=0 (Qt-style mnemonic)."""
        idx = text.find("&")
        if idx < 0:
            return {"label": text}
        return {"label": text.replace("&", "", 1), "underline": idx}

    def _accel(self, action: str) -> str:
        chord = self.hotkeys.get(action, "")
        if not chord:
            return ""
        pretty = {"comma": ",", "period": ".", "slash": "/", "backslash": "\\",
                  "minus": "-", "equal": "=", "Return": "Return"}
        parts = chord.split("+")
        key = parts[-1]
        key = pretty.get(key, key.upper() if len(key) == 1 else key)
        return "+".join(parts[:-1] + [key])

    def _menu(self, parent) -> "tk.Menu":
        return tk.Menu(parent, tearoff=False)

    def _cmd(self, menu, text, command=None, action=None, state="normal", accel=None):
        menu.add_command(command=command or (lambda: None), state=state,
                         accelerator=accel if accel is not None else (self._accel(action) if action else ""),
                         **self._mn(text))

    def _build_menu(self) -> None:
        bar = tk.Menu(self.root, tearoff=False)
        self.menubar = bar
        D = tk.DISABLED

        # ---------------------------------------------------------- File
        m = self._menu(bar)
        self._cmd(m, "&Open ROM", self.open_rom_dialog, "Open ROM")
        self._cmd(m, "&Close ROM", self.close_rom, "Close ROM")
        self.recent_menu = self._menu(m)
        m.add_cascade(menu=self.recent_menu, **self._mn("&Recent ROMs"))
        m.add_separator()
        self._cmd(m, "Play &NSF", state=D)
        m.add_separator()
        self._cmd(m, "Load State &From", self.load_state_from)
        self._cmd(m, "Save State &As", self.save_state_as)
        self._cmd(m, "Quick &Load", self.quick_load, "Load State")
        self._cmd(m, "Quick &Save", self.quick_save, "Save State")
        slots = self._menu(m)
        for n in range(10):
            slots.add_radiobutton(variable=self.state_slot, value=n,
                                  command=lambda n=n: self.select_slot(n),
                                  accelerator=self._accel(f"Select State Slot {n}"),
                                  **self._mn(f"Slot &{n}"))
        m.add_cascade(menu=slots, **self._mn("Change &State Slot"))
        m.add_separator()
        self._cmd(m, "Load &Lua Script", state=D)
        m.add_separator()
        self._cmd(m, "Screens&hot", self.screenshot, "Screenshot")
        self._cmd(m, "&Quit", self.quit, "Quit")
        bar.add_cascade(menu=m, **self._mn("&File"))
        self._refresh_recent_menu()

        # --------------------------------------------------------- Movie
        m = self._menu(bar)
        self._cmd(m, "Movie &Play", self.movie_play)
        self._cmd(m, "Movie Play From &Beginning", self.movie_play_beginning)
        self._cmd(m, "Movie &Stop", self.movie_stop)
        m.add_separator()
        self._cmd(m, "Movie &Record", self.movie_record)
        m.add_separator()
        self._cmd(m, "AVI &Record", state=D)
        self._cmd(m, "AVI Record &As", state=D)
        self._cmd(m, "AVI &Stop", state=D)
        m.add_separator()
        self._cmd(m, "WAV &Record", self.wav_record)
        self._cmd(m, "WAV Record &As", self.wav_record_as)
        self._cmd(m, "WAV &Stop", self.wav_stop)
        bar.add_cascade(menu=m, **self._mn("&Movie"))

        # ------------------------------------------------------- Options
        m = self._menu(bar)
        self._cmd(m, "&Input Config", lambda: self.open_tool(InputConfigWindow))
        self._cmd(m, "&GamePad Config", lambda: self.open_tool(InputConfigWindow))
        self._cmd(m, "&Sound Config", lambda: self.open_tool(SoundConfigWindow))
        self._cmd(m, "&Video Config", lambda: self.open_tool(VideoConfigWindow))
        self._cmd(m, "Hot&Key Config", lambda: self.open_tool(HotkeyConfigWindow))
        self._cmd(m, "&Palette Config", lambda: self.open_tool(PaletteConfigWindow))
        self._cmd(m, "G&UI Config", lambda: self.open_tool(GuiConfigWindow))
        self._cmd(m, "&Timing Config", lambda: self.open_tool(TimingConfigWindow))
        self._cmd(m, "&State Recorder Config", lambda: self.open_tool(StateRecorderConfigWindow))
        self._cmd(m, "&Movie Options", lambda: self.open_tool(MovieOptionsWindow))
        m.add_checkbutton(variable=self.auto_resume, **self._mn("Auto-&Resume Play"))
        m.add_separator()
        sizes = self._menu(m)
        for n in (1, 2, 3, 4):
            sizes.add_radiobutton(variable=self.scale, value=n, command=self.apply_scale,
                                  **self._mn(f"&{n}x"))
        m.add_cascade(menu=sizes, **self._mn("Window Resi&ze"))
        self._cmd(m, "&Fullscreen", self.toggle_fullscreen, "Fullscreen")
        self._cmd(m, "&Hide Menu", self.toggle_menu, "Hide Menu")
        m.add_checkbutton(variable=self.auto_hide_menu_fs, **self._mn("&Auto Hide Menu on Fullscreen"))
        m.add_separator()
        self._cmd(m, "BG Side Panel Color", self.choose_bg_color)
        m.add_checkbutton(variable=self.use_bg_palette, command=self._apply_bg,
                          label="Use BG Palette for Video BG Color")
        bar.add_cascade(menu=m, **self._mn("&Options"))

        # ----------------------------------------------------- Emulation
        m = self._menu(bar)
        self._cmd(m, "&Power", self.power, "Power")
        self._cmd(m, "Hard &Reset", self.hard_reset, "Hard Reset")
        self._cmd(m, "&Soft Reset", self.soft_reset, "Soft Reset")
        self._cmd(m, "&Pause", self.toggle_pause, "Pause")
        m.add_separator()
        reg = self._menu(m)
        for name in ("NTSC", "PAL", "Dendy"):
            reg.add_radiobutton(variable=self.region, value=name, command=self.apply_region,
                                **self._mn(f"&{name}"))
        m.add_cascade(menu=reg, **self._mn("&Region"))
        ram = self._menu(m)
        for text, val in (("&Default", "Default"), ("Fill $&FF", "Fill $FF"),
                          ("Fill $&00", "Fill $00"), ("&Random", "Random")):
            ram.add_radiobutton(variable=self.ram_init, value=val, **self._mn(text))
        m.add_cascade(menu=ram, **self._mn("&RAM Init"))
        m.add_separator()
        m.add_checkbutton(variable=self.game_genie, command=self.apply_cheats,
                          **self._mn("Enable Game &Genie"))
        self._cmd(m, "Load Game Genie ROM", state=D)
        m.add_separator()
        self._cmd(m, "Virtual Family Keyboard", state=D)
        m.add_separator()
        self._cmd(m, "&Insert Coin", state=D)
        m.add_separator()
        fds = self._menu(m)
        for text in ("&Switch Disk", "&Eject Disk", "&Load BIOS"):
            self._cmd(fds, text, state=D)
        m.add_cascade(menu=fds, **self._mn("&FDS"))
        m.add_separator()
        spd = self._menu(m)
        self._cmd(spd, "Speed &Up", self.speed_up, "Increase Speed")
        self._cmd(spd, "Slow &Down", self.slow_down, "Decrease Speed")
        spd.add_separator()
        self._cmd(spd, "&Slowest", self.speed_slowest)
        self._cmd(spd, "&Normal", self.speed_normal)
        self._cmd(spd, "&Turbo", self.toggle_turbo_mode, "Turbo")
        self._cmd(spd, "&Custom", self.speed_custom)
        spd.add_separator()
        self._cmd(spd, "Set Frame &Advance Delay", self.set_frame_advance_delay)
        m.add_cascade(menu=spd, **self._mn("&Speed"))
        m.add_separator()
        af = self._menu(m)
        for i, (on, off) in enumerate(AUTOFIRE_PATTERNS):
            af.add_radiobutton(variable=self.autofire, value=i, label=f"{on} On, {off} Off")
        af.add_separator()
        self._cmd(af, "Custom", state=D)
        af.add_separator()
        self._cmd(af, "Set Custom Pattern", state=D)
        m.add_cascade(menu=af, **self._mn("&AutoFire Pattern"))
        bar.add_cascade(menu=m, **self._mn("&Emulation"))

        # --------------------------------------------------------- Tools
        m = self._menu(bar)
        self._cmd(m, "&Cheats...", lambda: self.open_tool(CheatsWindow))
        self._cmd(m, "RAM &Search...", lambda: self.open_tool(RamSearchWindow))
        self._cmd(m, "RAM &Watch...", lambda: self.open_tool(RamWatchWindow))
        self._cmd(m, "&Frame Timing ...", lambda: self.open_tool(FrameTimingWindow))
        self._cmd(m, "&Palette Editor ...", lambda: self.open_tool(PaletteConfigWindow))
        self._cmd(m, "&AVI RIFF Viewer ...", state=D)
        self._cmd(m, "&TAS Editor ...", state=D)
        bar.add_cascade(menu=m, **self._mn("&Tools"))

        # --------------------------------------------------------- Debug
        m = self._menu(bar)
        self._cmd(m, "&Debugger...", lambda: self.open_tool(DebuggerWindow))
        self._cmd(m, "&Hex Editor...", lambda: self.open_tool(HexEditorWindow))
        self._cmd(m, "&PPU Viewer...", lambda: self.open_tool(PPUViewerWindow))
        self._cmd(m, "&Sprite Viewer...", lambda: self.open_tool(SpriteViewerWindow))
        self._cmd(m, "&Name Table Viewer...", lambda: self.open_tool(NameTableViewerWindow))
        self._cmd(m, "&Trace Logger...", lambda: self.open_tool(TraceLoggerWindow))
        self._cmd(m, "&Code/Data Logger...", state=D)
        self._cmd(m, "&Game Genie Encode/Decode", lambda: self.open_tool(GameGenieWindow))
        self._cmd(m, "NES Header Edito&r...", lambda: self.open_tool(HeaderEditorWindow))
        bar.add_cascade(menu=m, **self._mn("&Debug"))

        # ------------------------------------------------------- NetPlay
        m = self._menu(bar)
        self._cmd(m, "&Host", state=D)
        self._cmd(m, "&Join", state=D)
        m.add_separator()
        self._cmd(m, "&Disconnect/End Game", state=D)
        bar.add_cascade(menu=m, **self._mn("&NetPlay"))

        # ---------------------------------------------------------- Help
        m = self._menu(bar)
        self._cmd(m, "&About acnesemu", self.show_about)
        self._cmd(m, "About &Tk", self.show_about_tk)
        self._cmd(m, "&Message Log", lambda: self.open_tool(MessageLogWindow))
        docs = self._menu(m)
        self._cmd(docs, "&Online", lambda: webbrowser.open("https://fceux.com/web/help/fceux.html"))
        m.add_cascade(menu=docs, **self._mn("&Documentation"))
        bar.add_cascade(menu=m, **self._mn("&Help"))

        self.root.config(menu=bar)

    def _refresh_recent_menu(self) -> None:
        m = self.recent_menu
        m.delete(0, tk.END)
        for path in self.recent:
            m.add_command(label=str(path), command=lambda p=path: self.load_rom(str(p)))
        m.add_separator()
        m.add_command(label="", state=tk.DISABLED)
        m.add_command(label="Clear Recent ROM List", command=self._clear_recent)

    def _clear_recent(self) -> None:
        self.recent.clear()
        self._refresh_recent_menu()

    # ============================================================== screen
    def _build_screen(self) -> None:
        self.canvas = tk.Canvas(self.root, bg=self.bg_color, highlightthickness=0, bd=0,
                                width=512, height=480)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        self._small = tk.PhotoImage(width=SCREEN_W, height=SCREEN_H)
        self._big = tk.PhotoImage(width=SCREEN_W * 2, height=SCREEN_H * 2)
        self._img_item = self.canvas.create_image(0, 0, anchor=tk.NW, image=self._big)
        font = ("Helvetica", 11, "bold")
        self._txt = {}
        for name, anchor in (("msg", tk.SW), ("fps", tk.NE), ("frame", tk.NW),
                             ("input", tk.SE), ("movie", tk.NW)):
            shadow = self.canvas.create_text(0, 0, text="", fill="#000000", font=font, anchor=anchor)
            text = self.canvas.create_text(0, 0, text="", fill="#ffffff", font=font, anchor=anchor)
            self._txt[name] = (shadow, text)
        self.canvas.bind("<Configure>", lambda _e: self._layout())
        self._blank()

    def _layout(self) -> None:
        try:
            cw = max(1, self.canvas.winfo_width())
            ch = max(1, self.canvas.winfo_height())
        except tk.TclError:
            return
        s = self._zoom
        w, h = SCREEN_W * s, SCREEN_H * s
        ox, oy = max(0, (cw - w) // 2), max(0, (ch - h) // 2)
        self.canvas.coords(self._img_item, ox, oy)
        pos = {"msg": (ox + 6, oy + h - 6), "fps": (ox + w - 6, oy + 6),
               "frame": (ox + 6, oy + 6), "input": (ox + w - 6, oy + h - 6),
               "movie": (ox + 6, oy + 24)}
        for name, (x, y) in pos.items():
            shadow, text = self._txt[name]
            self.canvas.coords(shadow, x + 1, y + 1)
            self.canvas.coords(text, x, y)

    def _set_text(self, name: str, value: str) -> None:
        shadow, text = self._txt[name]
        if self.canvas.itemcget(text, "text") != value:
            self.canvas.itemconfigure(shadow, text=value)
            self.canvas.itemconfigure(text, text=value)

    def apply_scale(self) -> None:
        s = max(1, min(4, int(self.scale.get())))
        self._zoom = s
        self._big = tk.PhotoImage(width=SCREEN_W * s, height=SCREEN_H * s)
        self.canvas.itemconfigure(self._img_item, image=self._big if s > 1 else self._small)
        if not self.fullscreen:
            self.canvas.configure(width=SCREEN_W * s, height=SCREEN_H * s)
            self.root.update_idletasks()
            try:
                self.root.geometry("")
            except tk.TclError:
                pass
        self._layout()
        if self.nes:
            self._draw()
        else:
            self._blank()

    def _blank(self) -> None:
        self._small.tk.call(self._small, "put", self._ppm_header + bytes(SCREEN_W * SCREEN_H * 3),
                            "-format", "ppm")
        if self._zoom > 1:
            self._big.tk.call(self._big, "copy", self._small, "-zoom", self._zoom, self._zoom)

    def _apply_bg(self) -> None:
        colour = self.bg_color
        if self.use_bg_palette.get() and self.nes:
            r, g, b = _DISPLAY_PALETTE[self.nes.bus.ppu.palette[0] & 0x3F]
            colour = f"#{r:02x}{g:02x}{b:02x}"
        try:
            self.canvas.configure(bg=colour)
            self.root.configure(bg=colour)
        except tk.TclError:
            pass

    def choose_bg_color(self) -> None:
        from tkinter import colorchooser
        res = colorchooser.askcolor(color=self.bg_color, parent=self.root, title="BG Side Panel Color")
        if res and res[1]:
            self.bg_color = res[1]
            self._apply_bg()

    def _draw(self) -> None:
        nes = self.nes
        if not nes:
            return
        t0 = time.perf_counter()
        ppu = nes.bus.ppu
        frame = ppu.framebuffer_idx
        if self.clip_sides.get():
            frame = bytearray(frame)
            black = bytes((0x0F,)) * 8
            for y in range(SCREEN_H):
                o = y << 8
                frame[o:o + 8] = black
                frame[o + 248:o + 256] = black
        frame_to_rgb(frame, ppu.emphasis, out=self._rgb)
        self._small.tk.call(self._small, "put", self._ppm_header + self._rgb, "-format", "ppm")
        if self._zoom > 1:
            self._big.tk.call(self._big, "copy", self._small, "-zoom", self._zoom, self._zoom)
        self._update_overlays()
        self.stats["draw_ms"] = self.stats["draw_ms"] * 0.9 + (time.perf_counter() - t0) * 100.0

    def _update_overlays(self) -> None:
        nes = self.nes
        now = time.perf_counter()
        self._set_text("msg", self._osd_text if (self.show_messages.get() and now < self._osd_until) else "")
        self._set_text("fps", f"{self.stats['fps']:.1f} fps" if self.show_fps.get() else "")
        lines = []
        if nes and self.show_frame.get():
            lines.append(str(nes.frame_count))
        if nes and self.show_lag.get():
            lines.append(f"Lag: {nes.lag_count}")
        self._set_text("frame", "  ".join(lines))
        movie = ""
        if self.movie_mode and self.show_movie_status.get():
            if self.movie_mode == "play":
                movie = f"Playing {self.movie_index}/{len(self.movie_frames)}"
            else:
                movie = f"Recording {len(self.movie_frames)}"
        self._set_text("movie", movie)
        if nes and self.show_input.get():
            st = nes.bus.controller_state[0]
            self._set_text("input", "".join(ch if st & (1 << b) else "." for ch, b in zip(
                "RLDUTSBA", (7, 6, 5, 4, 3, 2, 1, 0))))
        else:
            self._set_text("input", "")
        if self.use_bg_palette.get():
            self._apply_bg()

    def osd(self, text: str, seconds: float = 2.0) -> None:
        self._osd_text = text
        self._osd_until = time.perf_counter() + seconds
        self.log(text)
        if not self.running or self.paused:
            self._update_overlays()

    def log(self, text: str) -> None:
        stamp = time.strftime("%H:%M:%S")
        self.messages.append(f"[{stamp}] {text}")
        if len(self.messages) > 2000:
            del self.messages[:500]

    # ============================================================== input
    @staticmethod
    def _mods(state: int) -> tuple:
        shift = bool(state & 0x1)
        ctrl = bool(state & 0x4)
        if sys.platform == "darwin":
            alt = bool(state & 0x10)
            ctrl = ctrl or bool(state & 0x8)        # Command acts as Ctrl
        elif sys.platform.startswith("win"):
            alt = bool(state & 0x20000)
        else:
            alt = bool(state & 0x8)
        return ctrl, shift, alt

    @staticmethod
    def chord_from_event(event) -> str:
        ctrl, shift, alt = EmulatorGUI._mods(event.state)
        sym = event.keysym
        if len(sym) == 1:
            sym = sym.lower()
        shifted = {"exclam": "1", "at": "2", "numbersign": "3", "dollar": "4", "percent": "5",
                   "asciicircum": "6", "ampersand": "7", "asterisk": "8", "parenleft": "9",
                   "parenright": "0", "question": "slash", "plus": "equal", "underscore": "minus",
                   "bar": "backslash", "less": "comma", "greater": "period"}
        if shift and sym in shifted:
            sym = shifted[sym]
        if sym == "ISO_Left_Tab":
            sym = "Tab"
        parts = []
        if ctrl:
            parts.append("Ctrl")
        if shift:
            parts.append("Shift")
        if alt:
            parts.append("Alt")
        return "+".join(parts + [sym])

    def rebuild_key_maps(self) -> None:
        self.hotkey_map = {chord: name for name, chord in self.hotkeys.items() if chord}
        pad = {}
        for port in range(2):
            for name, sym in self.pad_keys[port].items():
                if sym:
                    pad.setdefault(sym, []).append((port, name))
        self.pad_map = pad
        self.turbo_chord = self.hotkeys.get("Turbo", "")

    def _event_in_main(self, event) -> bool:
        try:
            return event.widget.winfo_toplevel() is self.root
        except (AttributeError, tk.TclError, KeyError):
            return False

    def _on_key_press(self, event) -> Optional[str]:
        if not self._alive or not self._event_in_main(event):
            return None
        chord = self.chord_from_event(event)
        action = self.hotkey_map.get(chord)
        sym = event.keysym if len(event.keysym) > 1 else event.keysym.lower()
        if action:
            self.do_hotkey(action)
            return "break"
        if sym in self.pad_map:
            self._pressed.add(sym)
            return "break"
        return None

    def _on_key_release(self, event) -> None:
        sym = event.keysym if len(event.keysym) > 1 else event.keysym.lower()
        self._pressed.discard(sym)
        if self.turbo_hold and self.turbo_chord and sym == self.turbo_chord.split("+")[-1]:
            self.turbo_hold = False

    def _set_focus(self, focused: bool) -> None:
        self._focused = focused
        if not focused:
            self._pressed.clear()
            self.turbo_hold = False

    def do_hotkey(self, action: str) -> None:
        table = {
            "Open ROM": self.open_rom_dialog, "Close ROM": self.close_rom,
            "Screenshot": self.screenshot, "Soft Reset": self.soft_reset,
            "Hard Reset": self.hard_reset, "Power": self.power, "Pause": self.toggle_pause,
            "Quit": self.quit, "Hide Menu": self.toggle_menu, "Fullscreen": self.toggle_fullscreen,
            "Save State": self.quick_save, "Load State": self.quick_load,
            "Decrease Speed": self.slow_down, "Increase Speed": self.speed_up,
            "Frame Advance": self.frame_advance,
            "Toggle Input Display": lambda: self._toggle_var(self.show_input, "Input display"),
            "Toggle Lag Counter Display": lambda: self._toggle_var(self.show_lag, "Lag counter"),
            "Toggle Frame Display": lambda: self._toggle_var(self.show_frame, "Frame counter"),
            "Toggle Movie Read-Only": self.toggle_movie_readonly,
            "Mute": self.toggle_mute,
        }
        if action == "Turbo":
            self.turbo_hold = True
            return
        if action.startswith("Save State Slot "):
            self.quick_save(int(action[-1]))
            return
        if action.startswith("Load State Slot "):
            self.quick_load(int(action[-1]))
            return
        if action.startswith("Select State Slot "):
            self.select_slot(int(action[-1]))
            return
        fn = table.get(action)
        if fn:
            fn()

    def _toggle_var(self, var, label: str) -> None:
        var.set(not var.get())
        self.osd(f"{label} {'on' if var.get() else 'off'}")

    def _apply_input(self) -> None:
        nes = self.nes
        state = [0, 0]
        pressed = self._pressed
        turbo_on, turbo_off = AUTOFIRE_PATTERNS[self.autofire.get() % len(AUTOFIRE_PATTERNS)]
        turbo_phase = (nes.frame_count % (turbo_on + turbo_off)) < turbo_on
        for sym in pressed:
            for port, name in self.pad_map.get(sym, ()):
                if name == "Turbo A":
                    if turbo_phase:
                        state[port] |= 1
                elif name == "Turbo B":
                    if turbo_phase:
                        state[port] |= 2
                else:
                    state[port] |= 1 << NES_BUTTONS.index(name)
        for port in range(2):          # no opposing directions (FCEUX default)
            if state[port] & 0x30 == 0x30:
                state[port] &= ~0x30
            if state[port] & 0xC0 == 0xC0:
                state[port] &= ~0xC0
        if self.movie_mode == "play":
            if self.movie_index < len(self.movie_frames):
                cmd, p0, p1 = self.movie_frames[self.movie_index]
                self.movie_index += 1
                if cmd & 1:
                    nes.reset()
                elif cmd & 2:
                    nes.power()
                state = [p0, p1]
            else:
                self.movie_mode = None
                self.osd("Movie finished")
        elif self.movie_mode == "record":
            self.movie_frames.append((0, state[0], state[1]))
        nes.bus.controller_state[0] = state[0]
        nes.bus.controller_state[1] = state[1]

    # =========================================================== main loop
    def target_fps(self) -> float:
        base = REGIONS[self.region.get()][4]
        return base * self.speed_pct / 100.0

    def speed_label(self) -> str:
        if self.turbo_mode or self.turbo_hold:
            return "Turbo"
        if self.speed_pct == 100.0:
            return "100% (Famicom speed)" if self.region.get() == "NTSC" else "100%"
        return f"{self.speed_pct:g}%"

    def _loop(self) -> None:
        if not self._alive:
            return
        delay = 16
        try:
            delay = self._tick()
        except Exception as exc:  # keep the window alive, surface core errors
            self._runtime_error(exc)
        if self._alive:
            self._after = self.root.after(max(1, min(int(delay), 33)), self._loop)

    def _active(self) -> bool:
        if not (self.nes and self.running) or self.paused:
            return False
        if self.debug_hooks and self.debug_hooks.halted:
            return False
        if self.pause_on_focus_loss.get() and not self._focused:
            return False
        return True

    def _tick(self) -> int:
        now = time.perf_counter()
        if not self._active():
            self._next = now
            if now < self._osd_until + 0.1:
                self._update_overlays()
            if self.tools and now - self._last_tool_refresh > 0.25:
                self._last_tool_refresh = now
                for tool in list(self.tools.values()):
                    if tool.alive() and tool.refresh_every < 1000:
                        try:
                            tool.refresh()
                        except tk.TclError:
                            pass
            return 16
        turbo = self.turbo_mode or self.turbo_hold
        ran = 0
        if turbo:
            budget = now + 0.016
            while time.perf_counter() < budget and ran < 30:
                if not self._emulate_frame(audio=False):
                    break
                ran += 1
            self._next = time.perf_counter()
            self._draw()
        else:
            period = 1.0 / max(0.5, self.target_fps())
            if now + 0.0008 >= self._next:
                max_frames = 4 if self.allow_frameskip.get() else 1
                while True:
                    if not self._emulate_frame(audio=True):
                        break
                    ran += 1
                    self._next += period
                    if time.perf_counter() + 0.0008 < self._next or ran >= max_frames:
                        break
                if ran > 1:
                    self.stats["skipped"] += ran - 1
                if time.perf_counter() - self._next > 0.25:
                    self._next = time.perf_counter() + period
                if (self.audio_sync.get() and self.speed_pct == 100.0 and self.audio.available
                        and not self.muted.get()):
                    level = self.audio.level_ms()
                    if level > 110.0:
                        self._next += period * 0.5
                    elif level > 75.0:
                        self._next += period * 0.08
                    elif level < 30.0:
                        self._next -= period * 0.08
                self._draw()
        if ran:
            self._fps_n += ran
            self._frames += ran
            self._refresh_tools()
        elapsed = now - self._fps_t
        if elapsed >= 1.0:
            self.stats["fps"] = self._fps_n / elapsed
            self._fps_n = 0
            self._fps_t = now
        if self._break_pc is not None:
            pc, self._break_pc = self._break_pc, None
            self._on_breakpoint(pc)
        if turbo:
            return 1
        return max(1, int((self._next - time.perf_counter()) * 1000.0))

    def _emulate_frame(self, audio: bool) -> bool:
        nes = self.nes
        self._apply_input()
        t0 = time.perf_counter()
        done = nes.run_frame()
        self.stats["emu_ms"] = self.stats["emu_ms"] * 0.9 + (time.perf_counter() - t0) * 100.0
        if not done:
            return False
        pcm = nes.bus.apu.drain_samples()
        if self.wav is not None:
            self.wav.write(pcm)
        if audio:
            self.audio.submit(pcm)
        if self.state_recorder.get() and nes.frame_count % max(1, self.recorder_interval.get()) == 0:
            depth = max(2, self.recorder_depth.get())
            if self.recorder.maxlen != depth:
                self.recorder = collections.deque(self.recorder, maxlen=depth)
            self.recorder.append(nes.save_state())
        return True

    def _refresh_tools(self) -> None:
        if not self.tools:
            return
        for tool in list(self.tools.values()):
            if not tool.alive():
                self.tools.pop(tool.key, None)
                continue
            if self._frames % tool.refresh_every == 0:
                try:
                    tool.refresh()
                except tk.TclError:
                    pass

    def open_tool(self, cls) -> ToolWindow:
        tool = self.tools.get(cls.key)
        if tool is not None and tool.alive():
            tool.lift()
            return tool
        tool = cls(self)
        self.tools[cls.key] = tool
        return tool

    def _runtime_error(self, exc: Exception) -> None:
        self.paused = True
        self.log(f"Error: {exc!r}")
        self.osd(f"Error: {exc}", 5.0)
        if self._alive:
            messagebox.showerror(APP_TITLE, f"{type(exc).__name__}: {exc}", parent=self.root)

    # ======================================================= file actions
    def open_rom_dialog(self) -> None:
        path = filedialog.askopenfilename(
            parent=self.root, title="Open ROM",
            filetypes=(("NES ROMs", ("*.nes", "*.NES", "*.zip", "*.ZIP", "*.unf")),
                       ("All files", "*.*")))
        if path:
            self.load_rom(path)

    @staticmethod
    def _read_rom_image(path: pathlib.Path) -> tuple[bytes, str]:
        if path.suffix.lower() == ".zip":
            import zipfile
            with zipfile.ZipFile(path) as zf:
                names = [n for n in zf.namelist() if n.lower().endswith(".nes")] or zf.namelist()
                if not names:
                    raise CartridgeError("The zip archive is empty.")
                return zf.read(names[0]), names[0]
        return path.read_bytes(), path.name

    def load_rom(self, path: str) -> None:
        self._remember_resume()
        self._save_battery()
        rom = pathlib.Path(path)
        try:
            image, inner = self._read_rom_image(rom)
            cart = Cartridge(image, str(rom))
            if cart.battery:
                cart.battery_path = rom.with_suffix(".sav")
                cart.load_battery()
            nes = NES(cart, region=self.region.get(), ram_init=self.ram_init.get())
        except (OSError, CartridgeError, ValueError) as exc:
            self.log(f"Failed to load {rom.name}: {exc}")
            messagebox.showerror(APP_TITLE, f"Error loading {rom.name}:\n\n{exc}", parent=self.root)
            return
        self.nes = nes
        self.rom_path = rom
        self.running = True
        self.paused = False
        self.movie_mode = None
        self.recorder.clear()
        self.audio.clear()
        self.apply_sound_settings()
        self.apply_cheats()
        if self.debug_hooks:
            self.debug_hooks.halted = False
            nes.set_debug(self.debug_hooks)
        self._next = time.perf_counter()
        if rom in self.recent:
            self.recent.remove(rom)
        self.recent.insert(0, rom)
        del self.recent[self.MAX_RECENT:]
        self._refresh_recent_menu()
        mapper_doc = (type(cart.mapper).__doc__ or "").strip().split("\n")[0]
        self.log(f"Loaded {inner}: mapper {cart.mapper_id} {mapper_doc} | PRG {cart.prg_len // 1024}K "
                 f"CHR {'RAM' if cart.chr_is_ram else 'ROM'} {cart.chr_len // 1024}K | "
                 f"{cart.header_mirroring} | battery {'yes' if cart.battery else 'no'}")
        if self.auto_resume.get() and str(rom) in self.resume_states:
            try:
                nes.load_state(self.resume_states[str(rom)])
                self.osd("Resumed")
            except (ValueError, pickle.UnpicklingError) as exc:
                self.log(f"Auto-resume failed: {exc}")
        else:
            self.osd(inner)
        self._apply_bg()
        for tool in list(self.tools.values()):
            if tool.alive():
                tool.refresh()

    def _remember_resume(self) -> None:
        if self.nes and self.rom_path and self.auto_resume.get():
            try:
                self.resume_states[str(self.rom_path)] = self.nes.save_state()
            except Exception as exc:  # noqa: BLE001
                self.log(f"Auto-resume save failed: {exc}")

    def _save_battery(self) -> None:
        if self.nes:
            try:
                self.nes.cart.save_battery()
            except Exception as exc:  # noqa: BLE001
                self.log(f"Battery save failed: {exc}")

    def close_rom(self) -> None:
        if not self.nes:
            return
        self._remember_resume()
        self._save_battery()
        self.movie_stop(quiet=True)
        self.nes = None
        self.rom_path = None
        self.running = False
        self.audio.clear()
        self._blank()
        self.osd("ROM closed")

    def quit(self) -> None:
        if not self._alive:
            return
        self._save_battery()
        self.movie_stop(quiet=True)
        self.wav_stop(quiet=True)
        self._alive = False
        try:
            self.root.after_cancel(self._after)
        except (tk.TclError, AttributeError):
            pass
        for tool in list(self.tools.values()):
            try:
                tool.top.destroy()
            except tk.TclError:
                pass
        self.audio.close()
        try:
            self.root.destroy()
        except tk.TclError:
            pass

    # ------------------------------------------------------------ states
    def select_slot(self, slot: int) -> None:
        self.state_slot.set(slot)
        self.osd(f"State {slot} selected" + ("" if slot in self.state_slots else " (empty)"))

    def quick_save(self, slot: Optional[int] = None) -> None:
        if not self.nes:
            return
        slot = self.state_slot.get() if slot is None else slot
        self.state_slots[slot] = self.nes.save_state()
        self.osd(f"State {slot} saved")

    def quick_load(self, slot: Optional[int] = None) -> None:
        if not self.nes:
            return
        slot = self.state_slot.get() if slot is None else slot
        blob = self.state_slots.get(slot)
        if blob is None:
            self.osd(f"State {slot} is empty")
            return
        self._load_state_blob(blob, f"State {slot} loaded")

    def _load_state_blob(self, blob: bytes, message: str) -> None:
        try:
            self.nes.load_state(blob)
        except (ValueError, pickle.UnpicklingError, zlib.error, KeyError) as exc:
            self.osd(f"Error loading state: {exc}")
            return
        if self.movie_mode == "record" or (self.movie_mode == "play" and not self.movie_readonly.get()):
            self.movie_mode = "record"
            del self.movie_frames[self.nes.frame_count:]
        self.audio.clear()
        self._draw()
        self.osd(message)

    def save_state_as(self) -> None:
        if not self.nes:
            return
        stem = self.rom_path.stem if self.rom_path else "state"
        path = filedialog.asksaveasfilename(parent=self.root, title="Save State As",
                                            initialfile=f"{stem}.acs", defaultextension=".acs",
                                            filetypes=(("acnesemu save state", "*.acs"), ("All files", "*.*")))
        if path:
            pathlib.Path(path).write_bytes(self.nes.save_state())
            self.osd(f"State saved to {pathlib.Path(path).name}")

    def load_state_from(self) -> None:
        if not self.nes:
            return
        path = filedialog.askopenfilename(parent=self.root, title="Load State From",
                                          filetypes=(("acnesemu save state", "*.acs"), ("All files", "*.*")))
        if path:
            self._load_state_blob(pathlib.Path(path).read_bytes(), f"State loaded from {pathlib.Path(path).name}")

    def recorder_load_previous(self) -> None:
        if not self.nes or not self.recorder:
            self.osd("No recorded states")
            return
        self._load_state_blob(self.recorder.pop(), "Recorded state loaded")

    # -------------------------------------------------------- screenshot
    def screenshot(self) -> None:
        if not self.nes:
            return
        base = self.rom_path.parent if self.rom_path else pathlib.Path.cwd()
        snaps = base / "snaps"
        try:
            snaps.mkdir(exist_ok=True)
            stem = self.rom_path.stem if self.rom_path else "snap"
            n = 0
            while (snaps / f"{stem}-{n}.png").exists():
                n += 1
            ppu = self.nes.bus.ppu
            rgb = frame_to_rgb(ppu.framebuffer_idx, ppu.emphasis)
            (snaps / f"{stem}-{n}.png").write_bytes(png_bytes(SCREEN_W, SCREEN_H, bytes(rgb)))
            self.osd(f"Screen snapshot {n} saved.")
        except OSError as exc:
            self.osd(f"Screenshot failed: {exc}")

    # ============================================================== movies
    def movie_record(self) -> None:
        if not self.nes:
            return
        stem = self.rom_path.stem if self.rom_path else "movie"
        path = filedialog.asksaveasfilename(parent=self.root, title="Record Movie",
                                            initialfile=f"{stem}.fm2", defaultextension=".fm2",
                                            filetypes=(("FCEUX movie", "*.fm2"),))
        if not path:
            return
        self.movie_path = path
        self.nes.power()
        self.movie_frames = []
        self.movie_mode = "record"
        self.osd("Movie recording started")

    def movie_play(self) -> None:
        if not self.nes:
            return
        path = filedialog.askopenfilename(parent=self.root, title="Play Movie",
                                          filetypes=(("FCEUX movie", "*.fm2"), ("All files", "*.*")))
        if path:
            self._start_playback(path)

    def _start_playback(self, path: str) -> None:
        frames = []
        try:
            for line in pathlib.Path(path).read_text(errors="replace").splitlines():
                if not line.startswith("|"):
                    continue
                fields = line.split("|")
                cmd = int(fields[1] or 0)
                pads = []
                for field in fields[2:4]:
                    value = 0
                    for ch, bit in zip(field[:8], (7, 6, 5, 4, 3, 2, 1, 0)):
                        if ch not in (".", " "):
                            value |= 1 << bit
                    pads.append(value)
                while len(pads) < 2:
                    pads.append(0)
                frames.append((cmd, pads[0], pads[1]))
        except (OSError, ValueError) as exc:
            self.osd(f"Movie load failed: {exc}")
            return
        self.movie_path = path
        self.movie_frames = frames
        self.movie_index = 0
        self.nes.power()
        self.movie_mode = "play"
        self.osd(f"Playing movie ({len(frames)} frames)")

    def movie_play_beginning(self) -> None:
        if self.movie_path and self.nes:
            if self.movie_mode == "record":
                self.movie_stop(quiet=True)
            self._start_playback(self.movie_path)

    def movie_stop(self, quiet: bool = False) -> None:
        if self.movie_mode == "record" and self.movie_path:
            self._write_fm2(self.movie_path)
            if not quiet:
                self.osd(f"Movie saved: {pathlib.Path(self.movie_path).name}")
        elif self.movie_mode == "play" and not quiet:
            self.osd("Movie stopped")
        self.movie_mode = None

    def _write_fm2(self, path: str) -> None:
        lines = ["version 3", "emuVersion 0", "rerecordCount 0",
                 f"palFlag {1 if self.region.get() == 'PAL' else 0}",
                 f"romFilename {self.rom_path.stem if self.rom_path else ''}",
                 "romChecksum base64:" + __import__("base64").b64encode(
                     __import__("hashlib").md5(self.nes.cart.prg).digest()).decode(),
                 "guid 00000000-0000-0000-0000-000000000000", "fourscore 0",
                 "microphone 0", "port0 1", "port1 1", "port2 0", "FDS 0", "NewPPU 0"]

        def pad(v: int) -> str:
            return "".join(ch if v & (1 << b) else "." for ch, b in zip("RLDUTSBA", (7, 6, 5, 4, 3, 2, 1, 0)))
        for cmd, p0, p1 in self.movie_frames:
            lines.append(f"|{cmd}|{pad(p0)}|{pad(p1)}||")
        pathlib.Path(path).write_text("\n".join(lines) + "\n")

    def toggle_movie_readonly(self) -> None:
        self.movie_readonly.set(not self.movie_readonly.get())
        self.osd("Movie read-only" if self.movie_readonly.get() else "Movie read+write")

    # ----------------------------------------------------------------- wav
    def wav_record(self) -> None:
        if self.wav_path:
            self._start_wav(self.wav_path)
        else:
            self.wav_record_as()

    def wav_record_as(self) -> None:
        stem = self.rom_path.stem if self.rom_path else "sound"
        path = filedialog.asksaveasfilename(parent=self.root, title="Record WAV",
                                            initialfile=f"{stem}.wav", defaultextension=".wav",
                                            filetypes=(("WAV audio", "*.wav"),))
        if path:
            self._start_wav(path)

    def _start_wav(self, path: str) -> None:
        self.wav_stop(quiet=True)
        try:
            self.wav = WavWriter(path, APU.SAMPLE_RATE)
            self.wav_path = path
            self.osd("WAV recording started")
        except OSError as exc:
            self.osd(f"WAV failed: {exc}")

    def wav_stop(self, quiet: bool = False) -> None:
        if self.wav is not None:
            self.wav.close()
            self.wav = None
            if not quiet:
                self.osd("WAV recording stopped")

    # ========================================================== emulation
    def power(self) -> None:
        if self.nes:
            self.nes.ram_init = self.ram_init.get()
            self.nes.power()
            self.audio.clear()
            self.paused = False
            self.osd("Power on")

    def hard_reset(self) -> None:
        if self.nes:
            self.nes.ram_init = self.ram_init.get()
            self.nes.power()
            self.audio.clear()
            self.paused = False
            self.osd("Hard reset")

    def soft_reset(self) -> None:
        if self.nes:
            self.nes.reset()
            self.audio.clear()
            self.paused = False
            self.osd("Soft reset")

    def toggle_pause(self) -> None:
        if not self.nes:
            return
        self.paused = not self.paused
        if self.debug_hooks and self.debug_hooks.halted and not self.paused:
            self.debug_continue()
        self.audio.clear()
        self._next = time.perf_counter()
        self.osd("Paused" if self.paused else "Running")

    def frame_advance(self) -> None:
        if not self.nes:
            return
        if not self.paused:
            self.paused = True
            self.audio.clear()
            self.osd("Paused")
            return
        if self._emulate_frame(audio=False):
            self._draw()
            self._refresh_tools()
        self.osd(f"Frame {self.nes.frame_count}", 1.0)

    def apply_region(self) -> None:
        region = self.region.get()
        if self.nes:
            self.nes.set_region(region)
        self._next = time.perf_counter()
        self.osd(f"Region: {region}")

    def toggle_mute(self) -> None:
        self.muted.set(not self.muted.get())
        self.apply_sound_settings()
        self.osd("Sound muted" if self.muted.get() else "Sound on")

    def apply_sound_settings(self) -> None:
        self.audio.muted = self.muted.get()
        if self.audio.muted:
            self.audio.clear()
        if self.nes:
            self.nes.bus.apu.set_volumes(*self.volumes)

    def apply_cheats(self) -> None:
        if not self.nes:
            return
        active = []
        for c in self.cheats:
            is_gg = ":" not in c["code"] and "?" not in c["code"]
            if is_gg and not self.game_genie.get():
                continue
            active.append(dict(c))
        self.nes.bus.set_cheats(active)

    def set_palette(self, palette: tuple, name: str) -> None:
        set_display_palette(palette)
        self.palette_name = name
        if self.nes:
            self._draw()

    # -------------------------------------------------------------- speed
    def _set_speed(self, pct: float) -> None:
        self.speed_pct = max(1.0, min(1600.0, pct))
        self.turbo_mode = False
        self._next = time.perf_counter()
        self.audio.clear()
        self.osd(f"Emulation speed {self.speed_label()}")

    def speed_up(self) -> None:
        bigger = [s for s in SPEED_STEPS if s > self.speed_pct]
        self._set_speed(bigger[0] if bigger else SPEED_STEPS[-1])

    def slow_down(self) -> None:
        smaller = [s for s in SPEED_STEPS if s < self.speed_pct]
        self._set_speed(smaller[-1] if smaller else SPEED_STEPS[0])

    def speed_slowest(self) -> None:
        self._set_speed(SPEED_STEPS[0])

    def speed_normal(self) -> None:
        self._set_speed(100.0)

    def toggle_turbo_mode(self) -> None:
        self.turbo_mode = not self.turbo_mode
        self.audio.clear()
        self.osd("Turbo on" if self.turbo_mode else "Turbo off")

    def speed_custom(self) -> None:
        value = simpledialog.askfloat("Custom Speed", "Emulation speed (% of normal, 1-1600):",
                                      parent=self.root, minvalue=1.0, maxvalue=1600.0,
                                      initialvalue=self.speed_pct)
        if value:
            self._set_speed(value)

    def set_frame_advance_delay(self) -> None:
        value = simpledialog.askinteger("Frame Advance Delay", "Frame advance delay (frames):",
                                        parent=self.root, minvalue=0, maxvalue=1000,
                                        initialvalue=self.frame_advance_delay)
        if value is not None:
            self.frame_advance_delay = value

    # ------------------------------------------------------------ window
    def toggle_fullscreen(self) -> None:
        self.fullscreen = not self.fullscreen
        try:
            self.root.attributes("-fullscreen", self.fullscreen)
        except tk.TclError:
            self.fullscreen = False
            return
        if self.fullscreen:
            self.root.update_idletasks()
            sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
            self._saved_scale = self.scale.get()
            self.scale.set(max(1, min(4, sh // SCREEN_H, sw // SCREEN_W)))
            if self.auto_hide_menu_fs.get() and not self.menu_hidden:
                self.toggle_menu()
        else:
            self.scale.set(getattr(self, "_saved_scale", 2))
            if self.menu_hidden and self.auto_hide_menu_fs.get():
                self.toggle_menu()
        self.apply_scale()

    def toggle_menu(self) -> None:
        try:
            if self.menu_hidden:
                self.root.config(menu=self.menubar)
            else:
                self.root.config(menu="")
            self.menu_hidden = not self.menu_hidden
        except tk.TclError:
            pass

    # ========================================================== debugging
    def ensure_debug_hooks(self) -> DebugHooks:
        if self.debug_hooks is None:
            hooks = DebugHooks()
            hooks.on_break = self._break_cb
            self.debug_hooks = hooks
            if self.nes:
                self.nes.set_debug(hooks)
        return self.debug_hooks

    def maybe_release_debug_hooks(self) -> None:
        h = self.debug_hooks
        if h and not h.breakpoints and h.trace is None and not h.halted:
            self.debug_hooks = None
            if self.nes:
                self.nes.set_debug(None)

    def _break_cb(self, pc: int) -> None:
        self._break_pc = pc

    def _on_breakpoint(self, pc: int) -> None:
        if pc in self._temp_breaks:
            self.debug_hooks.breakpoints -= self._temp_breaks
            self._temp_breaks.clear()
        self.audio.clear()
        self.osd(f"Breakpoint hit at ${pc:04X}")
        dbg = self.open_tool(DebuggerWindow)
        dbg.refresh()
        self._draw()

    def debug_break(self) -> None:
        h = self.ensure_debug_hooks()
        h.halted = True
        self.osd("Emulation halted (debugger)")
        self.root.after(50, lambda: self.tools.get("debugger") and self.tools["debugger"].refresh())

    def debug_continue(self) -> None:
        h = self.debug_hooks
        if h:
            h.halted = False
            h.skip_once = True
        self.paused = False
        self._next = time.perf_counter()
        self.maybe_release_debug_hooks()

    def debug_step(self) -> None:
        if not self.nes:
            return
        h = self.ensure_debug_hooks()
        if not h.halted:
            h.halted = True
            self.paused = False
        self.nes.step_instruction()
        h.skip_once = True
        for tool in list(self.tools.values()):
            if tool.alive():
                tool.refresh()

    def debug_run_to(self, addr: int) -> None:
        h = self.ensure_debug_hooks()
        if addr not in h.breakpoints:
            self._temp_breaks.add(addr)
            h.breakpoints.add(addr)
        self.debug_continue()

    # ============================================================== about
    def show_about(self) -> None:
        mappers = ", ".join(str(n) for n in sorted(MAPPERS))
        messagebox.showinfo(
            "About acnesemu",
            f"{APP_TITLE}\nby {APP_AUTHOR}\n\n"
            "NES / Famicom emulator in a single Python file.\n"
            f"Normal speed = Famicom NTSC {NTSC_FPS:.4f} fps.\n\n"
            f"Mappers ({len(MAPPERS)}): {mappers}\n\n"
            "Front end modelled on the FCEUX 2.6 console window.\n"
            "Original clean-room code; not affiliated with FCEUX.\n"
            "No ROMs or BIOS files are included.",
            parent=self.root)

    def show_about_tk(self) -> None:
        messagebox.showinfo(
            "About Tk",
            f"Tcl/Tk {self.root.tk.call('info', 'patchlevel')}\n"
            f"Python {sys.version.split()[0]}\n"
            f"Audio backend: {self.audio.backend}",
            parent=self.root)


def run_benchmark(path: str, frames: int = 600) -> int:
    """Headless speed test: emulate `frames` frames and report the rate."""
    nes = NES(Cartridge.from_file(path))
    for _ in range(60):
        nes.run_frame()
    t0 = time.perf_counter()
    for _ in range(frames):
        nes.run_frame()
        nes.bus.apu.drain_samples()
    dt = time.perf_counter() - t0
    fps = frames / dt
    print(f"{pathlib.Path(path).name}: {fps:.1f} fps emulated "
          f"({fps / NTSC_FPS * 100:.0f}% of Famicom speed, {dt / frames * 1000:.2f} ms/frame)")
    return 0


# ---------------------------------------------------------------------------
# Self-test, command line
# ---------------------------------------------------------------------------
def _make_test_rom(mapper: int = 0, prg_banks: int = 1, chr_banks: int = 1) -> bytes:
    header = bytearray(16)
    header[0:4] = b"NES\x1a"
    header[4] = prg_banks & 0xFF
    header[5] = chr_banks & 0xFF
    header[6] = (mapper & 0x0F) << 4
    header[7] = mapper & 0xF0
    prg = bytearray([0xEA] * (prg_banks * 0x4000))
    # LDX #$01; INX; STX $00; JMP $8002
    prg[:8] = bytes((0xA2, 0x01, 0xE8, 0x86, 0x00, 0x4C, 0x02, 0x80))
    prg[-6:] = bytes((0x00, 0x80, 0x00, 0x80, 0x00, 0x80))
    chr_rom = bytearray(chr_banks * 0x2000) if chr_banks else bytearray()
    return bytes(header + prg + chr_rom)


def _make_render_rom() -> bytes:
    """Tiny NROM program: palette, nametable, sprite 0 over BG, NMI-driven
    scroll/OAM-DMA loop — exercises the whole frame pipeline."""
    code = bytes([
        0x78, 0xD8, 0xA2, 0xFF, 0x9A, 0xA9, 0x00, 0x8D, 0x00, 0x20, 0x8D, 0x01, 0x20,   # init
        0x2C, 0x02, 0x20, 0x10, 0xFB, 0x2C, 0x02, 0x20, 0x10, 0xFB,                     # 2x vblank
        0xA9, 0x3F, 0x8D, 0x06, 0x20, 0xA9, 0x00, 0x8D, 0x06, 0x20,                     # $3F00
        0xA2, 0x00, 0xBD, 0x80, 0x80, 0x8D, 0x07, 0x20, 0xE8, 0xE0, 0x20, 0xD0, 0xF5,   # palette
        0xA9, 0x20, 0x8D, 0x06, 0x20, 0xA9, 0x00, 0x8D, 0x06, 0x20,                     # $2000
        0xA0, 0x04, 0xA2, 0x00, 0xA9, 0x01, 0x8D, 0x07, 0x20, 0xCA, 0xD0, 0xFA,         # fill tiles=1
        0x88, 0xD0, 0xF7,
        0xA9, 0x20, 0x8D, 0x00, 0x02, 0xA9, 0x01, 0x8D, 0x01, 0x02,                     # sprite 0
        0xA9, 0x00, 0x8D, 0x02, 0x02, 0xA9, 0x30, 0x8D, 0x03, 0x02,
        0xA9, 0x80, 0x8D, 0x00, 0x20, 0xA9, 0x1E, 0x8D, 0x01, 0x20,                     # NMI + render
        0x4C, 0x65, 0x80,                                                               # spin
    ])
    nmi = bytes([
        0x48, 0xA9, 0x00, 0x8D, 0x03, 0x20, 0xA9, 0x02, 0x8D, 0x14, 0x40,               # OAM DMA
        0xE6, 0x10, 0xA5, 0x10, 0x8D, 0x05, 0x20, 0xA9, 0x00, 0x8D, 0x05, 0x20,         # scroll
        0x68, 0x40,
    ])
    prg = bytearray([0xEA] * 0x4000)
    prg[0:len(code)] = code
    prg[0x80:0xA0] = bytes([0x0F, 0x16, 0x27, 0x30] * 8)
    prg[0x100:0x100 + len(nmi)] = nmi
    prg[-6:] = bytes((0x00, 0x81, 0x00, 0x80, 0x00, 0x80))
    chr_ = bytearray(0x2000)
    chr_[0x10:0x20] = b"\xff" * 16                 # tile 1 solid colour 3
    header = bytes(b"NES\x1a" + bytes([1, 1, 0x01, 0]) + bytes(8))
    return header + bytes(prg) + bytes(chr_)


def self_test() -> int:
    assert_fceux_opcode_table()
    assert len(OPCODES) == 256 and all(ins.mode in MODE_LENGTH for ins in OPCODES)
    assert PROMPT_HELP and "opcodes" in PROMPT_HELP
    assert len(list_all_opcodes()) == 256
    assert FAMICOM_SPEED == 60 and abs(REGIONS["NTSC"][4] - NTSC_FPS) < 1e-9

    # --- CPU: tiny loop in ROM
    cart = Cartridge(_make_test_rom(), "<self-test>")
    nes = NES(cart)
    for _ in range(20):
        nes.bus.cpu.step()
    assert nes.bus.ram[0] > 1
    assert 0x8002 <= nes.bus.cpu.pc < 0x8008
    assert cart.cpu_read(0x8000) == cart.cpu_read(0xC000)
    assert nes.run_frame() is True

    # --- every opcode executes from RAM without crashing
    walk = NES(Cartridge(_make_test_rom(), "<opcode-walk>"))
    cpu = walk.bus.cpu
    for opcode in range(256):
        cpu.jammed = False
        cpu.a = cpu.x = cpu.y = 0x11
        cpu.sp = 0xFD
        cpu.p = I_FLAG | U_FLAG
        walk.bus.ram[0x200:0x204] = bytes((opcode, 0x00, 0x02, 0x02))
        cpu.pc = 0x0200
        cpu.step()

    # --- ADC / SBC / flags via the generated core
    t = NES(Cartridge(_make_test_rom(), "<flags>"))
    c = t.bus.cpu
    t.bus.ram[0x300:0x306] = bytes((0x18, 0xA9, 0x7F, 0x69, 0x01, 0x02))   # CLC; LDA #$7F; ADC #$01; KIL
    c.pc = 0x300
    for _ in range(3):
        c.step()
    assert c.a == 0x80 and c.p & V_FLAG and c.p & N_FLAG and not c.p & C_FLAG

    # --- full frame pipeline: palette, nametable, sprite-0 hit, NMI, DMA
    gfx = NES(Cartridge(_make_render_rom(), "<render>"))
    for _ in range(8):
        gfx.run_frame()
    fb = gfx.bus.ppu.framebuffer_idx
    assert fb[120 * 256 + 128] == 0x30, "background tiles should render colour $30"
    assert gfx.bus.ram[0x10] >= 4, "NMI handler should run every frame"
    assert len(gfx.bus.ppu.framebuffer) == SCREEN_W * SCREEN_H * 3

    # --- loopy registers
    lp = NES(Cartridge(_make_test_rom(), "<loopy>")).bus.ppu
    lp.write_register(0x2006, 0x20)
    lp.write_register(0x2006, 0x00)
    assert lp.address == 0x2000
    lp.write_register(0x2005, 0x7D)
    lp.write_register(0x2005, 0x5E)
    assert lp.scroll_x & 0xFF == 0x7D and lp.fine_x == 5

    # --- MMC3 clocks 240 visible lines + pre-render = 241 per frame
    mmc3 = Cartridge(_make_test_rom(4, prg_banks=2, chr_banks=2), "<mmc3>")
    mnes = NES(mmc3)
    mnes.bus.ppu.mask = 0x18
    clocks = {"n": 0}
    original = mmc3.mapper.clock_scanline

    def counting() -> None:
        clocks["n"] += 1
        original()
    mmc3.mapper.clock_scanline = counting  # type: ignore[method-assign]
    mnes.run_frame()
    mnes.bus.ppu.mask = 0x18
    clocks["n"] = 0
    mnes.run_frame()
    assert clocks["n"] == 241, clocks

    # --- MMC1 ignores the second write of a read-modify-write pair
    mmc1 = Cartridge(_make_test_rom(1, prg_banks=2, chr_banks=1), "<mmc1>")
    m1 = mmc1.mapper
    mmc1.write_cycle = 100
    assert m1.cpu_write(0x8000, 0x00)
    shift = m1.shift
    mmc1.write_cycle = 101
    m1.cpu_write(0x8000, 0x01)
    assert m1.shift == shift
    mmc1.write_cycle = 103
    m1.cpu_write(0x8000, 0x80)
    assert m1.shift == 0x10

    # --- sprite overflow + greyscale/emphasis paths
    ov = NES(Cartridge(_make_test_rom(), "<overflow>")).bus.ppu
    ov.mask = 0x1E
    for i in range(9):
        ov.oam[i * 4:i * 4 + 4] = bytes((20, 0, 0, i * 8))
    ov.spr_dirty = True
    ov.render()
    assert ov.status & 0x20
    ov.mask = 0xE1
    assert len(ov.render()) == SCREEN_W * SCREEN_H * 3

    # --- APU: pulse tone at 44.1 kHz, frame IRQ, DMC IRQ / stall
    an = NES(Cartridge(_make_test_rom(), "<apu>"))
    apu = an.bus.apu
    apu.write(0x4017, 0x40)
    apu.write(0x4015, 0x01)
    apu.write(0x4000, 0xBF)
    apu.write(0x4002, 0xFD)
    apu.write(0x4003, 0x08)
    apu.step(29_781)
    pcm = apu.drain_samples()
    assert 1_440 <= len(pcm) <= 1_500 and len(set(pcm)) > 8
    apu.write(0x4017, 0x00)
    apu.step(29_900)
    assert apu.frame_irq, "4-step sequencer must raise the frame IRQ"
    dn = NES(Cartridge(_make_test_rom(), "<dmc>"))
    dmc = dn.bus.apu
    dmc.write(0x4010, 0x8F)
    dmc.write(0x4012, 0x00)
    dmc.write(0x4013, 0x00)
    dmc.write(0x4015, 0x10)
    dmc.step(2)
    assert dmc.dmc.irq and dn.bus.cpu.stall >= 4
    assert dmc.read_status() & 0x80
    dmc.write(0x4015, 0x00)
    assert not dmc.dmc.irq

    # --- save states round-trip
    st_nes = NES(Cartridge(_make_render_rom(), "<state>"))
    for _ in range(5):
        st_nes.run_frame()
    blob = st_nes.save_state()
    for _ in range(5):
        st_nes.run_frame()
    later = bytes(st_nes.bus.ram)
    st_nes.load_state(blob)
    for _ in range(5):
        st_nes.run_frame()
    assert bytes(st_nes.bus.ram) == later, "save state replay must be deterministic"

    # --- Game Genie + cheats
    assert game_genie_decode("SXIOPO") == (0x91D9, 0xAD, None)
    for addr, val, cmp_ in ((0x91D9, 0xAD, None), (0xD1DD, 0x14, 0x05), (0x8000, 0x00, 0xFF)):
        assert game_genie_decode(game_genie_encode(addr, val, cmp_)) == (addr, val, cmp_)
    assert parse_cheat("0075:09") == (0x75, 9, None)
    ch = NES(Cartridge(_make_test_rom(), "<cheat>"))
    ch.bus.set_cheats([{"addr": 0x8000, "value": 0x60, "compare": 0xA2, "enabled": True}])
    assert ch.bus.peek(0x8000) == 0x60
    ch.bus.set_cheats([])
    assert ch.bus.peek(0x8000) == 0xA2

    # --- battery helper
    bat = Cartridge(_make_test_rom(1, prg_banks=2, chr_banks=1), "<battery>")
    bat.battery = True
    bat.prg_ram[0] = 0x5A
    bat.battery_path = pathlib.Path("_acnes_test_battery.sav")
    bat.save_battery()
    bat.prg_ram[0] = 0
    bat.load_battery()
    assert bat.prg_ram[0] == 0x5A
    bat.battery_path.unlink(missing_ok=True)

    # --- every registered mapper loads, banks, and survives a frame
    for mapper_id in sorted(MAPPERS):
        prg_banks = 16 if mapper_id in (228, 232) else 4
        chr_banks = 0 if mapper_id in MAPPER_CHR_RAM_HINT else 4
        try:
            probe = Cartridge(_make_test_rom(mapper_id, prg_banks=prg_banks, chr_banks=chr_banks),
                              f"<mapper-{mapper_id}>")
        except CartridgeError as exc:
            raise AssertionError(f"mapper {mapper_id} failed to load: {exc}") from exc
        assert probe.mapper_id == mapper_id
        pn = NES(probe)
        pn.bus.ppu.mask = 0x1E
        pn.run_frame()
        probe.mapper.clock_scanline()
        probe.mapper.clock_cpu(3)
        probe.mapper.reset()

    print(f"{APP_TITLE}: self-test passed ({len(OPCODES)} opcodes, {len(MAPPERS)} mappers, "
          f"render/APU/state/cheat checks OK)")
    return 0


def parse_args(argv: Optional[list[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=APP_TITLE + " - NES/Famicom emulator")
    parser.add_argument("rom", nargs="?", help="optional .nes (or .zip) ROM to open")
    parser.add_argument("--self-test", action="store_true", help="test the core without opening the GUI")
    parser.add_argument("--benchmark", metavar="ROM", help="emulate 600 frames headless and report fps")
    parser.add_argument("--prompt", "-p", action="store_true",
                        help="interactive debugger prompt (opcodes/step/frame/mem)")
    parser.add_argument("--opcodes", action="store_true", help="print the 256-entry opcode map and exit")
    return parser.parse_args(argv)


def main(argv: Optional[list[str]] = None) -> int:
    args = parse_args(argv)
    if args.self_test:
        return self_test()
    if args.benchmark:
        return run_benchmark(args.benchmark)
    if args.opcodes:
        assert_fceux_opcode_table()
        print("\n".join(list_all_opcodes()))
        print(f"- {len(OPCODES)}/256 opcodes (FCEUX CycTable match)")
        return 0
    if args.prompt:
        return run_prompt(args.rom)
    if tk is None:
        print("tkinter is not available in this Python; install python3-tk (or use --prompt).")
        return 1
    root = tk.Tk()
    EmulatorGUI(root, args.rom)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

