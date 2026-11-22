#!/usr/bin/env python3
"""Bench conversation with the panel's touch controller (Synaptics TouchComm, S3908) over the lab SPI.
Framing as in the vendor driver (kernel/google-modules/touch/synaptics_touch/syna_gtd): a message is
A5, a code, a 16-bit length; its payload is read in a second cycle as A5, 03, the payload, 5A."""
import sys, os, time, struct
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lab_spi import *
import lab_pmic as P

CMU = 0x11000000
GPP1, GPN0 = 0x10840020, 0x15060000


def power_on():
    init(); write(CMU + 0x101C, 1)                                   # bus clock from the crystal: 6 MHz
    write(GPP1 + 4, read(GPP1 + 4) & ~2); write(GPP1, (read(GPP1) & ~0xF0) | 0x10)   # reset low, driven
    write(GPN0 + 8, (read(GPN0 + 8) & ~0xF) | 3)                     # pull-up on the interrupt line
    for reg, sel in ((P.L25M_CTRL, 0x2C), (P.L4M_CTRL, 0x3C)):
        v = P.pmic_read(reg)
        if v & 0x3F != sel:
            raise SystemExit(f"regulator {reg:#x} is programmed {v:#x}, not the expected voltage: not touching it")
        if not v & 0x80:
            P.pmic_update(reg, 0x80, 0x80)
    time.sleep(0.2)
    write(GPP1 + 4, read(GPP1 + 4) | 2)
    time.sleep(0.1)


def irq():
    return (read(GPN0 + 4) & 1) == 0     # active low


def spi_read(n):
    out = b""
    while len(out) < n:
        k = min(60, n - len(out))
        rx, _, _ = xfer(bytes(k), hold_cs=len(out) + k < n)
        out += rx
    return out


def spi_write(data):
    for i in range(0, len(data), 60):
        xfer(data[i:i + 60], hold_cs=i + 60 < len(data))


def read_message():
    h = spi_read(4)
    if h[0] != 0xA5:
        return None
    code, n = h[1], h[2] | (h[3] << 8)
    if n == 0:
        return code, b""
    time.sleep(0.0002)
    body = spi_read(n + 3)
    if body[0] != 0xA5 or body[1] != 0x03 or body[-1] != 0x5A:
        print("  odd continuation:", body[:2].hex(), "...", body[-1:].hex())
    return code, body[2:2 + n]


def drain(show=False):
    """Read whatever the controller has waiting. Reports (codes 0x10 and up) are returned in a list."""
    reports = []
    for _ in range(20):
        if not irq():
            break
        m = read_message()
        if m is None:
            break
        if show:
            print(f"  waiting: code {m[0]:#x} {m[1].hex()}")
        reports.append(m)
    return reports


def command(cmd, payload=b""):
    """A command and its answer: the first message that is a status (below 0x10) and not idle or busy.
    Reports that arrive meanwhile are dropped."""
    drain()
    spi_write(bytes([cmd, len(payload) & 0xFF, len(payload) >> 8]) + payload)
    for _ in range(200):
        time.sleep(0.005)
        if irq():
            m = read_message()
            if m and m[0] < 0x10 and m[0] not in (0x00, 0x02):
                return m
    return None


if __name__ == "__main__":
    if "--on" in sys.argv:
        power_on()
    else:
        init(); write(CMU + 0x101C, 1)
    code, ident = command(0x02)
    print("identify:", hex(code), "version", ident[0], "mode", ident[1], "part", ident[2:18].rstrip(b"\0"), "build", struct.unpack("<I", ident[18:22])[0], "max write", struct.unpack("<H", ident[22:24])[0])
    code, app = command(0x20)
    f = struct.unpack("<8H", app[:16])
    mx, my, objs, btns, rows, cols = struct.unpack("<6H", app[32:44])
    print("app info:", hex(code), "version", f[0], "status", f[1], "report cfg max", f[6], "payload max", f[7], "max x", mx, "max y", my, "objects", objs, "rows", rows, "cols", cols)
    code, cfg = command(0x25)
    print("touch report config:", hex(code), cfg.hex())
