#!/usr/bin/env python3
"""The two chips between the USB controller and the connector, from a regtest image's own record of them.

  tools/bench/lab_chips.py                 print the record, oldest first
  tools/bench/lab_chips.py guard           read each bus's two clock gates and protocol word, and say whether
                                           the image would touch the bus (six known registers, nothing else)
  tools/bench/lab_chips.py line <text>     explain a line read off the phone's screen, e.g.
                                           "T1E0C4A09 R000A00t1 PBC #3"

When the cable is pulled and put back the signer does not come back onto USB, and its controller shows
nothing wrong. A regtest image on the Pixel reads the USB-C port controller (0x25 on hsi2c@108C0000) and
the eUSB2 repeater (0x3E on hsi2c@10C90000) once a second, keeps the last 32 states (`Kernel.UsbChips`),
shows the newest at the foot of its screen, and hands the record over with the `lab` step `c`.

The line: T = port controller's CC status, power status, role control, data switch; R = repeater's global
configuration, mode, port configuration, then t1 if its tuning is the device tree's; P = control byte of
their supply, LDO19M; # = how many states there have been. `!n:word` in place of a chip's bytes is why it
was not read: 1 its bus's serial clock is gated, 2 its bus clock is gated, 3 its block is not set to I2C,
4 its controller is in reset, 5 the register's number was not sent in time, 6 the chip did not answer,
7 no bytes came back in time; the word is the register that says so.
"""
import os, struct, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lab import run, R, words

TICKS = 24576000
WHY = {1: "serial clock gated", 2: "bus clock gated", 3: "block not set to I2C", 4: "controller in reset",
       5: "register number not sent in time", 6: "chip did not answer", 7: "no bytes back in time"}
TCPC = ["VENDOR_ID lo", "VENDOR_ID hi", "ALERT lo", "ALERT hi", "TCPC_CTRL", "ROLE_CTRL", "POWER_CTRL",
        "CC_STATUS", "POWER_STATUS", "FAULT_STATUS", "EXT_STATUS", "VND_CC_STATUS1", "VND_CC_STATUS2", "USBSW_CTRL"]
REPEATER = ["REV_ID", "GLOBAL_CONFIG", "MODE(50)", "CONFIG_PORT1", "70", "71", "72", "73", "77", "78", "79",
            "BC_STATUS_1", "INT_STATUS_1", "INT_STATUS_2"]
TUNES = bytes([0x7C, 0x3C, 0x92, 0x83, 0x00, 0x0B, 0x60])
CC = {0: "open", 1: "Ra/default", 2: "Rd/1.5A", 3: "3A"}
BUSES = {"port controller (USI5)": (0x10802090, 0x10802094, 0x10821010),
         "repeater (USI9)": (0x10C02070, 0x10C02074, 0x10C21004)}


def tcpc_words(cc, ps, rc, sw):
    """What the four bytes of the line say, by the Type-C Port Controller Interface's bit layout."""
    looking = (cc >> 5) & 1
    term = "presenting Rd" if (cc >> 4) & 1 else "presenting Rp"
    pulls = {0: "Ra", 1: "Rp", 2: "Rd", 3: "open"}
    return (f"CC1 {CC[cc & 3]}, CC2 {CC[(cc >> 2) & 3]}, {'still looking' if looking else term}; "
            f"VBUS {'present' if ps & 4 else 'absent'}{', sinking' if ps & 1 else ''}"
            f"{', sourcing' if ps & 0x10 else ''}; "
            f"role: CC1 {pulls[rc & 3]}, CC2 {pulls[(rc >> 2) & 3]}{', toggling' if rc & 0x40 else ''}; "
            f"data switch {'closed' if sw == 9 else 'open' if sw == 0 else hex(sw)}")


def repeater_words(gc, mode, cfg, tunes_ok):
    return (f"port {'disabled' if gc & 0x40 else 'enabled'} (global {gc:#04x}), mode {mode:#04x}"
            f"{'' if mode == 0x0A else ' (tree: 0x0a)'}, port config {cfg:#04x}, "
            f"tuning {'as the tree' if tunes_ok else 'NOT the tree'}")


def ldo_words(v):
    return "not read" if v > 0xFF else f"{v:#04x}: {'on' if v & 0x80 else 'OFF'}, selector {v & 0x3F:#04x}"


def chip(data, off):
    err, word = struct.unpack_from("<II", data, off)
    return err, word, data[off + 8:off + 22]


def show():
    data = run(b"c")
    now, seen, n = struct.unpack_from("<QII", data, 0)
    rows = [16 + 56 * k for k in range(n)]
    for off in reversed(rows):
        ticks, ldo = struct.unpack_from("<QI", data, off)
        print(f"{(now - ticks) / TICKS:8.1f} s ago   supply {ldo_words(ldo)}")
        for name, names, at in (("port controller", TCPC, off + 12), ("repeater", REPEATER, off + 34)):
            err, word, b = chip(data, at)
            if err:
                print(f"    {name}: not read: {WHY.get(err, err)} ({word:#010x}); before that: {b.hex()}")
                continue
            print(f"    {name}: " + "  ".join(f"{k}={v:02x}" for k, v in zip(names, b)))
            if names is TCPC:
                print("      " + tcpc_words(b[7], b[8], b[5], b[13]))
            else:
                print("      " + repeater_words(b[1], b[2], b[3], b[4:11] == TUNES))
    print(f"  {seen} states seen, {n} kept")


def guard():
    for name, (ipclk, pclk, mode) in BUSES.items():
        got = words(run(R(ipclk) + R(pclk) + R(mode)))
        ok = lambda g: bool(g & (1 << 21)) and not g & (1 << 28)
        verdict = ("serial clock gated" if not ok(got[0]) else "bus clock gated" if not ok(got[1])
                   else "not set to I2C" if got[2] & 7 != 4 else "may be touched")
        print(f"{name}: serial gate {got[0]:#010x}  bus gate {got[1]:#010x}  protocol {got[2]:#x}  -> {verdict}")


def line(text):
    for part in text.split():
        body = part[1:]
        if part[0] in "TR" and body.startswith("!"):
            why, _, word = body[1:].partition(":")
            print(f"{'port controller' if part[0] == 'T' else 'repeater'}: not read: "
                  f"{WHY.get(int(why), why)} (word {word})")
        elif part[0] == "T":
            print("port controller: " + tcpc_words(*bytes.fromhex(body[:8])))
        elif part[0] == "R":
            print("repeater: " + repeater_words(*bytes.fromhex(body[:6]), body.endswith("t1")))
        elif part[0] == "P":
            print("supply: " + ldo_words(0x100 if body == "--" else int(body, 16)))
        elif part[0] == "#":
            print(f"states seen: {body}")


if __name__ == "__main__":
    a = sys.argv[1:]
    if not a:
        show()
    elif a == ["guard"]:
        guard()
    elif a[0] == "line" and len(a) > 1:
        line(" ".join(a[1:]))
    else:
        sys.exit(__doc__)
