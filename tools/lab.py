#!/usr/bin/env python3
"""Hardware bring-up from the host, over the cable, against a regtest build of the signer.

The image answers one wire operation, `lab`, with a run of register reads, writes and waits. On signet and
mainnet builds it is refused (`Kernel.WireProofs.only_test_builds_touch_registers`). This is a bench tool:
nothing here is part of the signer.

  tools/lab.py windows                    the register windows the image may touch
  tools/lab.py r <addr> [count]           read 32-bit registers
  tools/lab.py w <addr> <value>           write one
  tools/lab.py fdt <out.dtb>              save the device tree the bootloader handed over
"""
import os, struct, subprocess, sys

USB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "build", "tricorder-usb")


class Refused(Exception):
    pass


def run(steps: bytes) -> bytes:
    """One frame of steps; what the reads returned."""
    out = subprocess.run([USB, "lab", steps.hex()], capture_output=True, text=True)
    line = (out.stdout.strip().splitlines() or [""])[-1]
    if not line.startswith("OK:"):
        body = line[4:] if line.startswith("ERR:") else ""
        try:
            said = bytes.fromhex(body).decode("utf-8", "replace")
        except ValueError:
            said = line
        raise Refused(said or out.stderr.strip() or "no answer")
    return bytes.fromhex(line[3:])


def R(addr): return b"r" + struct.pack("<Q", addr)
def W(addr, value): return b"w" + struct.pack("<QI", addr, value & 0xFFFFFFFF)
def D(micros): return b"d" + struct.pack("<I", micros)


def words(data): return list(struct.unpack("<%dI" % (len(data) // 4), data))
def read(addr): return words(run(R(addr)))[0]
def write(addr, value): run(W(addr, value))


def windows():
    data = run(b"W")
    return [struct.unpack_from("<QQ", data, i) for i in range(0, len(data), 16)]


def fdt():
    size = words(run(b"f" + struct.pack("<IH", 0, 0)))[0]
    blob = b""
    while len(blob) < size:
        blob += run(b"f" + struct.pack("<IH", len(blob), min(3900, size - len(blob))))
    return blob


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["windows"]:
        for base, size in windows():
            print(f"{base:#012x} +{size:#x}")
    elif a[:1] == ["r"] and len(a) >= 2:
        base = int(a[1], 0)
        n = int(a[2], 0) if len(a) > 2 else 1
        for i, v in enumerate(words(run(b"".join(R(base + 4 * k) for k in range(n))))):
            print(f"{base + 4 * i:#012x}: {v:08x}")
    elif a[:1] == ["w"] and len(a) == 3:
        write(int(a[1], 0), int(a[2], 0))
    elif a[:1] == ["fdt"] and len(a) == 2:
        blob = fdt()
        open(a[1], "wb").write(blob)
        print(f"{len(blob)} bytes")
    else:
        sys.exit(__doc__)
