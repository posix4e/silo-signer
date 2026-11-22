#!/usr/bin/env python3
"""Print the touch reports the controller sends for a while: tools/lab_touch_watch.py [seconds]"""
import sys, os, time, struct
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lab_touch import *

CLASS = {0: "lift", 1: "finger", 2: "glove", 3: "stylus", 4: "eraser", 5: "small", 6: "palm", 8: "edge", 9: "hover"}


def decode(p):
    """The report as this firmware lays it out (its answer to command 0x25): eleven bytes, the last of them
    the number of objects, then twelve bytes an object."""
    out = []
    for k in range(p[10] if len(p) > 10 else 0):
        o = p[11 + 12 * k: 23 + 12 * k]
        if len(o) < 12:
            break
        x, y, z = struct.unpack_from("<HHH", o, 1)
        out.append((o[0] & 0xF, CLASS.get(o[0] >> 4, o[0] >> 4), x, y, z))
    return out


if __name__ == "__main__":
    init(); write(CMU + 0x101C, 1)
    end = time.time() + (float(sys.argv[1]) if len(sys.argv) > 1 else 30)
    n = 0
    while time.time() < end:
        if not irq():
            time.sleep(0.005); continue
        m = read_message()
        if not m:
            continue
        if m[0] == 0x11:
            n += 1
            print(f"{time.time() % 100:6.2f} touch", " ".join(f"#{i} {c} x={x / 10:.0f} y={y / 10:.0f} z={z}" for i, c, x, y, z in decode(m[1])) or m[1].hex(), flush=True)
        else:
            print(f"{time.time() % 100:6.2f} code {m[0]:#x} {m[1][:16].hex()}", flush=True)
    print("reports:", n)
