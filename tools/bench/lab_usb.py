#!/usr/bin/env python3
"""What the USB link has been seen to do, from a regtest image's own record of it.

  tools/bench/lab_usb.py          print the record, oldest first
  tools/bench/lab_usb.py watch    log each time the signer leaves or returns to USB, and print the record
                                  each time it returns

When the cable is pulled and put back the signer may not come back onto USB, and it cannot be asked why
while it is gone. A regtest image keeps the last 32 states of its USB controller's link (`Kernel.UsbLink`),
shows each change in its status line, and hands the record over with the `lab` step `u` once it can.

Link states: 0 on, 3 suspended, 4 no host, 5 waiting for the host, 6 polling. Speed 0 is high speed.
"""
import os, struct, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lab import run, Refused

USB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "build", "tricorder-usb")
TICKS = 24576000
LINK = {0: "on", 1: "U1", 2: "U2", 3: "suspended", 4: "no host", 5: "waiting", 6: "polling", 7: "recovery",
        8: "hot reset", 9: "compliance", 10: "loopback", 14: "reset", 15: "resume"}


def record():
    data = run(b"u")
    now, events, n = struct.unpack_from("<QII", data, 0)
    rows = [struct.unpack_from("<QIIIII", data, 16 + 28 * k) for k in range(n)]
    return now, events, rows


def show():
    now, events, rows = record()
    for ticks, dsts, dctl, ev, last, flags in reversed(rows):
        state = (dsts >> 18) & 0xF
        print(f"  {(now - ticks) / TICKS:8.1f} s ago  link {LINK.get(state, state):9}  speed {dsts & 7}"
              f"  run {dctl >> 31}  halted {(dsts >> 22) & 1}  configured {flags & 1}  gated {(flags >> 1) & 1}"
              f"  events {ev}  last {last:#010x}")
    print(f"  now: {events} events, {len(rows)} states kept")


def answers():
    try:
        out = subprocess.run([USB, "ping"], capture_output=True, text=True, timeout=5)
        return out.returncode == 0 and "TRICORDER" in out.stdout
    except subprocess.TimeoutExpired:
        return False


def watch():
    t0, last = time.time(), None
    while True:
        here = answers()
        if here != last:
            print(f"{time.time() - t0:6.0f} s  {'answers' if here else 'not on USB'}", flush=True)
            if here:
                try:
                    show()
                except Refused as e:
                    print("  no record:", e)
            last = here
        time.sleep(0.5)


if __name__ == "__main__":
    if sys.argv[1:2] == ["watch"]:
        try:
            watch()
        except KeyboardInterrupt:
            pass
    else:
        show()
