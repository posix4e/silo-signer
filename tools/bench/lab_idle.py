#!/usr/bin/env python3
"""Whether a regtest build that has gone dark is still listening: tools/bench/lab_idle.py [seconds to wait]

A regtest image's panel goes dark after about a minute left alone, and from then on its processor sleeps
between looks at the cable (`wfe`, woken by the timer's event stream). If that sleep did not end, the phone
would answer nothing. This waits for the panel to be dark, then times pings, which do not light it. Leave the
phone untouched while it runs, and look at the panel: it should go black and stay black.

Run it first on an image with no key in it. A phone that stops answering has to be switched off by holding
its buttons, and that loses whatever key it held.
"""
import os, subprocess, sys, time

USB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "build", "tricorder-usb")


def ping():
    t0 = time.time()
    out = subprocess.run([USB, "ping"], capture_output=True, text=True, timeout=10)
    return out.returncode == 0 and "TRICORDER" in out.stdout, (time.time() - t0) * 1000


def timed(n):
    times = []
    for _ in range(n):
        ok, ms = ping()
        if not ok:
            sys.exit("no answer: the phone is not listening")
        times.append(ms)
        time.sleep(0.2)
    times.sort()
    return times[len(times) // 2], times[-1]


if __name__ == "__main__":
    wait = float(sys.argv[1]) if len(sys.argv) > 1 else 75
    mid, worst = timed(20)
    print(f"lit:  ping {mid:.1f} ms median, {worst:.1f} ms worst")
    print(f"leave the phone alone for {wait:.0f} s ...")
    time.sleep(wait)
    try:
        mid, worst = timed(20)
    except subprocess.TimeoutExpired:
        sys.exit("no answer within 10 s: the sleep did not end")
    print(f"dark: ping {mid:.1f} ms median, {worst:.1f} ms worst (the panel should still be black)")
    print("now press a button: the panel should light, and that press should do nothing else")
