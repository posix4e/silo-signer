#!/usr/bin/env python3
"""Whether a regtest build that has gone dark is still listening, and what lights it.

  tools/bench/lab_idle.py              wait for dark, time pings in the dark, then light it with a host press
  tools/bench/lab_idle.py watch [s]    print the idle state every five seconds, disturbing nothing

A regtest image's panel goes dark after about a minute left alone, and from then on its processor sleeps
between looks at the cable (`wfe`, woken by the timer's event stream). If that sleep did not end, the phone
would answer nothing. The image's `lab` step `i` says whether the panel is dark, how long since a person's
press or tap and since the panel had a reason to be lit, and how many presses, taps and other stirrings it
has counted, so nothing here has to guess whether the phone was touched.

Run it first on an image with no key in it. A phone that stops answering has to be switched off by holding
its buttons, and that loses whatever key it held.
"""
import os, struct, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lab import run

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


def say(*args):
    out = subprocess.run([USB, *args], capture_output=True, text=True, timeout=10)
    return out.stdout.strip()


TICKS = 24576000


def idle():
    """(dark, seconds since a person, seconds since the screen stirred, presses, taps, stirrings)"""
    dark, person, screen, keys, taps, stirs = struct.unpack("<IQQIII", run(b"i"))
    return bool(dark), person / TICKS, screen / TICKS, keys, taps, stirs


def show(state):
    dark, person, screen, keys, taps, stirs = state
    return (f"{'dark' if dark else 'lit '}  person {person:6.1f} s ago  screen {screen:6.1f} s ago  "
            f"presses {keys} taps {taps} stirrings {stirs}")


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["watch"]:
        end = time.time() + (float(a[1]) if len(a) > 1 else 600)
        t0 = time.time()
        while time.time() < end:
            print(f"{time.time() - t0:5.0f} s  {show(idle())}  {say('status')}", flush=True)
            time.sleep(5)
        sys.exit(0)
    mid, worst = timed(20)
    print(f"lit:  ping {mid:.1f} ms median, {worst:.1f} ms worst   {show(idle())}")
    print("leave the phone alone ...")
    deadline = time.time() + 180
    while not idle()[0]:
        if time.time() > deadline:
            sys.exit(f"the panel did not go dark in three minutes: {show(idle())}")
        time.sleep(2)
    start = idle()
    try:
        mid, worst = timed(40)
    except subprocess.TimeoutExpired:
        sys.exit("no answer within 10 s: the sleep did not end")
    end = idle()
    print(f"dark: ping {mid:.1f} ms median, {worst:.1f} ms worst   {show(end)}")
    if not end[0] or end[3:] != start[3:]:
        sys.exit("the panel did not stay dark through the pings")
    before = say("status")
    woke = say("key", "prev")
    if not woke.startswith("OK: woke|") or say("status") != before or idle()[0]:
        sys.exit(f"a press on the dark panel did more than light it: {woke}")
    print("a press lit the panel and did nothing else")
    print(f"the next press was passed on: {say('key', 'prev')}")
