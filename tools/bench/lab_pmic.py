#!/usr/bin/env python3
"""Bench access to the main PMIC (S2MPG14) through the power-management firmware's mailbox, over the lab
operation. The queue layout and the command words are acpm_ipc.c's and acpm_mfd.c's
(kernel/google-modules/soc/gs); the channel's addresses are read from the firmware's own table."""
import sys, os, time, struct
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lab import *

SRAM, MBOX = 0x15700000, 0x15110000
INTGR1, INTCR0, INTSR0 = MBOX + 0x40, MBOX + 0x24, MBOX + 0x2C
CH = 2   # the main PMIC's channel (acpm-ipc-channel in zuma-pmic.dtsi)
_seq = [int(time.time()) % 60 + 1]


def rd(addr, n=1):
    return words(run(b"".join(R(addr + 4 * k) for k in range(n))))


def channel():
    fw = rd(SRAM + 0xA000, 4)
    for i in range(fw[3]):
        e = rd(SRAM + fw[2] + 72 * i, 18)
        if e[0] == CH:
            return dict(rx_rear=SRAM + e[4], rx_front=SRAM + e[5], rx_base=SRAM + e[6], tx_rear=SRAM + e[10],
                        tx_front=SRAM + e[11], tx_base=SRAM + e[12], q_len=e[13], elem=e[14])
    raise SystemExit("no PMIC channel in the firmware's table")


def ask(cmd0, cmd1):
    """One request to the firmware, and its answer's four words."""
    c = channel()
    assert c["elem"] == 16 and 1 < c["q_len"] < 64, c
    _seq[0] = _seq[0] % 63 + 1
    seq = _seq[0]
    front, rear = rd(c["rx_front"])[0], rd(c["rx_rear"])[0]
    assert (front + 1) % c["q_len"] != rear, "the firmware's queue is full"
    slot = c["rx_base"] + 16 * front
    steps = W(slot, cmd0 | (seq << 16)) + W(slot + 4, cmd1) + W(slot + 8, 0) + W(slot + 12, 0)
    steps += W(c["rx_front"], (front + 1) % c["q_len"]) + W(INTGR1, 1 << CH)
    run(steps)
    for _ in range(50):
        time.sleep(0.005)
        t_rear, t_front = rd(c["tx_rear"])[0], rd(c["tx_front"])[0]
        i = t_rear
        while i != t_front:
            got = rd(c["tx_base"] + 16 * i, 4)
            if (got[0] >> 16) & 0x3F == seq:
                run(W(c["tx_rear"], t_front) + W(INTCR0, 1 << CH))
                return got
            i = (i + 1) % c["q_len"]
    raise SystemExit("the firmware did not answer")


def pmic_read(reg, page=0x01):
    got = ask((page << 8) | reg, 0)          # FUNC_READ
    status, value = got[1] >> 24, (got[1] >> 8) & 0xFF
    if status:
        raise SystemExit(f"read of {reg:#x} refused: status {status}")
    return value


def pmic_update(reg, value, mask, page=0x01):
    got = ask((page << 8) | reg, 2 | (value << 8) | (mask << 16))   # FUNC_UPDATE
    if got[1] >> 24:
        raise SystemExit(f"update of {reg:#x} refused: status {got[1] >> 24}")


L4M_CTRL, L25M_CTRL = 0x2E, 0x43   # touch AVDD (3.3 V) and DVDD (1.8 V)

if __name__ == "__main__":
    for name, reg, base in (("LDO4M  (touch 3.3 V)", L4M_CTRL, 1.8), ("LDO25M (touch 1.8 V)", L25M_CTRL, 0.7)):
        v = pmic_read(reg)
        print(f"{name}: {v:#04x}  enabled={v >> 7}  selector={v & 0x3F:#x} -> {base + 0.025 * (v & 0x3F):.3f} V")
