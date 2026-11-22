#!/usr/bin/env python3
"""Bench SPI over the lab operation: the Pixel's spi_20 (USI2_HSI0), driven register by register from the
host. Register names and bits are spi-s3c64xx's (kernel/google-modules/soc/gs)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lab import *

SPI = 0x111D0000
CH_CFG, CLK_CFG, MODE_CFG, SLAVE_SEL, INT_EN, STATUS, TX_DATA, RX_DATA, PACKET_CNT, PENDING_CLR, SWAP_CFG, FB_CLK = (SPI + 4 * k for k in range(12))
USI_CON = SPI + 0xC4
SW_CONF = 0x1102101C


def init():
    steps = W(SW_CONF, 2) + W(USI_CON, 0) + D(100)
    steps += W(SLAVE_SEL, 1) + W(INT_EN, 0) + W(CH_CFG, 0) + W(MODE_CFG, 0) + W(PACKET_CNT, 0)
    steps += W(PENDING_CLR, 0x1E) + W(PENDING_CLR, 0) + W(SWAP_CFG, 0) + W(FB_CLK, 0)
    steps += W(CH_CFG, 1 << 5) + D(50) + W(CH_CFG, 0) + W(MODE_CFG, 0x3FF << 19)
    run(steps)


def xfer(tx: bytes, hold_cs=False, wait_us=None):
    """Clock len(tx) bytes out and the same number in, with chip select held low for the whole run."""
    n = len(tx)
    assert 0 < n <= 60
    steps = W(CH_CFG, 1 << 5) + D(20) + W(CH_CFG, 0)                 # flush both FIFOs
    steps += W(MODE_CFG, 0x3FF << 19) + W(SLAVE_SEL, 0) + D(5)
    steps += W(PACKET_CNT, n | (1 << 16)) + W(CH_CFG, 0b11)          # RXCH_ON | TXCH_ON, mode 0
    for b in tx:
        steps += W(TX_DATA, b)
    steps += D(wait_us if wait_us is not None else 200 + 20 * n) + R(STATUS)
    for _ in range(n):
        steps += R(RX_DATA)
    steps += R(STATUS) + W(CH_CFG, 0) + W(PACKET_CNT, 0)
    if not hold_cs:
        steps += W(SLAVE_SEL, 1)
    got = words(run(steps))
    st0, rx, st1 = got[0], bytes(v & 0xFF for v in got[1:1 + n]), got[-1]
    return rx, st0, st1


def levels(status):
    return {"tx": (status >> 6) & 0x7F, "rx": (status >> 15) & 0x7F, "tx_done": (status >> 25) & 1}


if __name__ == "__main__":
    init()
    for wait in (0, 10, 50, 200, 2000):
        rx, a, b = xfer(bytes(16), wait_us=wait)
        print(f"wait {wait:5d}us: before reads {levels(a)}  rx={rx.hex()}  after {levels(b)}")
