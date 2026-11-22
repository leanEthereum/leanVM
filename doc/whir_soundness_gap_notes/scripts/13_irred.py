#!/usr/bin/env python3
# Researcher 13. Lowest irreducible polynomial x^m + r(x) over F_2 for each degree m, in the same sense in which
# x^64 + x^4 + x^3 + x + 1 is the lowest one of degree 64 (r minimal as an integer). Prints "m r_hex" lines, and a
# second, different low-weight irreducible polynomial of each degree (used for the two-moduli runs).
# usage: 13_irred.py [mmin mmax]
import sys


def pmod(a, f, m):
    while a.bit_length() > m:
        a ^= f << (a.bit_length() - 1 - m)
    return a


def pmulmod(a, b, f, m):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> m & 1:
            a ^= f
    return r


def pgcd(a, b):
    while b:
        while a and a.bit_length() >= b.bit_length():
            a ^= b << (a.bit_length() - b.bit_length())
        a, b = b, a
    return a


def irreducible(f, m):
    # Rabin: x^(2^m) = x mod f and gcd(x^(2^(m/p)) - x, f) = 1 for every prime p | m
    primes = [p for p in range(2, m + 1) if m % p == 0 and all(p % q for q in range(2, p))]
    x = 2
    y = x
    powers = {}
    for i in range(1, m + 1):
        y = pmulmod(y, y, f, m)
        powers[i] = y
    if powers[m] != x:
        return False
    return all(pgcd(f, powers[m // p] ^ x) == 1 for p in primes)


def lowest(m, skip=0):
    r = 1
    while True:
        if r & 1 and irreducible((1 << m) | r, m):
            if skip == 0:
                return r
            skip -= 1
        r += 2


if __name__ == "__main__":
    lo, hi = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) == 3 else (8, 64)
    assert lowest(64) == 0x1B
    for m in range(lo, hi + 1):
        print(m, hex(lowest(m)), hex(lowest(m, 1)))
