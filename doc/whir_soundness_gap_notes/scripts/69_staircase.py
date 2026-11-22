#!/usr/bin/env python3
"""Lower bounds on the slack eps(L) that the lifted lists force on a tree code (and on Reed-Solomon on a subspace).
A top code [N = k_up/rho, k_up] with M members at block agreement a lifts to M codewords at agreement fraction
tau = a/N + (1 - a/N) rho/k_up (minus O(1/n)).  Families:
  a = k_up: M = binom(N, k_up) (proved: every k_up-subset of blocks interpolates one member);
  a > k_up: M = 1 + floor((N - a - 1)/(a - k_up)), the largest list a balanced configuration at the generalized
            Singleton value allows (assumed attained by the generic top code; checked by search at the sizes in the note).
For each list bound L: tau_L = (1 + L rho)/(L + 1) and eps(L) = max over families with M > L of tau - tau_L."""
from fractions import Fraction as Fr
from math import comb

def families(rho, kmax=1024):
    out = []
    k_up = 1
    while k_up <= kmax:
        N = int(k_up / rho)
        for a in range(k_up, N):
            if a == k_up:
                M = comb(N, k_up)
            else:
                M = 1 + (N - a - 1) // (a - k_up)
            if M < 2:
                break
            tau = Fr(a, N) + (1 - Fr(a, N)) * rho / k_up
            out.append((tau, M, k_up, a, N))
        k_up *= 2
    return out

def main():
    for rho in (Fr(1, 2), Fr(1, 4)):
        fam = families(rho)
        print(f"rate {rho}: list bound L, generalized Singleton threshold tau_L, forced slack eps(L) in units of 1/64, forcing family")
        for L in list(range(1, 17)) + [24, 32, 48, 64, 69, 70, 128]:
            tauL = (1 + L * rho) / (L + 1)
            best = max(((tau - tauL, M, k_up, a, N) for tau, M, k_up, a, N in fam if M > L), default=None)
            eps, M, k_up, a, N = best
            proved = "proved" if a == k_up else "needs a balanced top list"
            if eps <= 0:
                print(f"  L={L:3d} tau_L={float(tauL):.4f}  eps = 0 (no lifted family above tau_L)")
            else:
                print(f"  L={L:3d} tau_L={float(tauL):.4f}  eps >= {float(eps):.4f} = {float(eps) * 64:.2f}/64   top [{N},{k_up}], block agreement {a}, {M if M < 10**7 else '%.1e' % M} members at {float(eps + tauL):.4f}  ({proved})")
        print()

main()
