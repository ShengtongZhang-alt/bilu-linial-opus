#!/usr/bin/env python3
"""Regime and counting checks for CHECK_SECS.md (high precision).

1. A-PARP (SecA/ParP.lean) at extreme points of TRegime (p = 1e6 .. 1e12, p^17 <= d^2, d up to 1e300):
   eta0 >= 3/q, s <= 2, d a^2 s^2 <= 1, 1/d <= eps <= 1/200, L/D <= 51/100 (worst case L = 1).
2. A-E6 (RegA.E6): log[p 40^p (8p)^(4k+4) 8^(k+1) d^(-k)] <= -p over the boundary of RegA
   (log d >= 400, 120 log d <= p, p^17 <= d^2), k = ceil(16 p / log d).
3. A-CNT (sum_topIdx_prod_pow_le) by brute force: multi-indices j in N^m with entries 0 or >= 2,
   grade sum_{j_i>0} (j_i - 1) = k+1; sum prod x^{j_i} <= T^{-(k+1)} (1 + x^2 T/(1 - x T))^m.
Run: /tmp/tight-venv/bin/python scripts/tight/check_secs_regime.py
"""
import itertools
import mpmath as mp

mp.mp.dps = 400


def parp(d, p):
    d, p = mp.mpf(d), mp.mpf(p)
    q = d - 1
    De = 4 / p
    R2 = 4 * q + De
    a2 = 1 / R2
    eta = (mp.sqrt(De ** 2 + 4 * q * De) - De) / (2 * q)
    ts = (1 - eta) / q
    s = (1 + q * ts) / (1 - ts)
    eps = eta / 2
    L = mp.mpf(1)
    C = 1 / d
    return dict(eta_ge=eta - 3 / q, s_le2=2 - s, dkap=1 - d * a2 * s ** 2, inv_d=eps - 1 / d,
                eps200=mp.mpf(1) / 200 - eps, LD=mp.mpf(51) / 100 - L / (1 + L - C))


def e6(logd, p):
    k = mp.ceil(16 * p / logd)
    val = mp.log(p) + p * mp.log(40) + (4 * k + 4) * mp.log(8 * p) + (k + 1) * mp.log(8) - k * logd
    return val + p  # want <= 0


def cnt(m, k, x, T):
    tot = mp.mpf(0)
    rng = range(0, k + 3)
    for j in itertools.product(rng, repeat=m):
        if any(ji == 1 for ji in j):
            continue
        if sum(ji - 1 for ji in j if ji > 0) != k + 1:
            continue
        pr = mp.mpf(1)
        for ji in j:
            pr *= mp.mpf(x) ** ji
        tot += pr
    rhs = (1 / mp.mpf(T)) ** (k + 1) * (1 + mp.mpf(x) ** 2 * T / (1 - mp.mpf(x) * T)) ** m
    return tot, rhs


def main():
    print("== A-PARP margins (all should be >= 0) ==")
    worst = {}
    for lp in (6, 7, 9, 12, 20):
        p = mp.mpf(10) ** lp
        for ld in (mp.mpf(17) / 2 * lp, 9 * lp, 15 * lp, 300):
            d = mp.mpf(10) ** ld
            if p ** 17 > d ** 2:
                continue
            for k, v in parp(d, p).items():
                if k not in worst or v < worst[k][0]:
                    worst[k] = (v, lp, float(ld))
    for k, (v, lp, ld) in worst.items():
        print(f"  {k:8s} min margin {mp.nstr(v, 5):>12s}  at p=1e{lp}, d=1e{ld:g}")
    print("== A-E6: max of log(LHS) + p over the RegA boundary (should be <= 0) ==")
    w = None
    for logd in (400, 401, 450, 600, 1000, 3000, 10 ** 4, 10 ** 6):
        logd = mp.mpf(logd)
        pmin = 120 * logd
        pmax = mp.exp(2 * logd / 17)
        for t in [i / 40 for i in range(41)]:
            p = mp.floor(pmin * (pmax / pmin) ** t)
            if p < 10 ** 6 or p < pmin:
                p = max(mp.mpf(10 ** 6), mp.ceil(pmin))
            if p > pmax:
                continue
            v = e6(logd, p)
            if w is None or v > w[0]:
                w = (v, logd, p)
    print(f"  max {mp.nstr(w[0], 6)} at log d = {mp.nstr(w[1], 6)}, p = {mp.nstr(w[2], 6)}")
    print("== A-CNT brute force (lhs <= rhs) ==")
    worst = None
    for m in (1, 2, 3):
        for k in (0, 1, 2, 3):
            for x, T in ((0.3, 1.0), (0.1, 5.0), (0.05, 10.0), (0.4, 2.0)):
                if x * T >= 1:
                    continue
                l, r = cnt(m, k, x, T)
                ratio = l / r
                if worst is None or ratio > worst[0]:
                    worst = (ratio, m, k, x, T)
    print(f"  max lhs/rhs = {mp.nstr(worst[0], 6)} at m={worst[1]}, k={worst[2]}, x={worst[3]}, T={worst[4]}")


if __name__ == "__main__":
    main()
