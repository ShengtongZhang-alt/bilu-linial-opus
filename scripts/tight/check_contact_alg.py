"""Adversarial sampling of the pure-algebra lemmas of BiluLinial/Tight/Contact/Real.lean with the
explicit witnesses proposed in docs/tight/CHECK_CONTACT.md:
  jr_real:        K = 2|C1| + |C2| + 9
  fs7_real:       K = 3 (1+|Cw|)^2 (1+|Cq|)
  rc3_young_real: K = 1.5 K1^2 + |K1| + 1
and the worst-case fixed point of the d6_real bootstrap.
Run: /tmp/tight-venv/bin/python scripts/tight/check_contact_alg.py
"""
import math
import random

random.seed(1)


def rnd_scale():
    return 10 ** random.uniform(-6, 3) if random.random() < 0.8 else random.choice([0.0, 1e-12, 1.0])


# ---------------------------------------------------------------- jr_real
def jr_sample(p, C1, C2, E, eps, xi):
    """Return a feasible point (or None) and the slack of the jr_real conclusion with the given K."""
    r = [random.uniform(-E, E) if random.random() < 0.7 else random.choice([-E, E]) for _ in range(4)]
    alpha = rnd_scale()
    zeta = alpha + rnd_scale()
    tcap = 1 + C1 * eps
    if tcap < 0:
        return None
    t = random.uniform(0, tcap) if random.random() < 0.7 else tcap
    q = zeta + t + r[0]
    z = zeta - alpha - r[1]
    if q < 0 or z < 0 or t > q or zeta**2 > q * z + 1e-15 * (1 + q * z):
        return None
    beta = max(0.0, random.uniform(0, alpha + C2 * xi) if random.random() < 0.6 else alpha + C2 * xi)
    tm = random.uniform(0, tcap) if random.random() < 0.6 else tcap
    zm = rnd_scale()
    zetam = beta + r[3] - zm
    qm = tm + r[2] - zetam
    if qm < 0 or zetam**2 > qm * zm + 1e-15 * (1 + qm * zm):
        return None
    P = (p - 1) * (q - t) + p * (qm - tm)
    base = (p - 1) / 2 * z + p / 2 * zm - 1 / (4 * (p - 1))
    return P, base


def jr_test(n=400000):
    worst = math.inf
    worst0 = math.inf  # E = xi = 0: exact inequality P >= base
    feasible = 0
    for _ in range(n):
        p = random.choice([2, 3, 5, 10, 100, 10**6])
        C1 = random.choice([0.0, 1.0, 5.0, -1.0])
        C2 = random.choice([0.0, 1.0, 5.0])
        exact = random.random() < 0.3
        E = 0.0 if exact else rnd_scale()
        xi = 0.0 if exact else rnd_scale()
        eps = random.uniform(0, xi)
        res = jr_sample(p, C1, C2, E, eps, xi)
        if res is None:
            continue
        feasible += 1
        P, base = res
        K = 2 * abs(C1) + abs(C2) + 9
        slack = P - (base - K * p * (E + xi))
        scale = 1 + abs(P) + abs(base)
        worst = min(worst, slack / scale)
        if exact:
            worst0 = min(worst0, (P - base) / scale)
    print(f"jr_real: {feasible} feasible samples; min relative slack with K = 2|C1|+|C2|+9: {worst:.3e};"
          f" exact case (E = xi = 0) min relative (P - base): {worst0:.3e}")


# Tight case of JR2 at E = xi = 0: alpha-hat = 1/(2(p-1)), zeta = alpha/(1-alpha), beta = alpha,
# zm = beta^2/(1+beta) attains P - base = -1/(4(p-1)) + O(1/p^2) ... check the minimum directly.
def jr_tight(p):
    best = math.inf
    for k in range(1, 4000):
        a = k / 4000 * min(1, 4 / p)
        zeta = a / (1 - a)
        t = 1.0
        q = zeta + t
        z = zeta - a
        if zeta**2 > q * z + 1e-15:
            continue
        beta = a
        tm = 1.0
        zm = beta**2 / (tm + beta)
        lam = beta / (tm + beta)
        zetam = beta - zm
        qm = tm - zetam
        if zetam**2 > qm * zm * (1 + 1e-12):
            continue
        P = (p - 1) * (q - t) + p * (qm - tm)
        base = (p - 1) / 2 * z + p / 2 * zm
        best = min(best, (P - base) * 4 * (p - 1))
    return best


# ---------------------------------------------------------------- fs7_real
def fs7_test(n=300000):
    worst = math.inf
    for _ in range(n):
        Cw = random.choice([0.0, 1.0, 10.0, -1.0])
        Cq = random.choice([0.0, 1.0, 10.0])
        e, B0, hq, bh, th = (rnd_scale() for _ in range(5))
        z, zm = rnd_scale(), rnd_scale()
        qt = random.uniform(0, Cq)
        # residual r1 = zeta - z - alpha saturating its bound
        b1 = Cw * (e * math.sqrt(z + th) + B0)
        if b1 < 0:
            continue
        r1 = random.choice([-1, 1, random.uniform(-1, 1)]) * b1
        alpha = rnd_scale()
        zeta = z + alpha + r1
        if zeta < alpha:
            continue
        b0 = Cw * (e * math.sqrt(zeta - alpha + bh * qt + th) + e * hq + B0)
        b3 = Cw * (e * math.sqrt(zm + th) + B0)
        res = [b0, b1, b0, b3]  # saturate all four
        Ec = e * math.sqrt(z) + e * math.sqrt(zm) + e**2 + B0 + e * (hq + math.sqrt(bh) + math.sqrt(th))
        K = 3 * (1 + abs(Cw)) ** 2 * (1 + abs(Cq))
        for rr in res:
            if Ec == 0:
                assert rr == 0
                continue
            worst = min(worst, (K * Ec - abs(rr)) / (K * Ec))
    print(f"fs7_real: min relative slack with K = 3(1+|Cw|)^2(1+|Cq|): {worst:.3e} (>= 0 required)")


# ---------------------------------------------------------------- rc3_young_real
def rc3_test(n=300000):
    worst = math.inf
    for _ in range(n):
        p = random.choice([2, 3, 10, 10**6])
        K1 = random.choice([0.0, 1.0, 7.0, -3.0])
        e, z, zm, E0, xi = (rnd_scale() for _ in range(5))
        P = (p - 1) / 2 * z + p / 2 * zm - 1 / (4 * (p - 1)) - K1 * p * (e * math.sqrt(z) + e * math.sqrt(zm) + E0 + xi)
        K = 1.5 * K1**2 + abs(K1) + 1
        concl = -1 / (4 * (p - 1)) - K * p * (e**2 + E0 + xi)
        worst = min(worst, (P - concl) / (1 + abs(P) + abs(concl)))
    print(f"rc3_young_real: min relative slack with K = 1.5 K1^2 + |K1| + 1: {worst:.3e}")


# ---------------------------------------------------------------- d6_real worst case
def d6_worst(p, d, C1=1.0, C4=1.0, Cw=1.0, Ca=1.0):
    q = d - 1
    D = 4 / p
    a2 = 1 / (4 * q + D)
    eta0 = (math.sqrt(D * D + 4 * q * D) - D) / (2 * q)
    eps = eta0 / 2
    vth = d ** -10.0
    dbar = eps + p**4 / d + (p / d) ** (1 / 3)
    w = Cw * p**4 / d

    p13d2 = math.exp(13 * math.log(p) - 2 * math.log(d))

    def F(lam):
        E = C1 * (p**5 * math.sqrt(lam * dbar) + p13d2 + vth)
        S = C4 * (1 + p + p**5 / d + E)
        Gt = C4 * (p + p**5 / d) + E
        W = (2 * a2 * Gt + w * vth) / (1 - w)
        A2 = 2 * W + Ca * vth
        return a2 * S + A2 + vth

    lam = 1.0
    for _ in range(500):
        lam = F(lam)
    return lam * d / p


if __name__ == "__main__":
    jr_test()
    print("jr_real tight case, min over alpha of (P - base)*4(p-1) (should be >= -1):",
          {p: round(jr_tight(p), 6) for p in [2, 3, 10, 1000]})
    fs7_test()
    rc3_test()
    for p, d in [(1e6, 1e51), (1e6, 1e120), (1e9, 10 ** 76.5), (1e30, 1e255)]:
        print(f"d6_real worst-case lambda*d/p at p={p:.0e}, d={d:.0e} (C1=C4=Cw=Ca=1): {d6_worst(p, d):.4f}")
