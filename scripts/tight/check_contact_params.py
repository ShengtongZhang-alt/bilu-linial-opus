"""Numerical checks of `param_facts` and `ledger_real` (BiluLinial/Tight/Contact/Real.lean) and of
the regime bounds used in the proof sketches of docs/tight/CHECK_CONTACT.md.

Parameters exactly as BiluLinial/Tight/Defs.lean: q = d-1, Delta = 4/p, R^2 = 4q + Delta, a = 1/R,
eta0 = (sqrt(Delta^2 + 4 q Delta) - Delta)/(2q), tau = (1-eta0)/q, s = (1 + q tau)/(1 - tau),
r = 1 + eta0/2, eps = r - 1, Lbar = d a^2 s^2.
Run: /tmp/tight-venv/bin/python scripts/tight/check_contact_params.py
"""
from mpmath import mp, mpf, sqrt, floor, cbrt, log10

mp.dps = 1200


def params(d, p):
    d = mpf(d); p = mpf(p)
    q = d - 1
    D = 4 / p
    Rsq = 4 * q + D
    a2 = 1 / Rsq
    eta0 = (sqrt(D**2 + 4 * q * D) - D) / (2 * q)
    tau = (1 - eta0) / q
    s = (1 + q * tau) / (1 - tau)
    r = 1 + eta0 / 2
    eps = r - 1
    Lbar = d * a2 * s**2
    return dict(d=d, p=p, q=q, a2=a2, eta0=eta0, s=s, r=r, eps=eps, Lbar=Lbar)


def param_facts(d, p):
    P = params(d, p)
    d, p, a2, eta0, s, r, eps, Lbar = (P[k] for k in ("d", "p", "a2", "eta0", "s", "r", "eps", "Lbar"))
    sq = sqrt(p * d)
    facts = [
        ("a2 <= 1/d", 1 / d - a2),
        ("1/(4d) <= a2", a2 - 1 / (4 * d)),
        ("d a2 <= 1/4 + 1/d", mpf(1) / 4 + 1 / d - d * a2),
        ("1/(2 sqrt(pd)) <= eps", eps - 1 / (2 * sq)),
        ("eps <= 1/sqrt(pd)", 1 / sq - eps),
        ("eta0 <= 2/sqrt(pd)", 2 / sq - eta0),
        ("0 <= 1 - r Lbar", 1 - r * Lbar),
        ("1/p - 2 eta0 <= d eps (1 - r Lbar)", d * eps * (1 - r * Lbar) - (1 / p - 2 * eta0)),
        ("r Lbar s^2 <= 4", 4 - r * Lbar * s**2),
        ("4 - 8 eta0 <= Lbar s^2", Lbar * s**2 - (4 - 8 * eta0)),
        ("1/2 <= Lbar", Lbar - mpf(1) / 2),
        ("Lbar <= 2", 2 - Lbar),
        ("s^2 <= 5", 5 - s**2),
    ]
    return facts, P


def regime_ok(d, p):
    return 10**6 <= p and p**17 <= d**2


def min_d(p):
    # smallest d with p^17 <= d^2
    d = int(floor(mpf(p) ** (mpf(17) / 2)))
    while d * d < p**17:
        d += 1
    while (d - 1) ** 2 >= p**17:
        d -= 1
    return d


print("=== param_facts: margins (should all be > 0), relative to the natural scale ===")
cases = []
for p in [10**6, 10**7, 10**9, 10**15, 10**30]:
    cases.append((min_d(p), p))
for d in [10**60, 10**100, 10**200, 10**300, 10**600]:
    for p in [10**6, int(floor(mpf(d) ** (mpf(2) / 17)))]:
        if regime_ok(d, p):
            cases.append((d, p))
worst = {}
for d, p in cases:
    assert regime_ok(d, p)
    facts, P = param_facts(d, p)
    for name, m in facts:
        ok = m > 0
        if not ok:
            print(f"  FAIL {name} at d=1e{float(log10(d)):.1f}, p=1e{float(log10(p)):.1f}: margin {mp.nstr(m, 5)}")
        worst.setdefault(name, []).append(m)
    # drift reserve detail: (d eps (1-rLbar) - 1/p)/eta0  -> about -1.5
    dr = (P["d"] * P["eps"] * (1 - P["r"] * P["Lbar"]) - 1 / P["p"]) / P["eta0"]
    print(f"  d=1e{float(log10(d)):6.1f} p=1e{float(log10(p)):5.1f}: (drift - 1/p)/eta0 = {mp.nstr(dr, 8)},"
          f" (r Lbar s^2 - 4)/eta0 = {mp.nstr((P['r']*P['Lbar']*P['s']**2-4)/P['eta0'], 6)}")
print("  all 13 facts hold in all", len(cases), "cases:", all(all(m > 0 for m in v) for v in worst.values()))

print("\n=== regime bounds used in the sketches (TRegime only) ===")
for d, p in cases:
    P = params(d, p)
    d_, p_ = P["d"], P["p"]
    dbar = P["eps"] + p_**4 / d_ + cbrt(p_ / d_)
    Gam = p_**4 * sqrt(p_ * dbar / d_)
    chk = [
        ("dbar <= 3 (p/d)^(1/3)", 3 * cbrt(p_ / d_) - dbar),
        ("p^3 dbar <= p (D4)", p_ - p_**3 * dbar),
        ("p^9 dbar <= 3 d (D6)", 3 * d_ - p_**9 * dbar),
        ("Gam <= sqrt(3)/p (D7, D9b)", sqrt(3) / p_ - Gam),
        ("eps_s <= p^(-11/4)", p_ ** (-mpf(11) / 4) - p_ * sqrt(p_) / sqrt(d_)),
        ("16 d a^2 in [4, 5]", min(16 * d_ * P["a2"] - 4, 5 - 16 * d_ * P["a2"])),
    ]
    bad = [n for n, m in chk if not m >= 0]
    print(f"  d=1e{float(log10(d)):6.1f} p=1e{float(log10(p)):5.1f}: {'OK' if not bad else 'FAIL ' + str(bad)}")

print("\n=== ledger_real: TotErr summands at p = floor(c0 d^(2/17)), h = k0 p^-4 ===")


def toterr_terms(d, p, h):
    P = params(d, p)
    d_, p_, eps, eta0 = P["d"], P["p"], P["eps"], P["eta0"]
    h = mpf(h)
    vth = d_ ** -10
    th = d_ ** -2
    dbar = eps + p_**4 / d_ + cbrt(p_ / d_)
    Gam = p_**4 * sqrt(p_ * dbar / d_)
    e = sqrt(p_ * dbar) / (sqrt(d_) * h)
    B0 = p_ / (d_ * h) + 1 / (d_ * h * sqrt(h)) + vth
    epsS = p_ * sqrt(p_) / sqrt(d_)
    xi = sqrt(h) + (sqrt(eps / p_ + eps**2 + p_ / d_) + epsS + eta0 + 1 / d_) + sqrt(eps / p_ + eps**2) + eps + 1 / d_
    epsBL = vth * (p_**5 + p_**2 / h) + vth
    T = {
        "Gam": Gam, "Gam^2": Gam**2, "eps_s": epsS, "eta0": eta0, "1/d": 1 / d_,
        "p^13/d^2": p_**13 / d_**2, "vth": vth, "p^5/d": p_**5 / d_, "p^2/(dh)": p_**2 / (d_ * h),
        "p/(dh^1.5)": p_ / (d_ * h * sqrt(h)), "epsBL": epsBL,
        "p e^2": p_ * e**2, "p B0": p_ * B0, "p e h^.75": p_ * e * h ** (mpf(3) / 4),
        "p e/sqrt(dh)": p_ * e / sqrt(d_ * h), "p e sqrt(th)": p_ * e * sqrt(th),
        "p xi": p_ * xi, "p sqrt(h)": p_ * sqrt(h), "p^3 sqrt(p dbar/d)": p_**3 * sqrt(p_ * dbar / d_),
    }
    return T, P


for c0, k0 in [(mpf(1), mpf(1)), (mpf("0.01"), mpf("1e-6"))]:
    print(f"  c0 = {mp.nstr(c0,3)}, kappa0 = {mp.nstr(k0,3)}")
    for logd in [20, 51, 80, 150, 300]:
        d = mpf(10) ** logd
        p = int(floor(c0 * d ** (mpf(2) / 17)))
        if p < 3:
            continue
        h = k0 / mpf(p) ** 4
        T, P = toterr_terms(d, p, h)
        pm = mpf(p)
        tot = sum(T.values())
        crit = {"p sqrt(h)*p/sqrt(k0)": T["p sqrt(h)"] * pm / sqrt(k0),
                "Gam*p/c0^(17/3)": T["Gam"] * pm / c0 ** (mpf(17) / 3),
                "pe^2*p*k0^2/c0^(34/3)": T["p e^2"] * pm * k0**2 / c0 ** (mpf(34) / 3)}
        critsum = 2 * sqrt(k0) + c0 ** (mpf(17) / 3) + k0**-2 * c0 ** (mpf(34) / 3)
        rest = tot - 2 * T["p sqrt(h)"] - T["Gam"] - T["p e^2"]
        print(f"    d=1e{logd:3d} p={mp.nstr(pm,6):>10} reg={regime_ok(int(d), p)}: " +
              ", ".join(f"{k}={mp.nstr(v,5)}" for k, v in crit.items()) +
              f"; rest*p^1.5*k0^1.5 = {mp.nstr(rest * pm**1.5 * k0**1.5, 4)}"
              f"; p*TotErr/critsum = {mp.nstr(pm * tot / critsum, 5)}")

print("\n  margin at K = 1 with Ccrit = 24(|K|+1) = 48 and ledger_choice witnesses:")
K = mpf(1)
Cc = 24 * (abs(K) + 1)
k0 = (1 / (24 * Cc + 24)) ** 2
c0 = k0**2 / (24 * Cc + 24)
hyp = Cc * (sqrt(k0) + c0 ** (mpf(17) / 3) + k0**-2 * c0 ** (mpf(34) / 3))
print(f"    kappa0 = {mp.nstr(k0,4)}, c0 = {mp.nstr(c0,4)}, Ccrit*(...) = {mp.nstr(hyp,4)} (<= 1/8: {hyp <= mpf(1)/8})")
for logd in [700, 1500, 3000]:
    d = mpf(10) ** logd
    p = int(floor(c0 * d ** (mpf(2) / 17)))
    h = k0 / mpf(p) ** 4
    T, P = toterr_terms(d, p, h)
    pm = mpf(p)
    lhs = 2 * (1 + 9 / P["d"]) / (4 * (pm - 1)) + K * sum(T.values()) + 2 * P["eta0"]
    print(f"    d=1e{logd}: p=1e{float(log10(pm)):.1f}, reg={10**6 <= p}: p*(1/p - LHS) = {mp.nstr(pm*(1/pm - lhs), 6)}"
          f"  [3/8 = 0.375; rest*p = {mp.nstr(pm*(sum(T.values()) - 2*T['p sqrt(h)'] - T['Gam'] - T['p e^2']), 4)}]")
