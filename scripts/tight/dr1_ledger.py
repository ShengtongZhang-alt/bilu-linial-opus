"""DR1 check: exponent ledger of every term that GR1 touched, under three routes.

Monomials c0^A * kappa0^K * p^E at d = (p/c0)^(17/2), h = kappa0 p^-4 (exact powers, sympy).
Routes: 'GR1' (paper, delta_row = delta/p), 'none' (no row gain, rows bounded by delta only),
'DR1' (difference energy delta/p + p^2/d, individual rows by delta).  The end game tolerates
c * p^-1 with c small after choosing kappa0 then c0; anything with p-exponent < -1 is o(1/p).
Run: /tmp/tight-venv/bin/python scripts/tight/dr1_ledger.py
"""
from sympy import Rational as Q, sqrt, symbols, simplify, powsimp, expand_power_base, log

c0, k0, p = symbols('c0 kappa0 p', positive=True)
d = (p / c0) ** Q(17, 2)
h = k0 * p ** -4
eps = (p * d) ** Q(-1, 2)
delta = (p / d) ** Q(1, 3)            # dominant term of C*(eps + p^4/d + (p/d)^(1/3))
assert all(simplify(t / delta).subs({c0: 1}).subs(p, 10**6) < 1 for t in (eps, p**4 / d))
lam1 = p / d                           # D6: a^2 S + E tr A^2 <= C p/d at the contact
lam_r = 5 / d                          # (S+1)/d with S ~ 4 (D15); S <= Cp gives p/d
dlt_row = delta / p                    # GR1
dlt_diff = (delta / p, p**2 / d)       # DR1: two pieces


def mono(x):
    x = powsimp(expand_power_base(simplify(x), force=True), force=True)
    A = simplify(x.diff(c0) * c0 / x)
    K = simplify(x.diff(k0) * k0 / x)
    E = simplify(x.diff(p) * p / x)
    return f"c0^{A} k0^{K} p^{E}"


def show(label, terms):
    print(f"  {label:42s} " + " + ".join(mono(t) for t in terms))


print("Gamma = p^4 sqrt(p delta/d):", mono(p**4 * sqrt(p * delta / d)))
print("\n[D9a] E_row, the Phi^(4) R_v term (coefficient p^5) and the core-mark term p^4 sqrt(lam_c delta_c):")
show("GR1: p^5 sqrt(lam_r delta_row)", [p**5 * sqrt(lam_r * dlt_row)])
show("none: p^5 sqrt(lam_r delta)", [p**5 * sqrt(lam_r * delta)])
show("DR1: p^5 sqrt(lam_r delta_diff) + p^4 lam_r", [p**5 * sqrt(lam_r * t) for t in dlt_diff] + [p**5 / d])
show("all routes: p^4 sqrt(lam_1 delta)", [p**4 * sqrt(lam1 * delta)])

print("\n[FS5 -> RC3] p e^2, e = p sqrt(row score energy)/(sqrt(d) h):")
e_gr1 = p * sqrt(dlt_row) / (sqrt(d) * h)
e_none = p * sqrt(delta) / (sqrt(d) * h)
show("GR1", [p * e_gr1**2])
show("none", [p * e_none**2])
show("DR1 (det. part, two pieces)", [p * (p * sqrt(t) / (sqrt(d) * h)) ** 2 for t in dlt_diff])
show("DR1 (root-weight part, sqrt(lam1+delta))", [p * (sqrt(delta) / (sqrt(d) * h)) ** 2])
show("other e-terms: p e h^(3/4), p e (dh)^(-1/2)", [p * e_gr1 * h ** Q(3, 4), p * e_gr1 / sqrt(d * h)])

print("\n[D13] row-containing part of Q_*/a^2:")
show("GR1: p^3 sqrt(lam1 delta_row)", [p**3 * sqrt(lam1 * dlt_row)])
show("DR1/none: p^3 (lam1 + sqrt(lam1 delta))", [p**3 * lam1, p**3 * sqrt(lam1 * delta)])

print("\n[W1 remainder] coefficient p^3 rho + p^2 sqrt(rho) must be <= C p (rho = delta, no gain):")
show("p^3 delta, p^2 sqrt(delta)", [p**3 * delta, p**2 * sqrt(delta)])

print("\n[DR1 internal] p^2/d <= delta/p  <=>  p^4 <= d:", mono((p**2 / d) / (delta / p)))
print("[GR1-free bound on 2a^2T] a^2(S+ + S-) <= 2 delta, divided by (2p-1): delta/p:", mono(delta / p))
