"""AUDIT-D: parameter identities, the drift reserve (D2), the C_+ envelope,
the final margin, and the exponent ledger (D16) of
docs/second_order_bilu_linial_tight.tex, Section 1.5.

Run: /tmp/tight-venv/bin/python scripts/tight/auditD_params.py
"""
from mpmath import mp, mpf, sqrt, floor, log

mp.dps = 60


def params(d, p):
    d = mpf(d)
    p = mpf(p)
    q = d - 1
    Delta = 4 / p
    R2 = 4 * q + Delta
    a = 1 / sqrt(R2)
    # q eta^2/(1-eta) = Delta  ->  q eta^2 + Delta eta - Delta = 0
    eta = (-Delta + sqrt(Delta**2 + 4 * q * Delta)) / (2 * q)
    tau = (1 - eta) / q
    s = (1 + q * tau) / (1 - tau)
    r = 1 + eta / 2
    Lbar = d * a**2 * s**2
    return dict(d=d, p=p, q=q, Delta=Delta, R2=R2, a=a, eta=eta, tau=tau,
                s=s, r=r, Lbar=Lbar)


def check_identities(d, p):
    P = params(d, p)
    q, a, s, tau, eta, Lbar = P['q'], P['a'], P['s'], P['tau'], P['eta'], P['Lbar']
    # a^2 s^2 = tau/(1-tau)^2 (tau_* is the edge maximum of tau_ij at y=s)
    e1 = a**2 * s**2 - tau / (1 - tau)**2
    # s formula of (D1)
    e2 = s - (2 - eta) / (1 - (1 - eta) / q)
    # Lbar formula of (D2)
    e3 = Lbar - P['d'] * q * (1 - eta) / (q - 1 + eta)**2
    # Bethe diagonal at y = s 1: Z_i = (1+(deg-1)tau)/(1+q tau) <= 1, = 1 at deg = d
    c = tau / (1 - tau)
    Zmax = (1 + P['d'] * c) / s
    # diagonal-dominance margin 1 - d tau/(1+tau) = eta/(1+tau)
    e4 = (1 - P['d'] * tau / (1 + tau)) - eta / (1 + tau)
    return e1, e2, e3, Zmax, e4


def drift(d, p):
    P = params(d, p)
    r, Lbar, dd, pp, eta = P['r'], P['Lbar'], P['d'], P['p'], P['eta']
    val = dd * (r - 1) * (1 - r * Lbar)
    return val, val * pp, eta, (val - 1 / pp) / eta


def cplus_env(d, p):
    """C_+/a^2 <= d a^2 s^4 = Lbar s^2 and r*Lbar*s^2 (used in D14)."""
    P = params(d, p)
    return P['Lbar'] * P['s']**2, P['r'] * P['Lbar'] * P['s']**2


print("== identities (should be ~0, Zmax ~ 1) ==")
for d, p in [(10**4, 3), (10**8, 10), (10**17, 100), (10**40, 10**4)]:
    e1, e2, e3, Zm, e4 = check_identities(d, p)
    print(f"d=1e{len(str(d))-1} p={p}: {float(e1):.2e} {float(e2):.2e} "
          f"{float(e3):.2e} Zmax={float(Zm):.15f} {float(e4):.2e}")

print("\n== (D2) drift reserve d(r-1)(1-r Lbar) vs 1/p ==")
print("   (ratio p*drift -> 1; (drift-1/p)/eta stays bounded => O(eta) error)")
for d, p in [(10**6, 2), (10**8, 5), (10**12, 10), (10**17, 100),
             (10**25, 1000), (10**40, 10**4), (10**60, 10**6)]:
    v, vp, eta, err = drift(d, p)
    print(f"d=1e{len(str(d))-1} p={p}: p*drift={float(vp):.10f} "
          f"eta={float(eta):.3e} (drift-1/p)/eta={float(err):.4f}")

print("\n== C_+/a^2 envelope: r*Lbar*s^2 - 4 should be <= ~20/q ==")
for d, p in [(10**6, 5), (10**12, 10), (10**17, 100), (10**40, 10**4)]:
    e, er = cplus_env(d, p)
    q = mpf(d) - 1
    print(f"d=1e{len(str(d))-1} p={p}: Lbar s^2-4={float(e-4):.3e}, "
          f"r Lbar s^2-4={float(er-4):.3e}, 20/q={float(20/q):.3e}")

print("\n== final margin: 1/p - 2c_p (2c_p = 1/(2(p-1))) vs error budget ==")
for p in [10, 100, 1000, 10**4]:
    p = mpf(p)
    margin = 1 / p - 1 / (2 * (p - 1))
    print(f"p={int(p)}: p*(1/p - 2c_p) = {float(p*margin):.6f}  "
          f"(errors must total < this; paper uses < 1/4 + o(1))")

print("\n== regime checks at p = floor(c0 d^{2/17}) ==")
for c0 in [mpf(1), mpf('0.1'), mpf('0.01')]:
    for e in [20, 60, 200, 600, 2000]:
        d = mpf(10)**e
        p = floor(c0 * d**(mpf(2) / 17))
        if p < 3:
            print(f"c0={float(c0)} d=1e{e}: p={int(p)} (too small)")
            continue
        kstar = mp.ceil(16 * p / log(d))
        ok7 = p**7 <= d
        ok_mom = 8 * kstar + 12 <= p / 2
        # E6: log[p 40^p (C p)^{4k*+4} d^{-k*}] with C = 1 (C enters additively)
        e6 = log(p) + p * log(40) + (4 * kstar + 4) * log(p) - kstar * log(d)
        print(f"c0={float(c0)} d=1e{e}: p={float(p):.3e} k*={int(kstar)} "
              f"p^7<=d:{ok7} 8k*+12<=p/2:{ok_mom} E6 log/p={float(e6/p):.3f}")

# --------------------------------------------------------------------------
# (D16) exponent ledger.  Put d = (p/c0)^{17/2} (the extreme allowed by
# p <= c0 d^{2/17}), h = kappa0 p^{-4}.  Each quantity X is a monomial
# c0^A kappa0^K p^E; we record (A, K, E).
# --------------------------------------------------------------------------
from fractions import Fraction as F


class M:
    def __init__(self, A, K, E):
        self.A, self.K, self.E = F(A), F(K), F(E)

    def __mul__(self, o):
        if not isinstance(o, M):
            o = M(0, 0, 0) if o == 1 else o
        return M(self.A + o.A, self.K + o.K, self.E + o.E)

    __rmul__ = __mul__

    def __truediv__(self, o):
        return M(self.A - o.A, self.K - o.K, self.E - o.E)

    def __pow__(self, t):
        t = F(t)
        return M(self.A * t, self.K * t, self.E * t)

    def __repr__(self):
        return f"c0^{self.A} k0^{self.K} p^{self.E}"


one = M(0, 0, 0)
p = M(0, 0, 1)
d = M(F(-17, 2), 0, F(17, 2))       # d = c0^{-17/2} p^{17/2}
h = M(0, 1, -4)                      # h = kappa0 p^{-4}
eps = (p * d) ** F(-1, 2)            # r - 1 ~ (p d)^{-1/2}
eta0 = eps
delta_terms = {"eps": eps, "p^4/d": p**4 / d, "(p/d)^{1/3}": (p / d) ** F(1, 3)}
delta = (p / d) ** F(1, 3)           # dominant term of delta (D5), c0 <= 1
for k, v in delta_terms.items():
    print(f"   delta term {k}: {v}")
drow = delta / p
lam1 = p / d
eps_s = p ** F(3, 2) * d ** F(-1, 2)
rho_v = eps / p                      # eps/p dominates eps^2
chi = (eps / p) ** F(1, 2)           # dominant part of chi_+ besides eps_s
Gamma = p**4 * (p * delta / d) ** F(1, 2)
e = p * drow ** F(1, 2) / (d ** F(1, 2) * h)
theta = d ** -2

print("\n== (D16) ledger, d=(p/c0)^{17/2}, h=kappa0 p^{-4}; target scale p^-1 ==")
print("delta    =", delta, "  (paper: c0^{17/6} p^{-5/2})")
print("delta_row=", drow, "  (paper: p^{-7/2})")
print("lambda_1 =", lam1, "  (paper: p^{-15/2})")
print("eps      =", eps, "  (paper: p^{-19/4})")
print("eps_s    =", eps_s, "  (paper: p^{-11/4})")
print("e        =", e, "  (paper: p^{-1})")
terms = {
    "p sqrt(h)  [critical]": p * h ** F(1, 2),
    "Gamma      [critical]": Gamma,
    "p e^2      [critical]": p * e**2,
    "Gamma^2": Gamma**2,
    "p^13/d^2": p**13 / d**2,
    "p^5/d": p**5 / d,
    "p^2/(d h)": p**2 / (d * h),
    "p/(d h^{3/2})": p / (d * h ** F(3, 2)),
    "p B0 = p^2/(dh)+p/(d h^{3/2})": p / (d * h ** F(3, 2)),
    "p e h^{3/4}": p * e * h ** F(3, 4),
    "p e (dh)^{-1/2}": p * e * (d * h) ** F(-1, 2),
    "p e sqrt(theta)": p * e * theta ** F(1, 2),
    "p^3 sqrt(lambda1 delta_row)": p**3 * (lam1 * drow) ** F(1, 2),
    "p chi_+ (via eps_s)": p * eps_s,
    "p sqrt(eps/p)": p * chi,
    "p sqrt(rho_v)": p * rho_v ** F(1, 2),
    "p eps": p * eps,
    "eps_s (S-4 absorption)": eps_s,
    "d*O(p^5 d^-2) (D3 remainder)": p**5 / d,
    "d*eta0 (D2 error)": eta0,
}
for k, v in terms.items():
    tag = "CRITICAL" if v.E == -1 else ("ok o(1/p)" if v.E < -1 else "BAD")
    print(f"  {k:36s} {str(v):34s} {tag}")

print("\n== balancing: why 2/17 ==")
print(" Gamma = p^4 (p/d)^{1/2} delta^{1/2}, delta ~ (p/d)^{1/3}  =>  Gamma ~ p^{14/3} d^{-2/3}")
print(" Gamma ~ 1/p  <=>  p^{17/3} = d^{2/3}  <=>  p = d^{2/17}")
print(" p e^2 = kappa0^{-2} p Gamma^2 (identity), so p e^2 ~ 1/p iff Gamma ~ 1/p")
print(" p sqrt(h) ~ 1/p  <=>  h ~ p^{-4}")
pe2 = p * e**2
pg2 = p * Gamma**2
print(" check p e^2 / (p Gamma^2) =", pe2 / pg2, "(should be k0^{-2})")
