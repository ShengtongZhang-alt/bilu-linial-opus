"""AUDIT-B numerical checks for lines 600-1076 of second_order_bilu_linial_tight.tex.

Run: /tmp/tight-venv/bin/python scripts/tight/auditB_checks.py
"""
import numpy as np
from fractions import Fraction as Fr
from scipy import integrate, optimize

rng = np.random.default_rng(1)


def section(t):
    print("\n=== " + t + " ===")


# 1. E6 exponent: log 40 - 16 (1 - 4/7)
section("E6 constant")
print("log40 - 48/7 =", np.log(40) - 48 / 7)

# 2. exponent ledger with p = c0 d^{2/17}, i.e. d ~ p^{17/2}.
section("exponent checks in powers of p (d = p^(17/2))")
D = Fr(17, 2)
delta = max(Fr(-19, 4), 4 - D, (1 - D) / 3)  # eps, p^4/d, (p/d)^{1/3}
print("delta ~ p^", delta)
u = (1 - D) / 3
h = Fr(-4)
for name, lhs, rhs in [
    ("p^5/d <= u", 5 - D, u), ("p^4/d <= u", 4 - D, u), ("p^2/d <= u^2", 2 - D, 2 * u),
    ("p^9/d^2 <= u^2", 9 - 2 * D, 2 * u), ("p/(dh)=o(sqrt h)", 1 - D - h, h / 2),
    ("p^5/d=o(sqrt h)", 5 - D, h / 2), ("p^2/d=o(h)", 2 - D, h), ("p^9/d^2=o(h)", 9 - 2 * D, h),
    ("delta <= p^-2 (W-lemma needs rho_row<=Cp^-2)", delta, Fr(-2)),
]:
    print(f"{name:45s} lhs p^{lhs}  rhs p^{rhs}  ok={lhs <= rhs}")

# 3. Slack in GR1: T_v <= C p^m  =>  delta_row = C(delta/p + p^m/d).
section("GR1 slack: T_v <= C p^m")
for m in [Fr(4), Fr(5), Fr(11, 2), Fr(6)]:
    drow = max(delta - 1, m - D)
    pe2 = 11 + drow - D          # p e^2 = p^11 delta_row / (kappa0^2 d)
    gam = 5 + (drow - D) / 2     # p^5 sqrt(delta_row/d)  (times sqrt(S+1))
    print(f"m={m}: delta_row~p^{drow}, p e^2~p^{pe2}, p^5 sqrt(drow/d)~p^{gam}; "
          f"critical exponent must be <= -1: {pe2 <= -1 and gam <= -1}")
# without any row gain (delta_row = delta): best exponent theta with p = d^theta
# p e^2 = p^{11} (p/d)^{1/3} / d <= p^{-1}  <=>  p^{37/3} <= d^{4/3}
print("no row gain: theta_max =", Fr(4, 3) / Fr(37, 3), "vs 2/17 =", Fr(2, 17))


# 4. Elementary Gaussian lemma: tr(AB (I + c1 A + c2 B)^{-1}) >= 0.
section("tr(AB (I+c1A+c2B)^-1) >= 0, random tests")
def rpsd(n, r=None):
    r = r or n
    X = rng.standard_normal((n, r)) * rng.exponential(1, r)
    return X @ X.T
mn = np.inf
for _ in range(20000):
    n = rng.integers(1, 7)
    A, B = rpsd(n, rng.integers(1, n + 1)), rpsd(n, rng.integers(1, n + 1))
    c1, c2 = rng.exponential(3, 2)
    v = np.trace(A @ B @ np.linalg.inv(np.eye(n) + c1 * A + c2 * B))
    mn = min(mn, v / (np.linalg.norm(A) * np.linalg.norm(B)))
print("min normalized value:", mn)


# 5. Conditional positivity E[q_AB | q_A=u, q_B=w] >= 0 FAILS (2D example):
#    so monotonicity of the profiles is essential (no pointwise shortcut).
section("conditional positivity counterexample (2D)")
eps, phi = 0.01, 0.5
A = np.diag([1.0, eps])
R = np.array([[np.cos(phi), -np.sin(phi)], [np.sin(phi), np.cos(phi)]])
B = R @ A @ R.T
def cond(uu):
    f = lambda t: (np.array([np.cos(t), np.sin(t)]) @ (A - B) @ np.array([np.cos(t), np.sin(t)]))
    ts = np.linspace(0, np.pi, 20001)
    roots = [optimize.brentq(f, ts[k], ts[k + 1]) for k in range(len(ts) - 1)
             if f(ts[k]) * f(ts[k + 1]) < 0]
    s = 0.0
    for t in roots:
        e = np.array([np.cos(t), np.sin(t)])
        x = np.sqrt(uu / (e @ A @ e)) * e
        Ax, Bx = A @ x, B @ x
        s += np.exp(-x @ x / 2) * (Ax @ Bx) / abs(Ax[0] * Bx[1] - Ax[1] * Bx[0])
    return s
for uu in [1e-3, 1e-2, 0.05, 0.1, 0.3]:
    print(f"u=w={uu}: conditional numerator sign {np.sign(cond(uu)):+.0f} value {cond(uu):.4g}")


# 6. The GCI consequence itself, by 2D quadrature: G[q_AB alpha^{p-1} beta^{p-1}] >= 0.
section("G[q_AB alpha^(p-1) beta^(p-1)] in 2D (should be >= 0)")
def gci_val(A, B, p):
    def integrand(r, t):
        x = r * np.array([np.cos(t), np.sin(t)])
        qa, qb = x @ A @ x, x @ B @ x
        if qa >= 1 or qb >= 1:
            return 0.0
        return r * np.exp(-r * r / 2) * ((A @ x) @ (B @ x)) * (1 - qa) ** (p - 1) * (1 - qb) ** (p - 1)
    v, _ = integrate.dblquad(integrand, 0, 2 * np.pi, 0, 40, epsabs=1e-12)
    return v
for scale in [1.0, 5.0, 30.0]:
    for p in [3, 10, 40]:
        print(f"scale={scale} p={p}: {gci_val(scale * A, scale * B, p):.3e}")


# 7. Log-concavity of x -> log det P(x) - log det(P(x)+h) along random lines (P affine).
section("concavity of log det P - log det(P+h) on lines")
worst = -np.inf
for _ in range(2000):
    n = 5
    P0 = rpsd(n) + np.eye(n)
    E = rng.standard_normal((n, n)); E = E + E.T
    h = rng.exponential(1)
    ts = np.linspace(-1, 1, 41)
    vals = []
    for t in ts:
        P = P0 + 0.2 * t * E
        if np.min(np.linalg.eigvalsh(P)) <= 0:
            vals.append(np.nan); continue
        vals.append(np.linalg.slogdet(P)[1] - np.linalg.slogdet(P + h * np.eye(n))[1])
    v = np.array(vals)
    sd = v[2:] - 2 * v[1:-1] + v[:-2]
    sd = sd[~np.isnan(sd)]
    if len(sd):
        worst = max(worst, sd.max())
print("max second difference (should be <= ~0):", worst)
