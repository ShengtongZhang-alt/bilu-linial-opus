"""AUDIT-A Gaussian-side checks (C1, C4, E4, E5) in dimension 2-3.

 (G1) N_G >= f_G * w  (whitened Prekopa bound) and N_G >= 0;
 (G2) identity N_G = 2 G[F], F = (p-1) q_{A^2} a^{p-2} b^p + p q_{AB} a^{p-1} b^{p-1};
 (G3) Cramer-Rao form of (C4) for random PSD M;
 (G4) (E4) with k = 0,1,2 in two coordinates: remainder <= (1/6) sum ||d^{2j} f||;
 (G5) (E5) normalised derivative bounds with C = 5 (first expression) at random support points.
"""
import itertools
import numpy as np
import sympy as sp
from math import factorial

rng = np.random.default_rng(7)

# ---------- grid quadrature on R^2 ----------
L, M = 6.5, 1301
xs = np.linspace(-L, L, M)
X, Y = np.meshgrid(xs, xs, indexing="ij")
h = xs[1] - xs[0]
gauss = np.exp(-(X**2 + Y**2) / 2) / (2 * np.pi) * h * h


def G(vals):
    return float(np.sum(vals * gauss))


def rand_psd(scale):
    Q = rng.normal(size=(2, 2))
    lam = rng.uniform(0.08, 1.0, 2) * scale
    U, _ = np.linalg.qr(Q)
    return U @ np.diag(lam) @ U.T


def qf(Mx):
    Mx = (Mx + Mx.T) / 2
    return Mx[0, 0] * X**2 + 2 * Mx[0, 1] * X * Y + Mx[1, 1] * Y**2

worst_G1 = 1e9; worst_G2 = 0; worst_G3 = 1e9
for trial in range(25):
    p = int(rng.integers(3, 9))
    A = rand_psd(rng.uniform(0.1, 0.6)); B = rand_psd(rng.uniform(0.1, 0.6))
    qA, qB = qf(A), qf(B)
    al = np.clip(1 - qA, 0, None); be = np.clip(1 - qB, 0, None)
    Phi = al**p * be**p
    fG = G(Phi)
    NG = G((np.trace(A) - qA) * al ** (p - 1) * be**p)
    TA = np.trace(A @ A); mu = np.trace(A); w = TA / (1 + mu)
    worst_G1 = min(worst_G1, NG - fG * w)
    F = (p - 1) * qf(A @ A) * al ** (p - 2) * be**p + p * qf(A @ B) * al ** (p - 1) * be ** (p - 1)
    worst_G2 = max(worst_G2, abs(NG - 2 * G(F)) / max(abs(NG), 1e-12))
    # (C4) Cramer-Rao for random PSD M (any PSD M)
    Mm = rand_psd(rng.uniform(0.05, 1.0))
    lhs = G((np.trace(Mm) - qf(Mm)) * Phi)
    with np.errstate(divide="ignore", invalid="ignore"):
        ia = np.where(al > 0, 1 / np.where(al > 0, al, 1), 0)
        ib = np.where(be > 0, 1 / np.where(be > 0, be, 1), 0)
    rhs = 2 * p * G((np.trace(Mm @ A) * ia + np.trace(Mm @ B) * ib) * Phi) \
        + 4 * p * G((qf(A @ Mm @ A) * ia**2 + qf(B @ Mm @ B) * ib**2) * Phi)
    worst_G3 = min(worst_G3, rhs - lhs)
print(f"(G1) min over trials of N_G - f_G w = {worst_G1:.3e} (>= 0 expected)")
print(f"(G2) max relative error |N_G - 2G[F]|/|N_G| = {worst_G2:.2e}")
print(f"(G3) min over trials of RHS(C4) - LHS(C4) = {worst_G3:.3e} (>= 0 expected)")

# ---------- c_j ----------
def cj_list(n):
    from fractions import Fraction as Fr
    c = []
    for m in range(n + 1):
        val = Fr(1, 2**m * factorial(m))
        for j in range(m):
            val -= c[j] / factorial(2 * m - 2 * j)
        c.append(val)
    return [float(x) for x in c]
cj = cj_list(20)

# ---------- (G4) E4 in two coordinates ----------
x1, x2 = sp.symbols("x1 x2")
A = rand_psd(0.5)
m_pow = 26
poly = (1 - (A[0, 0] * x1**2 + 2 * A[0, 1] * x1 * x2 + A[1, 1] * x2**2)) ** m_pow
f_num = sp.lambdify((x1, x2), poly, "numpy")
qA = qf(A)
supp = qA < 1


def clipped(expr):
    fn = sp.lambdify((x1, x2), expr, "numpy")
    return lambda U, V: np.where(supp_of(U, V), fn(U, V), 0.0)


def supp_of(U, V):
    return A[0, 0] * U**2 + 2 * A[0, 1] * U * V + A[1, 1] * V**2 < 1

Gf = G(np.where(supp, f_num(X, Y), 0.0))
signs = [(-1.0, -1.0), (-1.0, 1.0), (1.0, -1.0), (1.0, 1.0)]


def R(expr):
    fn = clipped(expr)
    return float(np.mean([fn(np.array(s1), np.array(s2)) for s1, s2 in signs]))


def grade(j):
    return sum(ji - 1 for ji in j if ji > 0)

allowed = [0] + list(range(2, 8))
for k in range(0, 3):
    retained = 0.0
    rem_bound = 0.0
    for j in itertools.product(allowed, repeat=2):
        g = grade(j)
        if g <= k:
            expr = sp.diff(poly, x1, 2 * j[0], x2, 2 * j[1]) if (j[0] or j[1]) else poly
            retained += cj[j[0]] * cj[j[1]] * R(expr)
        elif g == k + 1:
            expr = sp.diff(poly, x1, 2 * j[0], x2, 2 * j[1])
            fn = clipped(expr)
            rem_bound += np.max(np.abs(fn(X, Y)))
    print(f"(G4) k={k}: |G f - retained| = {abs(Gf - retained):.3e}  <=  (1/6)*sum sup = {rem_bound/6:.3e}")

# ---------- (G5) E5 bound with C=5 ----------
dim = 3
xs3 = sp.symbols("y0:3")
worst = 0.0
for trial in range(6):
    p = 8
    Q1 = rng.normal(size=(dim, dim)); Q2 = rng.normal(size=(dim, dim))
    A3 = Q1 @ Q1.T * rng.uniform(0.02, 0.2); B3 = Q2 @ Q2.T * rng.uniform(0.02, 0.2)
    xv = sp.Matrix(xs3)
    qA3 = (xv.T * sp.Matrix(A3) * xv)[0]; qB3 = (xv.T * sp.Matrix(B3) * xv)[0]
    f3 = (np.trace(A3) - qA3) * (1 - qA3) ** (p - 1) * (1 - qB3) ** p
    b = np.diag(A3) + np.diag(B3); mu0 = np.trace(A3) + np.trace(B3)
    # random support points
    pts = []
    while len(pts) < 30:
        z = rng.normal(size=dim) * 2
        if z @ A3 @ z < 1 and z @ B3 @ z < 1:
            pts.append(z)
    for nu in [(1, 0, 0), (2, 0, 0), (1, 1, 0), (4, 0, 0), (2, 2, 0), (1, 1, 2), (6, 0, 0), (2, 2, 2)]:
        expr = sp.diff(f3, *[v_ for v_, k_ in zip(xs3, nu) for _ in range(k_)])
        fn = sp.lambdify(xs3, expr, "numpy")
        nn = sum(nu)
        norm = (5 * p) ** nn * (2 + mu0) * np.prod([b[i] ** (nu[i] / 2) for i in range(dim)])
        for z in pts:
            worst = max(worst, abs(fn(*z)) / norm)
print(f"(G5) max |d^nu f| / ((5p)^n (2+mu0) prod b^(nu/2)) = {worst:.3e} (<= 1 expected)")
