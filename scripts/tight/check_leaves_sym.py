"""Symbolic and random checks for BiluLinial/Tight/Contact/Leaves.lean.

1. The polynomial K_i (`Kpoly`, l.1372-1383) used by `qstar_bound` and `d13_centering`:
   - row-free part (x = z = 0) is 6[(p-1)P^2 + pPQ]   (so the row-free part of Q_*/a^2 is
     2 L_d[(p-1) t_{+,0} + p t_{-,0}], RC5);
   - every other monomial has degree >= 2 in the row variables (x, z), with coefficient of degree
     <= 3 in p; monomials of row-degree exactly 2 have p-degree <= 2;
   - the x = 0 part of the row terms is -6p(2p-1) P z^2 (<= 0), and every monomial of K - K|_{x=0}
     contains x and a second row factor.
2. `bm1_det`: random and adversarial PSD X, Y with ||X||, ||Y|| <= 1/h, b >= 0, index sets I,
   D = max_{i in I} X_ii; ratio LHS / (16 D^2 h^-2 b^T (X o Y / 4) b) must be <= 1.
Run: /tmp/tight-venv/bin/python scripts/tight/check_leaves_sym.py
"""
import numpy as np
import sympy as sp

x, z, P, Q, p = sp.symbols("x z P Q p")
U = (p - 1) * x - p * z
V = (p - 1) * (P + x**2) + p * (Q + z**2)
W = (p - 1) * (3 * P * x + x**3) - p * (3 * Q * z + z**3)
K = sp.expand(x * (8 * U**3 - 12 * U * V + 4 * W) - 3 * (P - x**2) * (4 * U**2 - 2 * V))

rowfree = sp.expand(K.subs({x: 0, z: 0}))
print("row-free part:", sp.factor(rowfree), "| equals 6[(p-1)P^2 + pPQ]:",
      sp.simplify(rowfree - 6 * ((p - 1) * P**2 + p * P * Q)) == 0)

poly = sp.Poly(K, x, z, P, Q)
bad = []
maxdeg_by_rowdeg = {}
for (ex, ez, eP, eQ), coeff in poly.terms():
    rd = ex + ez
    pdeg = sp.degree(sp.expand(coeff), p)
    if rd == 0:
        continue
    if rd < 2:
        bad.append(((ex, ez, eP, eQ), coeff))
    maxdeg_by_rowdeg[rd] = max(maxdeg_by_rowdeg.get(rd, 0), pdeg)
print("monomials with exactly one row factor:", bad if bad else "none")
print("max p-degree of coefficients by row degree:", dict(sorted(maxdeg_by_rowdeg.items())))

row_part = sp.expand(K - rowfree)
x0 = sp.expand(row_part.subs(x, 0))
print("x = 0 part of the row terms:", sp.factor(x0), "| equals -6p(2p-1)P z^2:",
      sp.simplify(x0 + 6 * p * (2 * p - 1) * P * z**2) == 0)
rest = sp.Poly(sp.expand(row_part - x0), x, z, P, Q)
ok = all(ex >= 1 and ex + ez >= 2 for (ex, ez, _, _), _c in rest.terms())
print("every monomial of K - K|_{x=0} has a factor x and a second row factor:", ok)

# ------------------------------------------------------------------ bm1_det
rng = np.random.default_rng(7)


def rand_psd(n, h, kind):
    A = rng.standard_normal((n, n))
    if kind == "rank1":
        A[1:, :] *= 1e-3
    Q, _ = np.linalg.qr(A)
    if kind == "flat":
        ev = np.full(n, 1 / h)
    elif kind == "rank1":
        ev = np.zeros(n); ev[0] = 1 / h
    else:
        ev = rng.uniform(0, 1 / h, n)
    return (Q * ev) @ Q.T


worst = 0.0
for trial in range(20000):
    n = rng.integers(1, 7)
    h = 10 ** rng.uniform(-2, 1)
    X = rand_psd(n, h, rng.choice(["gen", "flat", "rank1"]))
    Y = X if rng.random() < 0.3 else rand_psd(n, h, rng.choice(["gen", "flat", "rank1"]))
    b = rng.uniform(0, 1, n) * (rng.random(n) < 0.7)
    I = [i for i in range(n) if rng.random() < 0.7]
    if not I:
        continue
    Dm = max(X[i, i] for i in I) * (1 + rng.uniform(0, 0.1))
    Ux = X @ np.diag(b) @ Y
    lhs = sum((X[i, i] * Ux[j, i] - X[j, i] * Ux[i, i]) ** 2 for i in I for j in range(n))
    rhs = 16 * Dm**2 / h**2 * (b @ ((X * Y / 4) @ b))
    if rhs > 1e-300:
        worst = max(worst, lhs / rhs)
    assert lhs <= rhs * (1 + 1e-8) + 1e-250
print(f"bm1_det: 20000 random/adversarial instances, worst LHS/RHS = {worst:.4f}")
