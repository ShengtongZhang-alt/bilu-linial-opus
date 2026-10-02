"""AUDIT-D: symbolic / numerical checks of exact identities and deterministic
inequalities used in Section 1.5 of docs/second_order_bilu_linial_tight.tex.

 1. Phi^{-1} d_i^3 (Phi x_i) = a^3 K_i   (definition of Q_*, lines 1372-1393)
    and the row-free part / x_i = 0 part of K_i (lines 1414, 1946).
 2. D3 algebra: corrected loop + (F3) => (D3)  (lines 1396-1413).
 3. (BM1) deterministic mask inequality (lines 1596-1641), random tests.
 4. (FS2) Schur identity for the Schur column F_{ji} (lines 1674-1681).
 5. (C5) full/core shifted rank-one correction (used in D10, lines 1532-1545).
 6. Walk-sum bounds K = B^{-1} >= 0, K_vv >= 1, K_vi >= tau_vi (Lemma
    fw-deletion), which give J >= C_+ (load-bearing in D14).
 7. JR2 scalar step: min over x in [0,1) of
    -x + x^2/2 (A/(1-x) + p/(1+x)) >= -1/(4A)  (lines 1898-1906).
 8. Jacobi monotone iteration for the deletion lift (alternative to ODE).

Run: /tmp/tight-venv/bin/python scripts/tight/auditD_identities.py
"""
import numpy as np
import sympy as sp

rng = np.random.default_rng(20261001)

# ---------------------------------------------------------------------------
# 1. K_i identity.  Work with a 3-dim neighbourhood, xi_1 symbolic (index i=0).
# ---------------------------------------------------------------------------
print("== 1. Phi^{-1} d^3 (Phi x_i) = a^3 K_i ==")
a, p = sp.symbols('a p', positive=True)
t = sp.symbols('t', real=True)  # xi_i as a real variable


def rand_psd(n, scale):
    M = rng.normal(size=(n, n))
    return sp.Matrix((M @ M.T) * scale / n).applyfunc(lambda v: sp.Rational(int(v * 10**6), 10**6))


n = 3
A = rand_psd(n, 0.1)
B = rand_psd(n, 0.1)
xi = sp.Matrix([t, sp.Rational(1), sp.Rational(-1)])
qa = (xi.T * A * xi)[0]
qb = (xi.T * B * xi)[0]
alpha = 1 - qa
beta = 1 - qb
Axi = (A * xi)[0]
Bxi = (B * xi)[0]
Phi = alpha**p * beta**p
x = -Axi / (a * alpha)
z = Bxi / (a * beta)
P = A[0, 0] / (a**2 * alpha) + x**2
Q = B[0, 0] / (a**2 * beta) + z**2
U = (p - 1) * x - p * z
V = (p - 1) * (P + x**2) + p * (Q + z**2)
W = (p - 1) * (3 * P * x + x**3) - p * (3 * Q * z + z**3)
K = x * (8 * U**3 - 12 * U * V + 4 * W) - 3 * (P - x**2) * (4 * U**2 - 2 * V)
lhs = sp.diff(Phi * x, t, 3) / Phi
for tv in [sp.Rational(1), sp.Rational(-1), sp.Rational(1, 3)]:
    for pv in [5, 7, sp.Rational(23, 2)]:
        for av in [sp.Rational(1, 10), sp.Rational(1, 3)]:
            sub = {t: tv, p: pv, a: av}
            L = sp.N(lhs.subs(sub), 30)
            Rr = sp.N((a**3 * K).subs(sub), 30)
            print(f"  t={tv} p={pv} a={av}: lhs={float(L):+.12e} a^3K={float(Rr):+.12e}"
                  f" diff={float(L - Rr):.1e}")

# also: D_1 x_i formula used in the loop:  W^{-1} d (W x) = -a P + (2p-1) a x^2 - 2 p a x z
lhs1 = sp.diff(Phi * x, t) / Phi
rhs1 = -a * P + (2 * p - 1) * a * x**2 - 2 * p * a * x * z
sub = {t: sp.Rational(1), p: 7, a: sp.Rational(1, 5)}
print("  D_1 x_i check diff:", float(sp.N((lhs1 - rhs1).subs(sub), 30)))

# row-free part and x=0 part of K, as polynomials in x,z,P,Q
X, Z, PP, QQ = sp.symbols('x z P Q')
Uq = (p - 1) * X - p * Z
Vq = (p - 1) * (PP + X**2) + p * (QQ + Z**2)
Wq = (p - 1) * (3 * PP * X + X**3) - p * (3 * QQ * Z + Z**3)
Kq = sp.expand(X * (8 * Uq**3 - 12 * Uq * Vq + 4 * Wq) - 3 * (PP - X**2) * (4 * Uq**2 - 2 * Vq))
rowfree = sp.expand(Kq.subs({X: 0, Z: 0}))
print("  row-free part:", sp.factor(rowfree), " expected 6P((p-1)P+pQ)")
x0 = sp.expand(Kq.subs(X, 0) - rowfree)
print("  x=0 row part:", sp.factor(x0), " expected -6p(2p-1)P z^2")
rest = sp.expand(Kq - Kq.subs(X, 0))
poly = sp.Poly(rest, X, Z)
bad = [m for m in poly.monoms() if not (m[0] >= 1 and m[0] + m[1] >= 2)]
print("  monomials of K - K|_{x=0} lacking (x and a 2nd row factor):", bad)
deg = max(sum(m) for m in sp.Poly(Kq, X, Z, PP, QQ).monoms())
print("  total degree of K in inverse entries:", deg,
      "; max p-degree of coefficients:", sp.Poly(Kq, p).degree())

# ---------------------------------------------------------------------------
# 2. D3 algebra
# ---------------------------------------------------------------------------
print("\n== 2. D3 algebra ==")
r, L, Cp, S, T, J, Sl, Qs, a2 = sp.symbols('r L C_+ S T J Sigma_ld Q_* a2', real=True)
# Sum_i a^2 E[G_vv G_ii] <= r^2 L - r Sigma_ld + (1/p)(a2 S - r J)   [F3 + cap]
loop_rhs_bound = 1 + (r**2 * L - r * Sl + (a2 * S - r * J) / p) - (2 * p - 1) * a2 * S + 2 * p * a2 * T + Qs
Dplus = 1 + L - Cp
# D_+ r <= loop_rhs_bound   <=>   lhs_D3 <= Q_* + r C_+
lhs_D3 = (r - 1) * (1 - r * L) + r * Sl + (1 - 1 / p) * a2 * S + (r / p) * J + 2 * a2 * ((p - 1) * S - p * T)
diff = sp.simplify((loop_rhs_bound - Dplus * r) - (Qs + r * Cp - lhs_D3))
print("  (rhs - D_+ r) - (Q_* + r C_+ - lhs_D3) =", diff, "(should be 0)")

# ---------------------------------------------------------------------------
# 3. BM1
# ---------------------------------------------------------------------------
print("\n== 3. (BM1) sum_{i in I, j} F_ji^2 <= 16 D^2 h^-2 b^T K b ==")
worst = 0.0
for trial in range(4000):
    m = rng.integers(2, 9)
    h = 10 ** rng.uniform(-3, 0)

    def rpsd():
        M = rng.normal(size=(m, m)) * rng.uniform(0.1, 3)
        S_ = M @ M.T
        ev = np.linalg.eigvalsh(S_)
        S_ = S_ / ev.max() / h * rng.uniform(0.05, 1)
        return S_

    Xm, Ym = rpsd(), rpsd()
    b = rng.exponential(size=m) * (rng.random(m) < 0.8)
    Bm = np.diag(b)
    Um = Xm @ Bm @ Ym
    I = np.where(rng.random(m) < 0.6)[0]
    if len(I) == 0:
        continue
    D = Xm.diagonal()[I].max()
    Fm = np.array([[Xm[i, i] * Um[j, i] - Xm[j, i] * Um[i, i] for i in range(m)] for j in range(m)])
    lhsv = (Fm[:, I] ** 2).sum()
    Km = Xm * Ym / 4
    rhsv = 16 * D**2 / h**2 * b @ Km @ b
    if rhsv > 0:
        worst = max(worst, lhsv / rhsv)
print(f"  max lhs/rhs over 4000 trials: {worst:.4f} (must be <= 1)")

# ---------------------------------------------------------------------------
# 4. FS2 Schur identity, 5. C5
# ---------------------------------------------------------------------------
print("\n== 4. (FS2) and 5. (C5) on random signed graphs ==")


def random_graph(nv, pe):
    Adj = np.zeros((nv, nv))
    for i in range(nv):
        for j in range(i + 1, nv):
            if rng.random() < pe:
                s = rng.choice([-1.0, 1.0])
                Adj[i, j] = Adj[j, i] = s
    return Adj


maxerr4 = 0.0
min5 = np.inf
for trial in range(300):
    nv = rng.integers(4, 10)
    As = random_graph(nv, 0.5)
    aa = 0.25
    Zd = rng.uniform(1.0, 2.0, size=nv)
    Pp = np.diag(Zd) + aa * As
    Pm = np.diag(Zd * rng.uniform(1, 1.3, size=nv)) - aa * As
    if np.linalg.eigvalsh(Pp).min() <= 0 or np.linalg.eigvalsh(Pm).min() <= 0:
        continue
    h = 10 ** rng.uniform(-2, 0)
    Xp = np.linalg.inv(Pp + h * np.eye(nv))
    Xm_ = np.linalg.inv(Pm + h * np.eye(nv))
    v = 0
    Nv = [k for k in range(nv) if As[v, k] != 0]
    if len(Nv) < 1:
        continue
    u = np.zeros(nv)
    u[Nv] = 1 / np.sqrt(len(Nv) + 1)
    for eps_sign, Xe, Pe in [(+1, Xp, Pp), (-1, Xm_, Pm)]:
        Um = Xe @ np.diag(u) @ Xp
        for i in Nv:
            keep = [k for k in range(nv) if k != i]

            def core_inv(Pbranch):
                Ci = np.zeros((nv, nv))
                sub = Pbranch[np.ix_(keep, keep)] + h * np.eye(nv - 1)
                Ci[np.ix_(keep, keep)] = np.linalg.inv(sub)
                return Ci

            Ce = core_inv(Pe)
            Cpl = core_inv(Pp)
            for j in range(nv):
                if As[i, j] == 0:
                    continue
                F = Xe[i, i] * Um[j, i] - Xe[j, i] * Um[i, i]
                ssum = 0.0
                for k in Nv:
                    if k == i:
                        continue
                    for l in range(nv):
                        if As[i, l] == 0:
                            continue
                        ssum += Ce[j, k] * u[k] * Cpl[k, l] * As[i, l]
                Fs = -aa * Xe[i, i] * Xp[i, i] * ssum
                maxerr4 = max(maxerr4, abs(F - Fs))
    # C5: tr[X_z[N,N] - C_z[N,N]] <= (Z_v/z)(G_vv - X_z,vv)
    for Pbr in [Pp, Pm]:
        G = np.linalg.inv(Pbr)
        Xz = np.linalg.inv(Pbr + h * np.eye(nv))
        keep = [k for k in range(nv) if k != v]
        Cz = np.linalg.inv(Pbr[np.ix_(keep, keep)] + h * np.eye(nv - 1))
        idx = [keep.index(k) for k in Nv]
        lhs5 = np.trace(Xz[np.ix_(Nv, Nv)]) - np.trace(Cz[np.ix_(idx, idx)])
        rhs5 = Pbr[v, v] / h * (G[v, v] - Xz[v, v])
        min5 = min(min5, rhs5 - lhs5)
        assert lhs5 >= -1e-12
print(f"  FS2 max |F - Schur form| = {maxerr4:.2e}")
print(f"  C5 min(rhs - lhs) = {min5:.3e} (must be >= 0)")

# ---------------------------------------------------------------------------
# 6. Walk-sum bounds for K = B^{-1}
# ---------------------------------------------------------------------------
print("\n== 6. K = B^{-1}: K >= 0, K_vv >= 1, K_vi >= tau_vi on edges ==")
worst_diag, worst_edge, worst_neg = np.inf, np.inf, np.inf
for trial in range(300):
    dd = int(rng.integers(3, 12))
    q = dd - 1
    pp = 4.0
    Delta = 4 / pp
    R2 = 4 * q + Delta
    a2 = 1 / R2
    eta = (-Delta + np.sqrt(Delta**2 + 4 * q * Delta)) / (2 * q)
    tau_s = (1 - eta) / q
    s = (1 + q * tau_s) / (1 - tau_s)
    nv = int(rng.integers(dd + 1, 3 * dd))
    # random graph with max degree <= dd
    Adj = np.zeros((nv, nv), dtype=bool)
    pairs = [(i, j) for i in range(nv) for j in range(i + 1, nv)]
    rng.shuffle(pairs)
    for (i, j) in pairs:
        if Adj[i].sum() < dd and Adj[j].sum() < dd and rng.random() < 0.7:
            Adj[i, j] = Adj[j, i] = True
    y = rng.uniform(0, s, size=nv) ** rng.uniform(0.2, 1)  # in (0, s]
    y = np.minimum(y, s)
    c = np.zeros((nv, nv))
    tau = np.zeros((nv, nv))
    for i in range(nv):
        for j in range(nv):
            if Adj[i, j]:
                x_ = a2 * y[i] * y[j]
                c[i, j] = (np.sqrt(1 + 4 * x_) - 1) / 2
                tau[i, j] = c[i, j] / (1 + c[i, j])
    assert tau.max() <= tau_s + 1e-12
    Bm = np.zeros((nv, nv))
    for i in range(nv):
        Bm[i, i] = 1 + sum(tau[i, j]**2 / (1 - tau[i, j]**2) for j in range(nv) if Adj[i, j])
        for j in range(nv):
            if Adj[i, j]:
                Bm[i, j] = -tau[i, j] / (1 - tau[i, j]**2)
    Km = np.linalg.inv(Bm)
    worst_neg = min(worst_neg, Km.min())
    worst_diag = min(worst_diag, Km.diagonal().min() - 1)
    for i in range(nv):
        for j in range(nv):
            if Adj[i, j]:
                worst_edge = min(worst_edge, Km[i, j] - tau[i, j])
    # Jacobian check DZ = -D^{-1} B D^{-1} (finite differences)
    if trial < 20:
        def Zmap(yy):
            out = np.zeros(nv)
            for i in range(nv):
                ssum = 0.0
                for j in range(nv):
                    if Adj[i, j]:
                        x_ = a2 * yy[i] * yy[j]
                        ssum += (np.sqrt(1 + 4 * x_) - 1) / 2
                out[i] = (1 + ssum) / yy[i]
            return out
        Jfd = np.zeros((nv, nv))
        for k in range(nv):
            e_ = np.zeros(nv); e_[k] = 1e-6 * y[k]
            Jfd[:, k] = (Zmap(y + e_) - Zmap(y - e_)) / (2e-6 * y[k])
        Dinv = np.diag(1 / y)
        err = np.abs(Jfd + Dinv @ Bm @ Dinv).max() / np.abs(Jfd).max()
        assert err < 1e-6, err
print(f"  min K entry = {worst_neg:.3e} (>= 0), min K_vv - 1 = {worst_diag:.3e} (>= 0),"
      f" min (K_vi - tau_vi) = {worst_edge:.3e} (>= 0); Jacobian DZ = -D^-1 B D^-1 checked")

# ---------------------------------------------------------------------------
# 7. JR2 scalar step
# ---------------------------------------------------------------------------
print("\n== 7. JR2 scalar step ==")
for pv in [3, 5, 10, 100, 1000]:
    Ap = pv - 1
    xs = np.linspace(0, 0.999, 200001)
    f = -xs + xs**2 / 2 * (Ap / (1 - xs) + pv / (1 + xs))
    print(f"  p={pv}: min = {f.min():+.6e}, -1/(4A_p) = {-1/(4*Ap):+.6e},"
          f" ratio = {f.min()/(-1/(4*Ap)):.4f}")
xs = np.linspace(0, 50, 500001)
fx = xs**2 / (2 * (1 + xs)) - xs
df = np.diff(fx) / np.diff(xs)
print(f"  f(x)=x^2/(2(1+x))-x: slope range [{df.min():.4f}, {df.max():.4f}] (decreasing, 1-Lipschitz)")

# ---------------------------------------------------------------------------
# 8. Jacobi monotone iteration for the deletion lift
# ---------------------------------------------------------------------------
print("\n== 8. deletion lift by monotone Jacobi iteration ==")
from scipy.optimize import brentq
maxres = 0.0
for trial in range(40):
    dd = int(rng.integers(3, 8)); q = dd - 1
    a2 = 1 / (4 * q + 1.0)
    nv = int(rng.integers(dd + 2, 2 * dd + 4))
    Adj = np.zeros((nv, nv), dtype=bool)
    for i in range(nv):
        for j in range(i + 1, nv):
            if Adj[i].sum() < dd and Adj[j].sum() < dd and rng.random() < 0.6:
                Adj[i, j] = Adj[j, i] = True
    s = 2.0
    y = rng.uniform(0.05, s, size=nv)
    cfun = lambda x_: (np.sqrt(1 + 4 * x_) - 1) / 2

    def Zi(i, yi, yy, adj):
        return (1 + sum(cfun(a2 * yi * yy[j]) for j in range(len(yy)) if adj[i, j])) / yi

    v = 0
    Jset = list(range(1, nv))
    adjJ = Adj[np.ix_(Jset, Jset)]
    yJ = y[1:]
    target = np.array([Zi(i, y[i], y, Adj) for i in Jset])  # Z^H(y)|_J
    yh = yJ.copy()
    for it in range(400):
        new = np.empty_like(yh)
        for k in range(len(Jset)):
            g = lambda t_: Zi(k, t_, yh, adjJ) - target[k]
            gk = g(yh[k])
            if gk > 1e-9:
                raise RuntimeError("monotonicity violated")
            new[k] = brentq(g, 1e-9, yh[k], xtol=1e-15) if gk < 0 else yh[k]
        assert np.all(new <= yh + 1e-14)
        yh = new
    res = max(abs(Zi(k, yh[k], yh, adjJ) - target[k]) for k in range(len(Jset)))
    assert np.all(yh <= yJ + 1e-12) and np.all(yh >= 1 / target - 1e-12)
    maxres = max(maxres, res)
print(f"  max residual |Z^J(yhat) - Z^H(y)|_J| after 400 sweeps: {maxres:.2e};"
      " iterates decrease monotonically, stay >= 1/target, end <= y|_J")
