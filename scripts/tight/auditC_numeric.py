"""AUDIT-C numerical checks on small instances.

(a) Schur identities (F1), C5, the CR1 Frobenius decomposition, and B5 on a random graph.
(b) CR2 derivative rules and Phi^{-1} d^3(Phi x_i) = a^3 K_i by finite differences (mpmath).
(c) Gaussian IBP identity 2 G[F] = G[(trA - q_A) alpha^{p-1} beta^p]   (2-dim quadrature).
(d) Midpoint-BL:  Cov_nu <= E_nu (I+H)^{-1},  H = 2(p-1)M/alpha + 2pN/beta   (2-dim quadrature),
    and the parallelogram inequality alpha(z+w)alpha(z-w) <= alpha(z)^2 exp(-2 q_A(w)/alpha(z)).
"""
import numpy as np
import mpmath as mp

rng = np.random.default_rng(1)


# ---------------------------------------------------------------- (a) ----
def setup(n=9, d=4, p=6, seed=0):
    rng = np.random.default_rng(seed)
    # random graph of max degree <= d
    adj = np.zeros((n, n), dtype=int)
    for _ in range(4 * n):
        i, j = rng.integers(0, n, 2)
        if i != j and adj[i].sum() < d and adj[j].sum() < d:
            adj[i, j] = adj[j, i] = 1
    q = d - 1
    R2 = 4 * q + 4 / p
    a = 1 / np.sqrt(R2)
    sig = np.triu(rng.choice([-1, 1], size=(n, n)), 1)
    sig = (sig + sig.T) * adj
    return adj, a, sig


def precisions(adj, a, sig, yp, ym):
    n = len(adj)

    def Zof(y):
        c = np.zeros((n, n))
        for i in range(n):
            for j in range(n):
                if adj[i, j]:
                    c[i, j] = (-1 + np.sqrt(1 + 4 * a * a * y[i] * y[j])) / 2
        return (1 + c.sum(1)) / y, c

    Zp, cp = Zof(yp)
    Zm, cm = Zof(ym)
    Pp = np.diag(Zp) + a * sig
    Pm = np.diag(Zm) - a * sig
    return Pp, Pm, Zp, Zm, cp, cm


adj, a, sig = setup()
n = len(adj)
yp = rng.uniform(0.3, 1.0, n)
ym = rng.uniform(0.3, 1.0, n)
Pp, Pm, Zp, Zm, _, _ = precisions(adj, a, sig, yp, ym)
assert np.linalg.eigvalsh(Pp).min() > 0 and np.linalg.eigvalsh(Pm).min() > 0
v = int(np.argmax(adj.sum(1)))
N = np.flatnonzero(adj[v])
K = [k for k in range(n) if k != v]
Gp, Gm = np.linalg.inv(Pp), np.linalg.inv(Pm)
GKp = np.linalg.inv(Pp[np.ix_(K, K)])
GKm = np.linalg.inv(Pm[np.ix_(K, K)])
idxN = [K.index(i) for i in N]
xi = sig[v, N].astype(float)
A = a * a / Zp[v] * GKp[np.ix_(idxN, idxN)]
B = a * a / Zm[v] * GKm[np.ix_(idxN, idxN)]
alpha = 1 - xi @ A @ xi
beta = 1 - xi @ B @ xi
print("(a) F1: Zv G_vv alpha -1 =", Zp[v] * Gp[v, v] * alpha - 1, Zm[v] * Gm[v, v] * beta - 1)
print("    G+_vi + a^-1 (A xi)_i/alpha :", np.abs(Gp[v, N] + (A @ xi) / alpha / a).max())
print("    G-_vi - a^-1 (B xi)_i/beta  :", np.abs(Gm[v, N] - (B @ xi) / beta / a).max())
x = Gp[v, N]
zz = Gm[v, N]
print("    A_ii/alpha - a^2(P_i - x_i^2):",
      np.abs(np.diag(A) / alpha - a * a * (Gp[v, v] * np.diag(Gp)[N] - x**2)).max())
# CR1 Frobenius decomposition
lhs = a**4 * Gp[v, v]**2 * np.sum(Gp[np.ix_(N, N)]**2)
tplus = Zp[v] * Gp[v, v]
rhs = 2 * tplus**2 * np.trace(A @ A) + 2 * (a * a * np.sum(x**2))**2
print("    CR1 Frobenius: lhs <= rhs:", lhs <= rhs + 1e-15, lhs, rhs)
# C5 with shift z
for zsh in [0.05, 0.5]:
    Xz = np.linalg.inv(Pp + zsh * np.eye(n))
    Cz = np.linalg.inv(Pp[np.ix_(K, K)] + zsh * np.eye(n - 1))
    tr_corr = np.trace(Xz[np.ix_(N, N)]) - np.trace(Cz[np.ix_(idxN, idxN)])
    exact = a * a * Xz[v, v] * xi @ (Cz[np.ix_(idxN, idxN)] @ Cz[np.ix_(idxN, idxN)]) @ xi
    bound = Zp[v] / zsh * (Gp[v, v] - Xz[v, v])
    print(f"    C5 z={zsh}: corr={tr_corr:.3e} exact={exact:.3e} bound={bound:.3e}",
          abs(tr_corr - exact) < 1e-12 and tr_corr <= bound + 1e-14)
# B5 pointwise with M = a^2 Y+/Z+, N = a^2 Y-/Z-
h = 0.1
Yp = np.linalg.inv(Pp[np.ix_(K, K)] + h * np.eye(n - 1))[np.ix_(idxN, idxN)]
Ym = np.linalg.inv(Pm[np.ix_(K, K)] + h * np.eye(n - 1))[np.ix_(idxN, idxN)]
M = a * a * Yp / Zp[v]
Nn = a * a * Ym / Zm[v]
pp = 6
H = 2 * (pp - 1) * M / alpha + 2 * pp * Nn / beta
lhsB5 = np.trace(M @ H @ H) / alpha
X1 = np.trace(M @ M) / alpha**2
X2 = np.trace(M @ Nn) / alpha / beta
rhsB5 = 8 * pp**2 * (np.linalg.norm(M, 2) * X1 / alpha + np.linalg.norm(Nn, 2) * X2 / beta)
print("    B5: tr(MH^2)/alpha <= 8p^2(|M| X1 t+ + |N| X2 t-):", lhsB5 <= rhsB5, lhsB5, rhsB5)
print("    M <= A:", np.linalg.eigvalsh(A - M).min() >= -1e-14,
      "  |M| <= s a^2/h:", np.linalg.norm(M, 2) <= 2.1 * a * a / h)

# ---------------------------------------------------------------- (b) ----
mp.mp.dps = 50
pp = 6
i_loc = 0
i = N[i_loc]


am = mp.mpf(float(a))


def full_mats(t):
    Pp_ = mp.matrix(n, n)
    Pm_ = mp.matrix(n, n)
    for r_ in range(n):
        for c_ in range(n):
            sv = mp.mpf(int(sig[r_, c_]))
            if {r_, c_} == {v, i}:
                sv = t
            Pp_[r_, c_] = am * sv
            Pm_[r_, c_] = -am * sv
        Pp_[r_, r_] = mp.mpf(float(Zp[r_]))
        Pm_[r_, r_] = mp.mpf(float(Zm[r_]))
    return Pp_, Pm_


def Phi_x(t):
    Pp_, Pm_ = full_mats(t)
    G = Pp_**-1
    return (mp.det(Pp_) * mp.det(Pm_))**pp * G[v, i]


def Phi(t):
    Pp_, Pm_ = full_mats(t)
    return (mp.det(Pp_) * mp.det(Pm_))**pp


t0 = mp.mpf(int(sig[v, i]))
d3 = mp.diff(Phi_x, t0, 3)
ratio = d3 / Phi(t0)
Pp_, Pm_ = full_mats(t0)
G = Pp_**-1
Gm_ = Pm_**-1
xx, zv = G[v, i], Gm_[v, i]
PP, QQ = G[v, v] * G[i, i], Gm_[v, v] * Gm_[i, i]
U = (pp - 1) * xx - pp * zv
V = (pp - 1) * (PP + xx**2) + pp * (QQ + zv**2)
W = (pp - 1) * (3 * PP * xx + xx**3) - pp * (3 * QQ * zv + zv**3)
Ki = xx * (8 * U**3 - 12 * U * V + 4 * W) - 3 * (PP - xx**2) * (4 * U**2 - 2 * V)
print("(b) Phi^-1 d^3(Phi x_i) vs a^3 K_i:", mp.nstr(ratio, 12), mp.nstr(am**3 * Ki, 12))


# CR2 rule D_i c_kj for k,j in N
def cij(t, k, j):
    Pp_, _ = full_mats(t)
    G = Pp_**-1
    return G[v, v] * G[k, j]


k, j = N[0], N[-1]
num = mp.diff(lambda t: cij(t, k, j), t0) / am
pred = -2 * G[v, i] * G[v, v] * G[k, j] - G[v, k] * G[v, v] * G[i, j] - G[v, v] * G[k, i] * G[v, j]
print("    CR2 D_i c_kj:", mp.nstr(num, 12), mp.nstr(pred, 12))

# ---------------------------------------------------------------- (c,d) --
pB = 5


def grid_setup(A2, B2, L=7.0, m=1201):
    s = np.linspace(-L, L, m)
    X, Y = np.meshgrid(s, s, indexing='ij')
    pts = np.stack([X, Y], -1)
    qA = np.einsum('...i,ij,...j->...', pts, A2, pts)
    qB = np.einsum('...i,ij,...j->...', pts, B2, pts)
    al = np.clip(1 - qA, 0, None)
    be = np.clip(1 - qB, 0, None)
    gam = np.exp(-(X**2 + Y**2) / 2) / (2 * np.pi)
    dA = (s[1] - s[0])**2
    return pts, qA, qB, al, be, gam, dA


def randpsd(scale):
    Mx = rng.normal(size=(2, 2))
    return scale * Mx @ Mx.T


for trial in range(3):
    A2 = randpsd(0.15)
    B2 = randpsd(0.15)
    pts, qA, qB, al, be, gam, dA = grid_setup(A2, B2)
    g = al**(pB - 1) * be**pB
    # (c) Gaussian IBP
    qA2 = np.einsum('...i,ij,...j->...', pts, A2 @ A2, pts)
    qAB = np.einsum('...i,ij,...j->...', pts, A2 @ B2, pts)
    F = (pB - 1) * qA2 * al**(pB - 2) * be**pB + pB * qAB * al**(pB - 1) * be**(pB - 1)
    lhs = 2 * np.sum(F * gam) * dA
    rhs = np.sum((np.trace(A2) - qA) * g * gam) * dA
    # (d) BL with M = c A, N = c' B (any M<=A, N<=B)
    M2 = 0.6 * A2
    N2 = 0.8 * B2
    w = g * gam
    Z = w.sum()
    Sig = np.einsum('abi,abj,ab->ij', pts, pts, w) / Z
    sup = (al > 0) & (be > 0)
    Hs = np.zeros(pts.shape[:2] + (2, 2))
    Hs[sup] = (2 * (pB - 1) * M2[None] / al[sup][:, None, None]
               + 2 * pB * N2[None] / be[sup][:, None, None])
    Kinv = np.linalg.inv(np.eye(2)[None, None] + Hs)
    EK = np.einsum('abij,ab->ij', Kinv, w) / Z
    H0 = 2 * (pB - 1) * M2 + 2 * pB * N2
    const = np.linalg.inv(np.eye(2) + H0)
    print(f"(c) trial {trial}: 2G[F]={lhs:.6e}  G[(trA-qA)g]={rhs:.6e}")
    print(f"(d)   min eig(E(I+H)^-1 - Sigma) = {np.linalg.eigvalsh(EK - Sigma if False else EK - Sig).min():.3e}"
          f"   min eig((I+H0)^-1 - Sigma) = {np.linalg.eigvalsh(const - Sig).min():.3e}")
    # paper's lower bound chain: tr A - E q_A >= E tr(M(H - H^2))
    lhs_tr = np.trace(A2) - np.trace(A2 @ Sig)
    MH = np.einsum('ij,...jk->...ik', M2, Hs)
    trMH = np.trace(MH, axis1=-2, axis2=-1)
    trMHH = np.trace(np.einsum('...ij,...jk->...ik', MH, Hs), axis1=-2, axis2=-1)
    rhs_tr = np.sum((trMH - trMHH) * w) / Z
    const_tr = np.trace(M2 @ (H0 - H0 @ H0))
    print(f"      trA - E q_A = {lhs_tr:.5e} >= E tr(M(H-H^2)) = {rhs_tr:.5e};"
          f"  constant-Hessian analogue tr(M(H0-H0^2)) = {const_tr:.5e}")

# sharper test in a small-H regime: tr(M(I-Sigma)) >= E tr(M H (I+H)^{-1}) (BL),
# compared with the constant-Hessian (Prekopa-only) bound tr(M H0 (I+H0)^{-1}).
for (pB2, sc) in [(20, 0.004), (40, 0.002), (12, 0.03)]:
    A2 = randpsd(sc) + sc * np.eye(2)
    B2 = randpsd(sc) + sc * np.eye(2)
    pts, qA, qB, al, be, gam, dA = grid_setup(A2, B2, L=8.0, m=1601)
    w = al**(pB2 - 1) * be**pB2 * gam
    Z = w.sum()
    Sig = np.einsum('abi,abj,ab->ij', pts, pts, w) / Z
    M2, N2 = 0.7 * A2, 0.9 * B2
    sup = (al > 0) & (be > 0)
    Hs = np.zeros(pts.shape[:2] + (2, 2))
    Hs[sup] = (2 * (pB2 - 1) * M2[None] / al[sup][:, None, None]
               + 2 * pB2 * N2[None] / be[sup][:, None, None])
    Kinv = np.linalg.inv(np.eye(2)[None, None] + Hs)
    HK = np.einsum('abij,abjk->abik', Hs, Kinv)
    val = np.sum(np.trace(np.einsum('ij,abjk->abik', M2, HK), axis1=-2, axis2=-1) * w) / Z
    H0 = 2 * (pB2 - 1) * M2 + 2 * pB2 * N2
    cval = np.trace(M2 @ H0 @ np.linalg.inv(np.eye(2) + H0))
    lhs = np.trace(M2 @ (np.eye(2) - Sig))
    Ealpha = np.sum(al * w) / Z
    print(f"(d') p={pB2}: tr(M(I-Sig))={lhs:.5e} >= BL {val:.5e} >= const {cval:.5e};"
          f"  ratio BL/const={val / cval:.3f}, E_nu alpha={Ealpha:.3f}")

# parallelogram inequality, random tests
worst = np.inf
for _ in range(20000):
    nn = 3
    Mx = rng.normal(size=(nn, nn))
    A3 = 0.3 * Mx @ Mx.T
    zv_, wv_ = rng.normal(size=nn) * 0.6, rng.normal(size=nn) * 0.6
    al = lambda u: 1 - u @ A3 @ u
    if al(zv_ + wv_) > 0 and al(zv_ - wv_) > 0:
        lhs = al(zv_ + wv_) * al(zv_ - wv_)
        rhs = al(zv_)**2 * np.exp(-2 * (wv_ @ A3 @ wv_) / al(zv_))
        worst = min(worst, rhs - lhs)
print("(d) parallelogram: min (rhs - lhs) over random tests =", worst)
