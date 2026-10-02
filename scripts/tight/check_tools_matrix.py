"""Statement checks (workflow rule 2) for BiluLinial/Tight/Tools/{MatrixFacts,Interp}.lean
and the matrix input of Tools/Cov.lean (trace_sub_trace_mul_inv_ge).

Random symmetric / PSD matrices of sizes 0..6, including singular, rank-one, zero and
ill-conditioned ones; Lean junk values are mimicked where a statement could hit them
(inverse of a singular matrix = 0, x/0 = 0, sqrt of a negative = 0).
Run: /tmp/tight-venv/bin/python scripts/tight/check_tools_matrix.py
"""
import numpy as np

rng = np.random.default_rng(20261001)
TOL = 1e-9


def linv(M):
    """Lean's Matrix.inv: the inverse if det != 0, else 0."""
    if M.shape[0] == 0:
        return M.copy()
    if abs(np.linalg.det(M)) < 1e-300:
        return np.zeros_like(M)
    return np.linalg.inv(M)


def ldiv(x, y):
    return 0.0 if y == 0 else x / y


def mineig(M):
    if M.shape[0] == 0:
        return 0.0
    return float(np.linalg.eigvalsh((M + M.T) / 2)[0])


def is_psd(M, scale=1.0):
    return np.allclose(M, M.T, atol=1e-9 * max(1.0, scale)) and mineig(M) >= -TOL * max(1.0, scale)


def opnorm(M):
    if M.shape[0] == 0:
        return 0.0
    return float(np.linalg.norm(M, 2))


def tr(M):
    return float(np.trace(M)) if M.shape[0] else 0.0


def rand_psd(n, kind):
    if n == 0:
        return np.zeros((0, 0))
    if kind == "zero":
        return np.zeros((n, n))
    if kind == "rank1":
        v = rng.normal(size=n)
        return np.outer(v, v) * rng.uniform(0.1, 3)
    if kind == "singular":
        r = rng.integers(0, n)
        X = rng.normal(size=(n, r))
        return X @ X.T
    if kind == "illcond":
        Q, _ = np.linalg.qr(rng.normal(size=(n, n)))
        ev = 10.0 ** rng.uniform(-8, 3, size=n)
        return Q @ np.diag(ev) @ Q.T
    if kind == "large":
        X = rng.normal(size=(n, n)) * 30
        return X @ X.T
    X = rng.normal(size=(n, n))
    return X @ X.T * rng.uniform(0.01, 2)


def rand_sym(n):
    X = rng.normal(size=(n, n))
    return (X + X.T) / 2 * rng.uniform(0.1, 5)


KINDS = ["generic", "zero", "rank1", "singular", "illcond", "large"]
fails = {}


def record(name, ok, info=""):
    d = fails.setdefault(name, [0, 0, ""])
    d[0] += 1
    if not ok:
        d[1] += 1
        if not d[2]:
            d[2] = info


def psd_below(A):
    """random M with 0 <= M <= A"""
    n = A.shape[0]
    if n == 0:
        return A.copy()
    w, U = np.linalg.eigh(A)
    w = np.clip(w, 0, None)
    R = U @ np.diag(np.sqrt(w)) @ U.T
    Q, _ = np.linalg.qr(rng.normal(size=(n, n)))
    S = Q @ np.diag(rng.uniform(0, 1, size=n)) @ Q.T
    return R @ S @ R


for trial in range(6000):
    n = int(rng.integers(0, 7))
    kM, kX, kY = (KINDS[rng.integers(0, len(KINDS))] for _ in range(3))
    M, X, Yp = rand_psd(n, kM), rand_psd(n, kX), rand_psd(n, kY)
    I = np.eye(n)
    sc = 1 + opnorm(M) * (1 + opnorm(X) + opnorm(Yp)) ** 2
    # T.MAT-0
    record("trace_mul_nonneg", tr(M @ X) >= -TOL * sc)
    # (i): X <= Y := X + Yp
    Y = X + Yp
    record("trace_mul_le_trace_mul", tr(M @ X) <= tr(M @ Y) + TOL * sc)
    # (ii)
    N = X
    lam = opnorm(N) * rng.choice([1.0, 1.0, 1.5, 10.0])
    record("posSemidef_smul_sub_mul_self", is_psd(lam * N - N @ N, 1 + lam ** 2),
           f"n={n} kind={kX} lam={lam:.3g} mineig={mineig(lam * N - N @ N):.3g}")
    record("trace_mul_mul_self_le", tr(M @ N @ N) <= lam * tr(M @ N) + TOL * sc)
    S = rand_sym(n)
    record("posSemidef_opNorm_smul_sub", is_psd(opnorm(S) * I - S, 1 + opnorm(S)))
    record("posSemidef_trace_smul_sub", is_psd(tr(N) * I - N, 1 + tr(N)))
    record("trace_mul_le_trace_mul_trace", tr(M @ N) <= tr(M) * tr(N) + TOL * sc)
    # (iii)
    H1, H2 = rand_sym(n), rand_sym(n)
    record("posSemidef_two_sq_add_two_sq_sub_sq",
           is_psd(2 * H1 @ H1 + 2 * H2 @ H2 - (H1 + H2) @ (H1 + H2), 1 + opnorm(H1) ** 2 + opnorm(H2) ** 2))
    # (iv)
    H = X
    R = linv(I + H)
    sH = 1 + opnorm(H) ** 2
    record("posSemidef_inv_one_add", is_psd(R, sH))
    record("posSemidef_one_sub_inv_one_add", is_psd(I - R, sH))
    record("posSemidef_one_sub_inv_sub", is_psd(I - R - (H - H @ H), sH))
    record("trace_mul_sub_sq_le", tr(M @ (H - H @ H)) <= tr(M) - tr(M @ R) + TOL * sc * sH)
    record("trace_mul_inv_one_add_mem", -TOL * sc <= tr(M @ R) <= tr(M) + TOL * sc)
    # (v)
    P = X
    h = float(10.0 ** rng.uniform(-6, 2))
    K = linv(P + h * I)
    record("posSemidef_inv_smul_sub_inv_add", is_psd(I / h - K, 1 / h))
    record("opNorm_inv_add_smul_le", opnorm(K) <= 1 / h * (1 + 1e-9))
    if n == 0 or mineig(P) > 1e-6 * (1 + opnorm(P)):
        z = float(rng.choice([0.0, 10.0 ** rng.uniform(-4, 3)]))
        Pi, Pz = linv(P), linv(P + z * I)
        s5 = 1 + opnorm(Pi) ** 2 * (1 + z)
        record("inv_sub_inv_add_smul", np.allclose(Pi - Pz, z * Pi @ Pz, atol=1e-7 * s5))
        record("posSemidef_inv_sub_inv_add_sub", is_psd(Pi - Pz - z * Pz @ Pz, s5))
    # (vi)
    Xs = rand_sym(n)
    if n > 0:
        kk = int(rng.integers(0, n + 1))
        f = rng.permutation(n)[:kk]
        sub = (Xs @ Xs)[np.ix_(f, f)] - Xs[np.ix_(f, f)] @ Xs[np.ix_(f, f)]
        record("posSemidef_submatrix_mul_self_sub", is_psd(sub, 1 + opnorm(Xs) ** 2))
    # (vii)
    record("opNorm_le_opNorm_add", opnorm(Yp) <= opnorm(X + Yp) * (1 + 1e-12) + 1e-12)
    # (viii): M <= A (A = M + X), S <= I (S = I - Yp), M arbitrary symmetric allowed
    Ms = rand_sym(n)
    A = Ms + X
    Sm = I - Yp
    record("trace_mul_one_sub_le", tr(Ms @ (I - Sm)) <= tr(A @ (I - Sm)) + TOL * (1 + opnorm(A)) * (1 + opnorm(Yp)))
    # B5
    Nn = rand_psd(n, KINDS[rng.integers(0, len(KINDS))])
    a, b = float(10.0 ** rng.uniform(-2, 1)), float(10.0 ** rng.uniform(-2, 1))
    p = int(rng.integers(0, 12))
    c1, c2 = 2 * max(p - 1, 0) / a, 2 * p / b
    Hh = c1 * M + c2 * Nn
    lhs = tr(M @ Hh @ Hh) / a
    rhs = 8 * p ** 2 * (opnorm(M) * (tr(M @ M) / a ** 2) * (1 / a) + opnorm(Nn) * (tr(M @ Nn) / (a * b)) * (1 / b))
    record("trace_mul_hess_sq_div_le (B5)", lhs <= rhs + 1e-9 * (1 + abs(rhs)), f"n={n} p={p} {lhs} {rhs}")
    L = max(opnorm(M), opnorm(Nn)) * rng.choice([1.0, 2.0])
    rhs2 = 8 * p ** 2 * L * (tr(M @ M) / a ** 2 * (1 / a) + tr(M @ Nn) / (a * b) * (1 / b))
    record("trace_mul_hess_sq_div_le' (B5)", lhs <= rhs2 + 1e-9 * (1 + abs(rhs2)))
    # Cov matrix input
    Aa = X
    l = opnorm(Aa) * rng.choice([1.0, 1.0, 3.0])
    c = float(rng.choice([0.0, 10.0 ** rng.uniform(-3, 3)]))
    lhs = c * tr(Aa @ Aa) / (1 + c * l)
    rhs = tr(Aa) - tr(Aa @ linv(I + c * Aa))
    record("trace_sub_trace_mul_inv_ge (Cov)", lhs <= rhs + 1e-9 * (1 + abs(rhs)) * (1 + c), f"{lhs} {rhs}")

# hypotheses are needed (expected failures without them; informational)
P = np.diag([1.0, 0.0])
Pi, Pz = linv(P), linv(P + 1.0 * np.eye(2))
print("[info] inv_sub_inv_add_smul with P PSD singular (Lean junk P^-1=0): holds?",
      np.allclose(Pi - Pz, 1.0 * Pi @ Pz), "-> PosDef hypothesis needed (present)")
Xs = np.array([[2.0, 0.0], [0.0, 0.0]])
f = [0, 0]
sub = (Xs @ Xs)[np.ix_(f, f)] - Xs[np.ix_(f, f)] @ Xs[np.ix_(f, f)]
print("[info] (vi) with non-injective f: min eig", mineig(sub), "-> injectivity needed (present)")

print("\n== MatrixFacts / B5 / Cov matrix input ==")
for k, (tot, bad, info) in fails.items():
    print(f"{k:42s} trials={tot:5d} fails={bad} {info}")

# ---------------- Interp.lean (finite weighted averages) ----------------
fails.clear()


def wavg(w, f):
    s = w.sum()
    return 0.0 if s == 0 else float((w * f).sum() / s)


def rp(x, e):
    """Real.rpow for x >= 0"""
    if x == 0:
        return 1.0 if e == 0 else 0.0
    return x ** e


for trial in range(20000):
    n = int(rng.integers(1, 9))
    w = rng.uniform(0, 1, size=n) * (rng.uniform(size=n) < 0.8)
    if w.sum() == 0:
        w[0] = 0.5
    X = rng.exponential(size=n) * (rng.uniform(size=n) < 0.7)
    Y = rng.exponential(size=n) * (rng.uniform(size=n) < 0.7) * rng.choice([1, 10])
    if rng.uniform() < 0.05:
        X[:] = 0
    k = int(rng.integers(1, 6))
    tol = 1e-9
    lhs = wavg(w, X * Y)
    rhs = rp(wavg(w, X), 1 - 1 / k) * rp(wavg(w, X * Y ** k), 1 / k)
    record("wavg_mul_le_holder", lhs <= rhs * (1 + tol) + tol)
    Xr, Yr = rng.normal(size=n), rng.normal(size=n)
    record("wavg_mul_sq_le", wavg(w, Xr * Yr) ** 2 <= wavg(w, Xr ** 2) * wavg(w, Yr ** 2) * (1 + tol) + tol)
    # T.IL at tight constants
    m = wavg(w, X) * rng.choice([1.0, 1.0, 2.0])
    if m > 0:
        th = m * rng.choice([1.0, rng.uniform(1e-3, 1)])
        BX = np.sqrt(wavg(w, X ** 2))
        BY = wavg(w, Y ** (2 * k)) ** (1 / (2 * k))
        rhs = m * th ** (-1 / k) * rp(BX, 1 / k) * BY
        record("wavg_mul_le_interp", lhs <= rhs * (1 + tol) + tol)
    # T.DSTAR
    nS = int(rng.integers(1, 5))
    XX = rng.exponential(size=(nS, n)) * (rng.uniform(size=(nS, n)) < 0.7)
    mm = int(rng.integers(0, 6))
    Bm = max(wavg(w, XX[u] ** mm) for u in range(nS))
    lhs2 = wavg(w, XX.max(axis=0) ** mm)
    record("wavg_sup_pow_le", lhs2 <= nS * Bm * (1 + tol) + tol)
    if mm >= 1:
        B0 = Bm ** (1 / mm)
        record("wavg_sup_pow_rpow_le", rp(lhs2, 1 / mm) <= nS ** (1 / mm) * B0 * (1 + tol) + tol)
    # Hölder (k, k/(k-1)) and UMI
    Z = rng.exponential(size=n) * (rng.uniform(size=n) < 0.7)
    lhs3 = wavg(w, X * Z ** (k - 1))
    rhs3 = rp(wavg(w, X ** k), 1 / k) * rp(wavg(w, Z ** k), 1 - 1 / k)
    record("wavg_mul_pow_pred_le", lhs3 <= rhs3 * (1 + tol) + tol)
    kk = int(rng.integers(2, 7))
    Mm = wavg(w, X ** kk) ** (1 / kk) * rng.choice([1.0, 1.0, 3.0])
    Bb = wavg(w, Z ** kk) ** (1 / kk) * rng.choice([1.0, 1.0, 3.0])
    th = float(10.0 ** rng.uniform(-4, 2))
    lhs4 = wavg(w, X * Z)
    rhs4 = Bb * rp(Mm / th, 1 / (kk - 1)) * (wavg(w, X) + th)
    record("wavg_mul_le_umi", lhs4 <= rhs4 * (1 + tol) + tol, f"{lhs4} {rhs4}")
    # basics
    f, g = rng.normal(size=n), rng.normal(size=n)
    g = np.maximum(f, g)
    record("wavg_mono", wavg(w, f) <= wavg(w, g) + tol)
    record("wavg_nonneg", wavg(w, np.abs(f)) >= 0)
    record("wavg_const", abs(wavg(w, np.full(n, 3.7)) - 3.7) < 1e-12)

# Docstring checks of the BP_TOOLS entry: constants
print("\n== Interp ==")
for k, (tot, bad, info) in fails.items():
    print(f"{k:42s} trials={tot:5d} fails={bad} {info}")
