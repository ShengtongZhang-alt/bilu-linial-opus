"""Statement checks (workflow rule 2) for BiluLinial/Tight/Tools/{Alpha2,GaussDensity,GIBP2,Cov}.lean.

Gaussian expectations G[f] = E f(X), X ~ N(0, I_n), n = 0..3, by tensor trapezoid quadrature on
[-L, L]^n (n = 1, 2) and on a 3-D grid processed in slabs (n = 3). Lean junk values are mimicked:
x/0 = 0 in clipHess (2m/alpha with alpha = 0), inverse of a singular matrix = 0 (never hit here:
I + H with H PSD). All integrands are bounded by C(1 + |x|^2), so every Bochner integral is a
genuine Lebesgue integral (no integral-of-non-integrable = 0 trap); the script also prints the
grid maximum of the B2 integrand to confirm boundedness near the support boundary.
Run: /tmp/tight-venv/bin/python scripts/tight/check_tools_gauss.py
"""
import numpy as np

rng = np.random.default_rng(7)


def grid_batches(n, N, L=7.5):
    """yield (X, w): points (P, n) and quadrature weights including the Gaussian density"""
    if n == 0:
        yield np.zeros((1, 0)), np.ones(1)
        return
    t = np.linspace(-L, L, N)
    h = t[1] - t[0]
    wt = np.full(N, h)
    wt[0] = wt[-1] = h / 2
    dens = np.exp(-t ** 2 / 2) / np.sqrt(2 * np.pi)
    w1 = wt * dens
    if n == 1:
        yield t[:, None], w1
    elif n == 2:
        X1, X2 = np.meshgrid(t, t, indexing="ij")
        yield np.stack([X1.ravel(), X2.ravel()], 1), np.outer(w1, w1).ravel()
    else:
        X2, X3 = np.meshgrid(t, t, indexing="ij")
        W23 = np.outer(w1, w1).ravel()
        P23 = np.stack([X2.ravel(), X3.ravel()], 1)
        for a in range(N):
            if w1[a] < 1e-30:
                continue
            X = np.concatenate([np.full((P23.shape[0], 1), t[a]), P23], 1)
            yield X, w1[a] * W23


def qf(M, X):
    return np.einsum("pi,ij,pj->p", X, M, X) if X.shape[1] else np.zeros(X.shape[0])


def rand_psd(n, kind="generic", scale=1.0):
    if n == 0:
        return np.zeros((0, 0))
    if kind == "zero":
        return np.zeros((n, n))
    if kind == "rank1":
        v = rng.normal(size=n)
        return np.outer(v, v) * scale
    X = rng.normal(size=(n, n))
    return X @ X.T * scale / n


def psd_below(A):
    n = A.shape[0]
    if n == 0:
        return A.copy()
    w, U = np.linalg.eigh(A)
    R = U @ np.diag(np.sqrt(np.clip(w, 0, None))) @ U.T
    Q, _ = np.linalg.qr(rng.normal(size=(n, n)))
    S = Q @ np.diag(rng.uniform(0, 1, size=n)) @ Q.T
    return R @ S @ R


def ldivv(c, v):
    out = np.zeros_like(v)
    nz = v != 0
    out[nz] = c / v[nz]
    return out


def integrals(n, N, A, B, M, Nm, T, m, mp_, p, c):
    """all Gaussian expectations needed for one parameter set"""
    I = np.eye(n)
    acc = {}

    def add(k, v):
        acc[k] = acc.get(k, 0.0) + v

    trA = np.trace(A) if n else 0.0
    trM = np.trace(M) if n else 0.0
    supB2 = 0.0
    for X, w in grid_batches(n, N):
        qA, qB, qT, qM = qf(A, X), qf(B, X), qf(T, X), qf(M, X)
        al, be = np.maximum(1 - qA, 0), np.maximum(1 - qB, 0)
        # BLG with phi = alpha^m beta^m'
        phi = al ** m * be ** mp_
        cA, cB = ldivv(2.0 * m, al), ldivv(2.0 * mp_, be)
        if n:
            Hs = cA[:, None, None] * M[None] + cB[:, None, None] * Nm[None]
            Ri = np.linalg.inv(I[None] + Hs)
            trTR = np.einsum("ij,pji->p", T, Ri)
        else:
            trTR = np.zeros(X.shape[0])
        add("G[qT phi]", np.dot(w, qT * phi))
        add("G[tr(T(I+H)^-1) phi]", np.dot(w, trTR * phi))
        add("G[phi]", np.dot(w, phi))
        # star quantities, H = clipHess (p-1) p A B M N
        g = al ** max(p - 1, 0) * be ** p
        Phi = al ** p * be ** p
        add("G[g]", np.dot(w, g))
        add("G[Phi]", np.dot(w, Phi))
        add("NG", np.dot(w, (trA - qA) * g))
        add("G[qA g]", np.dot(w, qA * g))
        if p >= 2:
            qA2, qAB = qf(A @ A, X), qf(A @ B, X)
            F = max(p - 1, 0) * qA2 * al ** (p - 2) * be ** p + p * qAB * al ** (p - 1) * be ** (p - 1)
            add("G[F]", np.dot(w, F))
        if p >= 1 and n:
            c1, c2 = ldivv(2.0 * max(p - 1, 0), al), ldivv(2.0 * p, be)
            H = c1[:, None, None] * M[None] + c2[:, None, None] * Nm[None]
            MH = np.einsum("ij,pjk->pik", M, H)
            trMH = np.einsum("pii->p", MH)
            trMH2 = np.einsum("pij,pji->p", MH, H)
            integ = g * (trMH - trMH2)
            supB2 = max(supB2, float(np.abs(integ).max()))
            add("G[g tr(M(H-H^2))]", np.dot(w, integ))
            Ri = np.linalg.inv(I[None] + H)
            add("G[g tr(M(I-(I+H)^-1))]", np.dot(w, g * (trM - np.einsum("ij,pji->p", M, Ri))))
            exp_int = Phi * (max(p - 1, 0) * np.trace(M @ M) * ldivv(1.0, al ** 2)
                             + p * np.trace(M @ Nm) * ldivv(1.0, al * be)
                             - trMH2 * ldivv(1.0, 2 * al))
            add("G[B2 expanded]", np.dot(w, exp_int))
    acc["supB2"] = supB2
    return acc


def polar_gibp2(A, B, p, nth=1500):
    """(2 G[F], G[(tr A - q_A) g]) for n = 2 by polar quadrature (radial split at the boundary)"""
    from scipy import integrate
    ths = (np.arange(nth) + 0.5) * 2 * np.pi / nth
    A2, AB, trA = A @ A, A @ B, np.trace(A)
    sF = sN = 0.0
    for th in ths:
        u = np.array([np.cos(th), np.sin(th)])
        qa, qb, qa2, qab = u @ A @ u, u @ B @ u, u @ A2 @ u, u @ AB @ u
        R = min([1 / np.sqrt(c) for c in (qa, qb) if c > 1e-300] + [12.0])
        F = lambda r: ((p - 1) * qa2 * max(1 - qa * r * r, 0) ** (p - 2) * max(1 - qb * r * r, 0) ** p
                       + p * qab * max(1 - qa * r * r, 0) ** (p - 1) * max(1 - qb * r * r, 0) ** (p - 1)) \
            * r ** 3 * np.exp(-r * r / 2) / (2 * np.pi)
        N = lambda r: (trA - qa * r * r) * max(1 - qa * r * r, 0) ** (p - 1) * max(1 - qb * r * r, 0) ** p \
            * r * np.exp(-r * r / 2) / (2 * np.pi)
        sF += integrate.quad(F, 0, R, epsabs=1e-15, epsrel=1e-13)[0]
        sN += integrate.quad(N, 0, R, epsabs=1e-15, epsrel=1e-13)[0]
    dth = 2 * np.pi / nth
    return 2 * sF * dth, sN * dth


fails = {}


def record(name, ok, info=""):
    d = fails.setdefault(name, [0, 0, ""])
    d[0] += 1
    if not ok:
        d[1] += 1
        if not d[2]:
            d[2] = info


# ---------- quadrature accuracy sanity: G[q_T] = tr T, G[1] = 1 ----------
for n, N in ((1, 4001), (2, 801), (3, 161)):
    T = rand_psd(n)
    s0 = s1 = 0.0
    for X, w in grid_batches(n, N):
        s0 += w.sum()
        s1 += np.dot(w, qf(T, X))
    print(f"[quad n={n} N={N}] G[1]-1 = {s0 - 1:.1e}, G[q_T]-trT = {s1 - np.trace(T):.1e}")

# ---------- BP_TOOLS docstring numbers (T.COV check, n = 1, B = 0, p = 2, A = 1) ----------
acc = integrals(1, 20001, np.eye(1), np.zeros((1, 1)), np.eye(1), np.zeros((1, 1)), np.eye(1), 1, 0, 2, 0)
print(f"[doc] n=1 A=1 B=0 p=2: N_G = {acc['NG']:.4f} (doc 0.3975), bound G[g]*2/3 = {acc['G[g]'] * 2 / 3:.4f} (doc 0.3226)")

# ---------- random trials ----------
CASES = []
for n, N in ((0, 1), (1, 6001), (2, 701), (3, 121)):
    for trial in range({0: 4, 1: 60, 2: 40, 3: 6}[n]):
        kinds = ["generic", "generic", "zero", "rank1"]
        A = rand_psd(n, kinds[rng.integers(0, 4)], scale=float(10 ** rng.uniform(-1, 1.3)))
        B = rand_psd(n, kinds[rng.integers(0, 4)], scale=float(10 ** rng.uniform(-1, 1.3)))
        ext = rng.integers(0, 4)  # extreme Loewner bounds: M = A, N = B / M = 0, N = 0
        M, Nm = {0: (psd_below(A), psd_below(B)), 1: (A.copy(), B.copy()),
                 2: (0 * A, 0 * B), 3: (A.copy(), 0 * B)}[int(ext)]
        T = rand_psd(n, kinds[rng.integers(0, 4)])
        m, mp_ = int(rng.choice([0, 1, 2, 3, 6])), int(rng.choice([0, 1, 2, 5]))
        p = int(rng.choice([0, 1, 2, 3, 3, 4, 6, 12]))
        CASES.append((n, N, A, B, M, Nm, T, m, mp_, p))

for (n, N, A, B, M, Nm, T, m, mp_, p) in CASES:
    acc = integrals(n, N, A, B, M, Nm, T, m, mp_, p, 0)
    tol = {0: 1e-12, 1: 2e-7, 2: 2e-5, 3: 2e-3}[n]
    I = np.eye(n)
    tag = f"n={n} p={p} m={m} m'={mp_}"
    # T.BLG variable modulus (any m, m')
    record("gaussE_qForm_mul_clipProd_le", acc["G[qT phi]"] <= acc["G[tr(T(I+H)^-1) phi]"] + tol, tag)
    # T.BLG constant modulus, c in [0, 2m]
    for c in (0.0, 2.0 * m * rng.uniform(), 2.0 * m):
        trc = np.trace(T @ np.linalg.inv(I + c * A)) if n else 0.0
        record("gaussE_qForm_mul_clipProd_le_const", acc["G[qT phi]"] <= trc * acc["G[phi]"] + tol, tag + f" c={c}")
    # T.COV
    trA = np.trace(A) if n else 0.0
    trA2 = np.trace(A @ A) if n else 0.0
    cc = 2.0 * max(p - 1, 0)
    lmax = float(np.linalg.eigvalsh(A)[-1]) if n else 0.0
    for l in (lmax, 2 * lmax + 0.1, trA):
        record("gaussE_NG_ge_of_le / _opNorm", acc["G[g]"] * cc * trA2 / (1 + cc * l) <= acc["NG"] + tol, tag)
    record("gaussE_NG_nonneg", acc["NG"] >= -tol, tag + f" NG={acc['NG']}")
    if p >= 2:
        record("gaussE_NG_ge_whitened", acc["G[Phi]"] * trA2 / (1 + trA) <= acc["NG"] + tol, tag)
    if p >= 3:
        # T.GIBP2
        rel = abs(2 * acc["G[F]"] - acc["NG"]) / (1e-12 + abs(acc["NG"]) + abs(2 * acc["G[F]"]))
        # grid error at the clipping kink is O(h^2); exact check in check_tools_gibp2_1d.py
        ok = abs(2 * acc["G[F]"] - acc["NG"]) <= 10 * tol + 1e-4 * abs(acc["NG"])
        if not ok and n == 2:
            l2, r2 = polar_gibp2(A, B, p)
            print(f"[GIBP2 grid miss n=2 p={p}, eig(A)={np.linalg.eigvalsh(A).round(3)}]: grid 2GF={2 * acc['G[F]']:.6f}"
                  f" NG={acc['NG']:.6f}; polar 2GF={l2:.10f} NG={r2:.10f}")
            ok = abs(l2 - r2) <= 1e-8 * (abs(l2) + abs(r2))
        record("two_mul_gaussE_starF (identity; grid, polar if grid misses)", ok,
               tag + f" 2GF={2 * acc['G[F]']:.6g} NG={acc['NG']:.6g}")
        # B2
        if n:
            record("gaussE_starG_trace_le (B2)", acc["G[g tr(M(H-H^2))]"] <= 2 * acc["G[F]"] + 10 * tol, tag)
            record("  B2 chain: G[g tr(M(H-H^2))] <= G[g tr(M(I-(I+H)^-1))]",
                   acc["G[g tr(M(H-H^2))]"] <= acc["G[g tr(M(I-(I+H)^-1))]"] + tol, tag)
            record("gaussE_starPhi_B2_le (expanded)", acc["G[B2 expanded]"] <= acc["G[F]"] + 10 * tol, tag)
            record("  expanded B2 integrand = half the B2 integrand",
                   abs(acc["G[B2 expanded]"] - acc["G[g tr(M(H-H^2))]"] / 2) <= 1e-9 * (1 + abs(acc["G[B2 expanded]"])), tag)
            record("  B2 integrand bounded on grid (p>=3)", acc["supB2"] < 1e8, tag + f" sup={acc['supB2']}")

# n = 0 (empty index type): direct evaluation at the single point
print("\n== Gaussian statements (quadrature n=0..3) ==")
for k, (tot, bad, info) in fails.items():
    print(f"{k:60s} trials={tot:4d} fails={bad} {info}")

# ---------- informational: does the constant form fail for c > 2m? ----------
worst = -1e9
for trial in range(30):
    A = rand_psd(1, scale=float(10 ** rng.uniform(-1, 1)))
    T = np.eye(1)
    m = int(rng.choice([1, 2]))
    acc = integrals(1, 6001, A, np.zeros((1, 1)), A, np.zeros((1, 1)), T, m, 0, 3, 0)
    c = 6.0 * m
    worst = max(worst, acc["G[qT phi]"] - 1 / (1 + c * A[0, 0]) * acc["G[phi]"])
print(f"[info] constant BLG with c = 6m > 2m: max(LHS - RHS) = {worst:.3g} (positive => c <= 2m is needed)")

# ---------- T.ALPHA2 pointwise (already proved; sanity) ----------
bad = 0
for trial in range(20000):
    n = int(rng.integers(1, 5))
    A = rand_psd(n, ["generic", "rank1", "zero"][rng.integers(0, 3)], scale=float(10 ** rng.uniform(-1, 1)))
    z, wv = rng.normal(size=n) * rng.uniform(0, 2), rng.normal(size=n) * rng.uniform(0, 2)
    al = lambda x: max(1 - x @ A @ x, 0.0)
    a0 = al(z)
    rhs = a0 ** 2 * np.exp(-(0.0 if a0 == 0 else 2 * (wv @ A @ wv) / a0))
    if al(z + wv) * al(z - wv) > rhs + 1e-12:
        bad += 1
    if al(z + wv) * al(z - wv) > a0 ** 2 * np.exp(-2 * (wv @ A @ wv)) + 1e-12:
        bad += 1
print(f"[T.ALPHA2 pointwise] 20000 trials, failures = {bad}")
