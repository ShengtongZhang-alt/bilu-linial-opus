"""Numerical checks for the GCI node (GR1 of docs/second_order_bilu_linial_tight.tex).

Target:  G[ <AX,BX> alpha^{p-1} beta^{p-1} ] >= 0,
  alpha = (1 - x^T A x)_+, beta = (1 - x^T B x)_+, A, B PSD, X standard Gaussian.

Checks:
  1. Monte Carlo of the target for random PSD A, B (several shapes, p).
  2. Conditional form: E[<AX,BX> | q_A in bin, q_B in bin] >= 0 on a 2D histogram.
  3. Special case (i): tr(X Y (I+X+Y)^{-1}) >= 0 and the closed form of
     E[<AX,BX> e^{-a q_A - b q_B}].
  4. Special case (ii): E[<AX,BX> e^{-a q_A} psi(q_B)] >= 0 for clipped psi, and the
     identity with tr(A B' N).
  5. Royen exponential-sum route: for slab boxes, the explicit function
     F(s) = sum_j c_j det(I + diag(lambda_j) C(s))^{-1/2}
     equals the Monte Carlo value of E[prod_i phi_i(Z_i(s))] and is nondecreasing in s.
"""

import itertools
import math

import numpy as np

rng = np.random.default_rng(20260930)


def rand_psd(n, rank=None, scale=1.0):
    rank = n if rank is None else rank
    M = rng.normal(size=(n, rank))
    A = M @ M.T
    return scale * A / np.trace(A)


def target_mc(A, B, p, nsamp=400_000, batch=100_000):
    n = A.shape[0]
    tot = 0.0
    tot2 = 0.0
    m = 0
    while m < nsamp:
        X = rng.normal(size=(batch, n))
        AX = X @ A
        BX = X @ B
        qA = np.einsum("ij,ij->i", X, AX)
        qB = np.einsum("ij,ij->i", X, BX)
        w = np.maximum(1 - qA, 0) ** (p - 1) * np.maximum(1 - qB, 0) ** (p - 1)
        v = np.einsum("ij,ij->i", AX, BX) * w
        tot += v.sum()
        tot2 += (v**2).sum()
        m += batch
    mean = tot / m
    sd = math.sqrt(max(tot2 / m - mean**2, 0) / m)
    return mean, sd


def check_target():
    print("== 1. Monte Carlo of G[<AX,BX> alpha^{p-1} beta^{p-1}] ==")
    worst = None
    for trial in range(12):
        n = int(rng.integers(2, 7))
        rA = int(rng.integers(1, n + 1))
        rB = int(rng.integers(1, n + 1))
        A = rand_psd(n, rA, scale=float(rng.uniform(0.3, 2.0)))
        B = rand_psd(n, rB, scale=float(rng.uniform(0.3, 2.0)))
        # make <Ax,Bx> indefinite: random rotation of B
        p = int(rng.integers(2, 9))
        mean, sd = target_mc(A, B, p)
        ev = np.linalg.eigvalsh((A @ B + B @ A) / 2)
        print(f"n={n} rA={rA} rB={rB} p={p}  mean={mean:+.3e}  sd={sd:.1e}  "
              f"z={mean / sd:+.1f}  eig(sym AB) in [{ev.min():+.2e},{ev.max():+.2e}]")
        if worst is None or mean / sd < worst:
            worst = mean / sd
    print("worst z-score:", worst)


def check_conditional(n=4, nsamp=2_000_000):
    print("== 2. Conditional positivity on a 2D histogram ==")
    A = rand_psd(n, scale=1.5)
    Q, _ = np.linalg.qr(rng.normal(size=(n, n)))
    B = Q @ np.diag(rng.uniform(0, 1, size=n)) @ Q.T
    X = rng.normal(size=(nsamp, n))
    AX = X @ A
    BX = X @ B
    qA = np.einsum("ij,ij->i", X, AX)
    qB = np.einsum("ij,ij->i", X, BX)
    w = np.einsum("ij,ij->i", AX, BX)
    print("fraction of samples with <AX,BX> < 0:", (w < 0).mean())
    ea = np.quantile(qA, np.linspace(0, 1, 9))
    eb = np.quantile(qB, np.linspace(0, 1, 9))
    ia = np.clip(np.searchsorted(ea, qA) - 1, 0, 7)
    ib = np.clip(np.searchsorted(eb, qB) - 1, 0, 7)
    worst = np.inf
    for a in range(8):
        for b in range(8):
            sel = (ia == a) & (ib == b)
            if sel.sum() < 2000:
                continue
            m = w[sel].mean()
            s = w[sel].std() / math.sqrt(sel.sum())
            worst = min(worst, m / s)
    print("min over bins of (bin mean / bin sd):", worst)


def check_special_i():
    print("== 3. Special case (i): exponential weights ==")
    worst = np.inf
    for _ in range(2000):
        n = int(rng.integers(1, 7))
        Xm = rand_psd(n, int(rng.integers(1, n + 1)), scale=float(rng.uniform(0.01, 30)))
        Ym = rand_psd(n, int(rng.integers(1, n + 1)), scale=float(rng.uniform(0.01, 30)))
        v = np.trace(Xm @ Ym @ np.linalg.inv(np.eye(n) + Xm + Ym))
        worst = min(worst, v)
    print("min tr(XY(I+X+Y)^{-1}) over random PSD pairs:", worst)
    n = 4
    A = rand_psd(n, scale=1.0)
    B = rand_psd(n, 2, scale=1.0)
    a, b = 0.7, 1.3
    N = 1_000_000
    X = rng.normal(size=(N, n))
    AX = X @ A
    BX = X @ B
    qA = np.einsum("ij,ij->i", X, AX)
    qB = np.einsum("ij,ij->i", X, BX)
    mc = (np.einsum("ij,ij->i", AX, BX) * np.exp(-a * qA - b * qB)).mean()
    M = np.eye(n) + 2 * a * A + 2 * b * B
    exact = np.linalg.det(M) ** -0.5 * np.trace(A @ B @ np.linalg.inv(M))
    print(f"E[<AX,BX> e^(-a qA - b qB)]: MC {mc:.5f}  closed form {exact:.5f}")


def check_special_ii():
    print("== 4. Special case (ii): one exponential, one clipped factor ==")
    n = 4
    A = rand_psd(n, scale=1.0)
    B = rand_psd(n, 3, scale=1.2)
    a = 0.8
    p = 5
    N = 2_000_000
    X = rng.normal(size=(N, n))
    AX = X @ A
    BX = X @ B
    qA = np.einsum("ij,ij->i", X, AX)
    qB = np.einsum("ij,ij->i", X, BX)
    psi = np.maximum(1 - qB, 0) ** (p - 1)
    mc = (np.einsum("ij,ij->i", AX, BX) * np.exp(-a * qA) * psi).mean()
    Sig = np.linalg.inv(np.eye(n) + 2 * a * A)
    w, V = np.linalg.eigh(Sig)
    Sh = V @ np.diag(np.sqrt(w)) @ V.T
    Bp = Sh @ B @ Sh
    Z = rng.normal(size=(N, n))
    qBp = np.einsum("ij,ij->i", Z, Z @ Bp)
    Nmat = (Z[:, :, None] * Z[:, None, :] * (np.maximum(1 - qBp, 0) ** (p - 1))[:, None, None]).mean(0)
    pred = np.linalg.det(Sig) ** 0.5 * np.trace(A @ Bp @ Nmat)
    comm = np.abs(Bp @ Nmat - Nmat @ Bp).max()
    print(f"MC {mc:.5f}   det(Sig)^(1/2) tr(A B' N) = {pred:.5f}   |[B',N]|_max = {comm:.1e}")


def royen_phi_data(t, k):
    """phi_k(z) = 1 - (1 - e^{-k z})^{b}, threshold t_k = t + k^{-1/2}, b = ceil(e^{k t_k}).

    Returns (coefficients, frequencies) with phi_k(z) = sum_j a_j e^{-lam_j z}."""
    tk = t + k ** -0.5
    b = math.ceil(math.exp(k * tk))
    coeffs = [math.comb(b, j) * (-1) ** (j + 1) for j in range(1, b + 1)]
    freqs = [j * k for j in range(1, b + 1)]
    return coeffs, freqs, b


def check_royen_exp():
    print("== 5. Royen exponential-sum route on slab boxes ==")
    n = 2
    P1 = rng.normal(size=(2, n))
    P2 = rng.normal(size=(1, n))
    t = np.array([0.6, 0.4, 0.5])
    k = 2
    data = [royen_phi_data(ti, k) for ti in t]
    print("b per coordinate:", [d[2] for d in data])

    def C(s):
        return np.block([[P1 @ P1.T, s * P1 @ P2.T], [s * P2 @ P1.T, P2 @ P2.T]])

    def F(s):
        tot = 0.0
        for idx in itertools.product(*[range(len(d[0])) for d in data]):
            c = np.prod([data[i][0][j] for i, j in enumerate(idx)])
            lam = np.array([data[i][1][j] for i, j in enumerate(idx)], dtype=float)
            tot += c * np.linalg.det(np.eye(3) + np.diag(lam) @ C(s)) ** -0.5
        return tot

    def phi(z, i):
        tk = t[i] + k ** -0.5
        b = math.ceil(math.exp(k * tk))
        return 1 - (1 - np.exp(-k * z)) ** b

    for s in [0.0, 0.3, 0.6, 0.9, 1.0]:
        N = 1_000_000
        G1 = rng.normal(size=(N, n))
        G2 = rng.normal(size=(N, n))
        Y = s * G1 + math.sqrt(max(1 - s * s, 0)) * G2
        V = np.concatenate([G1 @ P1.T, Y @ P2.T], axis=1)
        Zs = V**2 / 2
        mc = np.prod([phi(Zs[:, i], i) for i in range(3)], axis=0).mean()
        print(f"s={s:.1f}  F(s) explicit = {F(s):.6f}   MC = {mc:.6f}")
    ss = np.linspace(0, 1, 41)
    vals = [F(s) for s in ss]
    print("F nondecreasing on grid:", all(np.diff(vals) >= -1e-12), " min diff", np.diff(vals).min())


if __name__ == "__main__":
    check_target()
    check_conditional()
    check_special_i()
    check_special_ii()
    check_royen_exp()
