"""AUDIT-B: Monte Carlo test of conditional positivity E[q_AB | q_A, q_B] >= 0.

If this held, E_gamma[q_AB phi(q_A) psi(q_B)] >= 0 for all nonnegative phi, psi,
which would make the GCI input of (GR1) elementary.  We look for negative bins.
"""
import numpy as np
rng = np.random.default_rng(7)

def rpsd(n, r):
    X = rng.standard_normal((n, r)) * rng.exponential(1, r)
    return X @ X.T

worst = 0.0
for trial in range(60):
    n = int(rng.integers(2, 6))
    A, B = rpsd(n, int(rng.integers(1, n + 1))), rpsd(n, int(rng.integers(1, n + 1)))
    M = 2_000_000
    x = rng.standard_normal((M, n))
    Ax, Bx = x @ A, x @ B
    qa, qb = (x * Ax).sum(1), (x * Bx).sum(1)
    qab = (Ax * Bx).sum(1)
    nb = 12
    ea = np.quantile(qa, np.linspace(0, 1, nb + 1)); eb = np.quantile(qb, np.linspace(0, 1, nb + 1))
    ia = np.clip(np.searchsorted(ea, qa) - 1, 0, nb - 1); ib = np.clip(np.searchsorted(eb, qb) - 1, 0, nb - 1)
    S = np.zeros((nb, nb)); S2 = np.zeros((nb, nb)); C = np.zeros((nb, nb))
    np.add.at(S, (ia, ib), qab); np.add.at(S2, (ia, ib), qab ** 2); np.add.at(C, (ia, ib), 1)
    with np.errstate(invalid="ignore", divide="ignore"):
        mean = S / C
        se = np.sqrt(np.maximum(S2 / C - mean ** 2, 0) / C)
        z = mean / se
    ok = C > 2000
    zmin = np.nanmin(np.where(ok, z, np.inf))
    if zmin < worst:
        worst = zmin
        print(f"trial {trial} n={n}: most negative bin z-score {zmin:.2f}, "
              f"mean {np.nanmin(np.where(ok, mean, np.inf)):.3e}")
print("most negative z-score over all trials:", worst)
