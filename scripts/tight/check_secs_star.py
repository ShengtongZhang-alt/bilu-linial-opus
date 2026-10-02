#!/usr/bin/env python3
"""Star-level (Gaussian) checks for CHECK_SECS.md, by quadrature in dimensions 1 and 2.

alpha = (1 - x^T A x)_+, beta = (1 - x^T B x)_+, Phi = alpha^p beta^p, G = standard Gaussian.
  (a) A-C1b gaussE_f1Obs_ge:  G[Phi] * w(A) <= G[(trA - q_A) alpha^(p-1) beta^p],  w = trA^2/(1+trA)
  (b) A-CR  gaussE_C4:  G[(trM - q_M) Phi] <= 2p G[trMA a^(p-1)b^p + trMB a^p b^(p-1)]
                                           + 4p G[q_AMA a^(p-2) b^p + q_BMB a^p b^(p-2)],  M >= 0 arbitrary
  (c) T.GIBP2:  2 G[F] = G[(trA - q_A) a^(p-1) b^p],  F = (p-1) q_{A^2} a^(p-2) b^p + p q_{AB} a^(p-1) b^(p-1)
  (d) B25 gauss_rowNum_ge:  (p-1) trM^2 G[a^(p-2)b^p] + p tr(MN) G[a^(p-1)b^(p-1)]
          - 4p^2 m0 (trM^2 G[a^(p-3)b^p] + tr(MN) G[a^(p-1)b^(p-2)]) <= G[F]
       for 0 <= M <= A, 0 <= N <= B, M, N <= m0 I, p >= 4
  (e) A-PDOM pdom (matrix inequalities, random)
Run: /tmp/tight-venv/bin/python scripts/tight/check_secs_star.py
"""
import numpy as np

rng = np.random.default_rng(7)


def grid(dim, L=7.0, n1=4001, n2=1201):
    if dim == 1:
        x = np.linspace(-L, L, n1)
        w = np.full(n1, x[1] - x[0])
        w[0] = w[-1] = w[0] / 2
        pts = x[:, None]
        gw = w * np.exp(-x ** 2 / 2) / np.sqrt(2 * np.pi)
        return pts, gw
    x = np.linspace(-L, L, n2)
    h = x[1] - x[0]
    w1 = np.full(n2, h)
    w1[0] = w1[-1] = h / 2
    X, Y = np.meshgrid(x, x, indexing="ij")
    pts = np.stack([X.ravel(), Y.ravel()], axis=1)
    gw = (np.outer(w1, w1).ravel()) * np.exp(-(pts ** 2).sum(1) / 2) / (2 * np.pi)
    return pts, gw


GRID = {1: grid(1), 2: grid(2)}


def qv(M, pts):
    return np.einsum("ni,ij,nj->n", pts, M, pts)


def rand_psd(dim, scale):
    Q = np.linalg.qr(rng.normal(size=(dim, dim)))[0]
    ev = rng.uniform(0, scale, dim)
    if rng.random() < 0.3:
        ev[0] = 0.0
    return Q @ np.diag(ev) @ Q.T


def sqrtm_psd(A):
    w, U = np.linalg.eigh(A)
    return U @ np.diag(np.sqrt(np.clip(w, 0, None))) @ U.T


def below(A):
    """random 0 <= M <= A."""
    dim = A.shape[0]
    Q = np.linalg.qr(rng.normal(size=(dim, dim)))[0]
    R = Q @ np.diag(rng.uniform(0, 1, dim)) @ Q.T
    S = sqrtm_psd(A)
    return S @ R @ S


def main():
    worst = {k: -np.inf for k in "abcde"}
    where = {}
    for trial in range(240):
        dim = 1 if trial % 3 == 0 else 2
        pts, gw = GRID[dim]
        G = lambda f: float(np.dot(gw, f))
        scale = [0.05, 0.3, 1.0, 3.0][trial % 4]
        A, B = rand_psd(dim, scale), rand_psd(dim, scale * rng.uniform(0.2, 2))
        qa, qb = qv(A, pts), qv(B, pts)
        al, be = np.clip(1 - qa, 0, None), np.clip(1 - qb, 0, None)
        for p in (2, 3, 4, 5, 8, 20):
            trA = np.trace(A)
            wA = np.trace(A @ A) / (1 + trA)
            f1 = (trA - qa) * al ** (p - 1) * be ** p
            Phi = al ** p * be ** p
            # (a)
            gap = G(Phi) * wA - G(f1)
            if gap / (abs(G(f1)) + 1e-12) > worst["a"]:
                worst["a"], where["a"] = gap / (abs(G(f1)) + 1e-12), (dim, scale, p)
            if p >= 3:
                M = rand_psd(dim, scale * rng.uniform(0.1, 3))
                lhs = G((np.trace(M) - qv(M, pts)) * Phi)
                rhs = 2 * p * G(np.trace(M @ A) * al ** (p - 1) * be ** p + np.trace(M @ B) * al ** p * be ** (p - 1)) \
                    + 4 * p * G(qv(A @ M @ A, pts) * al ** (p - 2) * be ** p + qv(B @ M @ B, pts) * al ** p * be ** (p - 2))
                # absolute floor 1e-6: for A = B = 0 both sides vanish exactly and the grid
                # truncation |x| <= 7 leaves ~1e-9 on the left
                r = (lhs - rhs) / (abs(rhs) + 1e-6)
                if r > worst["b"]:
                    worst["b"], where["b"] = r, (dim, scale, p)
                F = (p - 1) * qv(A @ A, pts) * al ** (p - 2) * be ** p + p * qv(A @ B, pts) * al ** (p - 1) * be ** (p - 1)
                r = abs(2 * G(F) - G(f1)) / (abs(G(f1)) + 1e-9)
                if r > worst["c"]:
                    worst["c"], where["c"] = r, (dim, scale, p)
            if p >= 4:
                M, Nn = below(A), below(B)
                m0 = max(np.linalg.eigvalsh(M)[-1], np.linalg.eigvalsh(Nn)[-1]) * rng.uniform(1, 2)
                F = (p - 1) * qv(A @ A, pts) * al ** (p - 2) * be ** p + p * qv(A @ B, pts) * al ** (p - 1) * be ** (p - 1)
                trM2, trMN = np.trace(M @ M), np.trace(M @ Nn)
                lhs = (p - 1) * trM2 * G(al ** (p - 2) * be ** p) + p * trMN * G(al ** (p - 1) * be ** (p - 1)) \
                    - 4 * p ** 2 * m0 * (trM2 * G(al ** (p - 3) * be ** p) + trMN * G(al ** (p - 1) * be ** (p - 2)))
                r = (lhs - G(F)) / (abs(G(F)) + 1e-12)
                if r > worst["d"]:
                    worst["d"], where["d"] = r, (dim, scale, p, lhs, G(F))
        # (e) pdom
        M = below(A)
        Th = np.trace(A @ A + B @ B)
        e1 = np.trace(M @ A) - Th
        e2 = np.trace(M @ B) - Th
        e3 = -np.linalg.eigvalsh(Th * A - A @ M @ A)[0]
        e4 = -np.linalg.eigvalsh(Th * B - B @ M @ B)[0]
        worst["e"] = max(worst["e"], e1, e2, e3, e4)
    print("(a) A-C1b  max (G[Phi] w - G[f1]) / |G[f1]|     (want <= 0):", f"{worst['a']:.3e}", where.get("a"))
    print("(b) A-CR   max (lhs - rhs) / |rhs|               (want <= 0):", f"{worst['b']:.3e}", where.get("b"))
    print("(c) GIBP2  max |2G[F] - G[f1]| / |G[f1]|         (want ~ 0):", f"{worst['c']:.3e}", where.get("c"))
    print("(d) B25    max (lhs - G[F]) / |G[F]|             (want <= 0):", f"{worst['d']:.3e}", where.get("d"))
    print("(e) PDOM   max violation                         (want <= 0):", f"{worst['e']:.3e}")


if __name__ == "__main__":
    main()
