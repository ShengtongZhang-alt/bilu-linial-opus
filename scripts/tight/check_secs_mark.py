#!/usr/bin/env python3
"""T.MARK checks (SecC/Mark.lean): rowNum_line (exact), mark_grade_one, mark_grade_two_diag,
mark_grade_two_mixed (explicit constants 1000 and 10^6), by exact polynomial arithmetic along
lines/planes x + t e_i (+ s e_k) inside {alpha, beta > 0}.

F(x) = (p-1) q_{A^2}(x) alpha^{p-2} beta^p + p q_{AB}(x) alpha^{p-1} beta^{p-1}  (Contact/Defs rowNum)
starRow a A x j = -(Ax)_j/(a alpha),  starCore a A x k j = A_kj/(a^2 alpha),
starScale = |x_i| + sqrt(e_ii) + |z_i| + sqrt(f_ii),  z = starRow(-a, B), f = starCore(a, B).
Run: /tmp/tight-venv/bin/python scripts/tight/check_secs_mark.py
"""
from math import factorial, sqrt
import numpy as np
from scipy.signal import convolve2d

rng = np.random.default_rng(11)


def pmul(P, Q):
    return convolve2d(P, Q)


def ppow(P, n):
    R = np.array([[1.0]])
    for _ in range(n):
        R = pmul(R, P)
    return R


def padd(P, Q):
    n = max(P.shape[0], Q.shape[0])
    m = max(P.shape[1], Q.shape[1])
    R = np.zeros((n, m))
    R[:P.shape[0], :P.shape[1]] += P
    R[:Q.shape[0], :Q.shape[1]] += Q
    return R


def lin_vec(M, x, i, k):
    """components of M(x + t e_i + s e_k) as 2D polys in (t, s)."""
    out = []
    for j in range(len(x)):
        P = np.zeros((2, 2))
        P[0, 0] = (M @ x)[j]
        P[1, 0] = M[j, i]
        if k is not None:
            P[0, 1] = M[j, k]
        out.append(P)
    return out


def rownum_poly(p, A, B, x, i, k):
    Ax, Bx = lin_vec(A, x, i, k), lin_vec(B, x, i, k)
    one = np.array([[1.0]])
    al = padd(one, -1 * sum_dot(lin_vec(np.eye(len(x)), x, i, k), Ax))
    be = padd(one, -1 * sum_dot(lin_vec(np.eye(len(x)), x, i, k), Bx))
    qAA = sum_dot(Ax, Ax)
    qAB = sum_dot(Ax, Bx)
    F = padd((p - 1) * pmul(pmul(qAA, ppow(al, p - 2)), ppow(be, p)),
             p * pmul(pmul(qAB, ppow(al, p - 1)), ppow(be, p - 1)))
    return F


def sum_dot(U, V):
    R = np.zeros((1, 1))
    for u, v in zip(U, V):
        R = padd(R, pmul(u, v))
    return R


def rand_psd(n, scale):
    Q = np.linalg.qr(rng.normal(size=(n, n)))[0]
    return Q @ np.diag(rng.uniform(0, scale, n)) @ Q.T


def main():
    worst = {"line": 0.0, "g1": 0.0, "g2d": 0.0, "g2m": 0.0}
    for trial in range(400):
        n = [1, 2, 3][trial % 3]
        p = [8, 9, 12, 20][trial % 4]
        a = [0.02, 0.1, 0.5, 1.0][(trial // 4) % 4]
        sc = [0.05, 0.4, 2.0][(trial // 16) % 3]
        A, B = rand_psd(n, sc), rand_psd(n, sc * rng.uniform(0.1, 2))
        x = rng.normal(size=n) * rng.uniform(0.05, 1.5)
        al, be = 1 - x @ A @ x, 1 - x @ B @ x
        if al <= 0.02 or be <= 0.02:
            continue
        xr = -(A @ x) / (a * al)
        zr = -(B @ x) / (-a * be)
        e = A / (a * a * al)
        f = B / (a * a * be)
        r = np.abs(xr) + np.sqrt(np.clip(np.diag(e), 0, None)) + np.abs(zr) + np.sqrt(np.clip(np.diag(f), 0, None))
        Phi = al ** p * be ** p
        i = rng.integers(n)
        P1 = rownum_poly(p, A, B, x, i, None)[:, 0]
        # rowNum_line at a small t
        t = rng.uniform(-0.3, 0.3) * min(1.0, 1 / (a * (1 + r[i])))
        rp = 1 + 2 * a * xr[i] * t - a * a * e[i, i] * t * t
        rm = 1 - 2 * a * zr[i] * t - a * a * f[i, i] * t * t
        if rp >= 0 and rm >= 0:
            lhs = np.polyval(P1[::-1], t)
            rhs = a * a * al ** p * be ** p * sum(
                (p - 1) * (xr[j] - a * e[i, j] * t) ** 2 * rp ** (p - 2) * rm ** p
                - p * (xr[j] - a * e[i, j] * t) * (zr[j] + a * f[i, j] * t) * rp ** (p - 1) * rm ** (p - 1)
                for j in range(n))
            worst["line"] = max(worst["line"], abs(lhs - rhs) / (abs(lhs) + 1e-300 + abs(rhs)))
        d4 = 24 * P1[4]
        bnd1 = a ** 2 * Phi * a ** 4 * (1 + r[i]) ** 4 * 1000 * (
            p ** 5 * abs(sum(xr[j] * (xr[j] - zr[j]) for j in range(n)))
            + p ** 4 * sum(xr[j] ** 2 + abs(xr[j] * e[i, j]) + abs(xr[j] * f[i, j]) + abs(e[i, j] * zr[j])
                           + e[i, j] ** 2 + abs(e[i, j] * f[i, j]) for j in range(n)))
        worst["g1"] = max(worst["g1"], abs(d4) / bnd1)
        d6 = 720 * P1[6]
        bnd2 = a ** 2 * Phi * a ** 6 * (1 + r[i]) ** 6 * 1e6 * p ** 9 * sum(
            xr[j] ** 2 + abs(xr[j] * zr[j]) + abs(xr[j] * e[i, j]) + abs(xr[j] * f[i, j])
            + abs(e[i, j] * zr[j]) + e[i, j] ** 2 + abs(e[i, j] * f[i, j]) for j in range(n))
        worst["g2d"] = max(worst["g2d"], abs(d6) / bnd2)
        if n >= 2:
            k = (i + 1) % n
            P2 = rownum_poly(p, A, B, x, i, k)
            d44 = 576 * P2[4, 4]
            eb = [abs(e[i, j]) + abs(e[k, j]) for j in range(n)]
            fb = [abs(f[i, j]) + abs(f[k, j]) for j in range(n)]
            bnd3 = a ** 2 * Phi * a ** 8 * (1 + r[i]) ** 4 * (1 + r[k]) ** 4 * 1e6 * p ** 9 * sum(
                xr[j] ** 2 + abs(xr[j] * zr[j]) + abs(xr[j]) * eb[j] + abs(xr[j]) * fb[j]
                + eb[j] * abs(zr[j]) + eb[j] ** 2 + eb[j] * fb[j] for j in range(n))
            worst["g2m"] = max(worst["g2m"], abs(d44) / bnd3)
    print("rowNum_line           max rel residual  (want 0):", f"{worst['line']:.2e}")
    print("mark_grade_one        max |d^4F|/bound  (want <= 1):", f"{worst['g1']:.3e}")
    print("mark_grade_two_diag   max |d^6F|/bound  (want <= 1):", f"{worst['g2d']:.3e}")
    print("mark_grade_two_mixed  max |d44F|/bound  (want <= 1):", f"{worst['g2m']:.3e}")


if __name__ == "__main__":
    main()
