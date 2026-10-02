"""T.GIBP2 (two_mul_gaussE_starF) in one dimension with adaptive quadrature split at the support
boundaries |x| = 1/sqrt(a), 1/sqrt(b); 2 G[F] must equal G[(a - a x^2) g] to quadrature accuracy.
Also n = 2 with polar quadrature for diagonal A, B (exact boundary handling in r).
Run: /tmp/tight-venv/bin/python scripts/tight/check_tools_gibp2_1d.py
"""
import numpy as np
from scipy import integrate

rng = np.random.default_rng(3)
phi = lambda x: np.exp(-x * x / 2) / np.sqrt(2 * np.pi)


def one(a, b, p):
    def al(x):
        return max(1 - a * x * x, 0.0)

    def be(x):
        return max(1 - b * x * x, 0.0)

    F = lambda x: ((p - 1) * a * a * x * x * al(x) ** (p - 2) * be(x) ** p
                   + p * a * b * x * x * al(x) ** (p - 1) * be(x) ** (p - 1)) * phi(x)
    NG = lambda x: (a - a * x * x) * al(x) ** (p - 1) * be(x) ** p * phi(x)
    pts = sorted({1 / np.sqrt(c) for c in (a, b) if c > 0} | {12.0})
    lo = 0.0
    sF = sN = 0.0
    for hi in pts:
        sF += integrate.quad(F, lo, hi, epsabs=1e-14, epsrel=1e-13, limit=200)[0]
        sN += integrate.quad(NG, lo, hi, epsabs=1e-14, epsrel=1e-13, limit=200)[0]
        lo = hi
        if hi == 12.0:
            break
    return 2 * (2 * sF), 2 * sN  # even integrands: double the half-line


worst = 0.0
for t in range(400):
    a = float(rng.choice([0.0, 10 ** rng.uniform(-2, 2)]))
    b = float(rng.choice([0.0, 10 ** rng.uniform(-2, 2)]))
    p = int(rng.choice([3, 4, 5, 8, 20]))
    lhs, rhs = one(a, b, p)
    worst = max(worst, abs(lhs - rhs) / (1e-14 + abs(lhs) + abs(rhs)))
print(f"[GIBP2 n=1 adaptive] 400 cases (a,b in {{0}} U [1e-2,1e2], p in 3..20): worst rel. residual {worst:.1e}")

# the doc check: p = 3, B = 0, A = a: G[4a^2x^2(1-ax^2)_+] = G[(a - ax^2)(1-ax^2)_+^2]
for a in (0.3, 1.0, 5.0):
    lhs, rhs = one(a, 0.0, 3)
    print(f"[doc] p=3 B=0 a={a}: 2G[F]={lhs:.12f}  G[(trA-qA)g]={rhs:.12f}")

# p = 2 (excluded by the hypothesis 3 <= p): identity still holds in 1-D (g Lipschitz)
lhs, rhs = one(1.0, 0.5, 2)
print(f"[info] p=2: 2G[F]={lhs:.10f} vs {rhs:.10f} (hypothesis p >= 3 is for the C^1 Stein route)")


# n = 2, diagonal A, B: polar coordinates, radial integral split at the boundary radius per angle
def two_d(A, B, p, nth=2000):
    ths = (np.arange(nth) + 0.5) * 2 * np.pi / nth
    sF = sN = 0.0
    trA = A[0] + A[1]
    for th in ths:
        u = np.array([np.cos(th), np.sin(th)])
        qa, qb = A @ (u * u), B @ (u * u)
        qa2, qab = (A * A) @ (u * u), (A * B) @ (u * u)
        rr = [1 / np.sqrt(c) for c in (qa, qb) if c > 0]
        R = min(rr + [12.0])

        def F(r):
            al, be = max(1 - qa * r * r, 0), max(1 - qb * r * r, 0)
            return ((p - 1) * qa2 * r * r * al ** (p - 2) * be ** p + p * qab * r * r * al ** (p - 1) * be ** (p - 1)) \
                * np.exp(-r * r / 2) / (2 * np.pi) * r

        def N(r):
            al, be = max(1 - qa * r * r, 0), max(1 - qb * r * r, 0)
            return (trA - qa * r * r) * al ** (p - 1) * be ** p * np.exp(-r * r / 2) / (2 * np.pi) * r

        sF += integrate.quad(F, 0, R, epsabs=1e-15, epsrel=1e-13)[0]
        sN += integrate.quad(N, 0, R, epsabs=1e-15, epsrel=1e-13)[0]
    dth = 2 * np.pi / nth
    return 2 * sF * dth, sN * dth


worst2 = 0.0
for t in range(12):
    A = np.array([10 ** rng.uniform(-1, 1), float(rng.choice([0.0, 10 ** rng.uniform(-1, 1)]))])
    B = np.array([float(rng.choice([0.0, 10 ** rng.uniform(-1, 1)])), 10 ** rng.uniform(-1, 1)])
    p = int(rng.choice([3, 4, 7]))
    lhs, rhs = two_d(A, B, p)
    worst2 = max(worst2, abs(lhs - rhs) / (abs(lhs) + abs(rhs)))
print(f"[GIBP2 n=2 polar, diagonal A,B] 12 cases: worst rel. residual {worst2:.1e}")


# n = 2, general symmetric PSD A, B (non-commuting, rank one, large eigenvalues)
def two_d_general(A, B, p, nth=1500):
    ths = (np.arange(nth) + 0.5) * 2 * np.pi / nth
    A2, AB = A @ A, A @ B
    trA = np.trace(A)
    sF = sN = 0.0
    for th in ths:
        u = np.array([np.cos(th), np.sin(th)])
        qa, qb, qa2, qab = u @ A @ u, u @ B @ u, u @ A2 @ u, u @ AB @ u
        R = min([1 / np.sqrt(c) for c in (qa, qb) if c > 1e-300] + [12.0])

        def F(r):
            al, be = max(1 - qa * r * r, 0), max(1 - qb * r * r, 0)
            return ((p - 1) * qa2 * al ** (p - 2) * be ** p + p * qab * al ** (p - 1) * be ** (p - 1)) \
                * r ** 3 * np.exp(-r * r / 2) / (2 * np.pi)

        def N(r):
            al, be = max(1 - qa * r * r, 0), max(1 - qb * r * r, 0)
            return (trA - qa * r * r) * al ** (p - 1) * be ** p * r * np.exp(-r * r / 2) / (2 * np.pi)

        sF += integrate.quad(F, 0, R, epsabs=1e-15, epsrel=1e-13)[0]
        sN += integrate.quad(N, 0, R, epsabs=1e-15, epsrel=1e-13)[0]
    dth = 2 * np.pi / nth
    return 2 * sF * dth, sN * dth


def rpsd(kind):
    X = rng.normal(size=(2, 2))
    if kind == "rank1":
        v = rng.normal(size=2)
        return np.outer(v, v) * 10 ** rng.uniform(-1, 1.3)
    if kind == "zero":
        return np.zeros((2, 2))
    return X @ X.T * 10 ** rng.uniform(-1, 1.3) / 2


worst3 = 0.0
for t in range(20):
    A, B = rpsd(rng.choice(["gen", "gen", "rank1"])), rpsd(rng.choice(["gen", "rank1", "zero"]))
    p = int(rng.choice([3, 3, 4, 7]))
    lhs, rhs = two_d_general(A, B, p)
    worst3 = max(worst3, abs(lhs - rhs) / (abs(lhs) + abs(rhs) + 1e-300))
print(f"[GIBP2 n=2 polar, general symmetric PSD A,B] 20 cases: worst rel. residual {worst3:.1e}")
