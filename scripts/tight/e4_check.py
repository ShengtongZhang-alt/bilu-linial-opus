"""Numerical sanity checks for the Lean files BiluLinial/Tight/Compare/*.lean (Part D, (E1), (E4)).

Checks:
  1. c_j from the recursion sum_{i<=k} c_i/(2(k-i))! = 1/(2^k k!) equals the Taylor coefficients of
     e^{t^2/2}/cosh t; c_0..c_3 = 1, 0, 1/12, -1/45; |c_j| <= 1 (and the decay rate 4/pi^2).
  2. One-dimensional comparison (gauss_rad_compare): for f(x) = cos(w x),
     |G f - sum_{j<=n} c_j R f^{(2j)}| <= 2 sup|f^{(2n+2)}| = 2 w^{2n+2}.
  3. Endpoint identity (endpoint_identity): exact on degree <= 4 polynomials; constant 13/60 on
     f(x) = cos(w x + phi).
  4. Multi-coordinate comparison (gauss_rad_expansion) in two and three coordinates for
     f(x) = cos(a . x): |G f - sum_{|j|_g<=k} c_j R d^{2j} f| <= 2 sum_{|j|_g=k+1} prod a_i^{2 j_i}.
Run with /tmp/tight-venv/bin/python scripts/tight/e4_check.py
"""
import itertools
import math
from fractions import Fraction

import sympy as sp


def ecoef(N):
    c = [Fraction(1)]
    for k in range(1, N + 1):
        s = sum(c[i] / math.factorial(2 * (k - i)) for i in range(k))
        c.append(Fraction(1, 2**k * math.factorial(k)) - s)
    return c


def check_coefficients(N=40):
    c = ecoef(N)
    t = sp.symbols("t")
    ser = sp.series(sp.exp(t**2 / 2) / sp.cosh(t), t, 0, 2 * 12 + 2).removeO()
    for j in range(12):
        assert sp.Rational(c[j].numerator, c[j].denominator) == ser.coeff(t, 2 * j), j
    assert c[:4] == [1, 0, Fraction(1, 12), Fraction(-1, 45)]
    assert all(abs(x) <= 1 for x in c)
    assert all(abs(x) <= Fraction(1, 12) for x in c[2:])
    ratio = float(abs(c[N] / c[N - 1]))
    print(f"c_0..c_5 = {[str(x) for x in c[:6]]}; max_j>=2 |c_j| = {float(max(abs(x) for x in c[2:])):.4g};"
          f" |c_{N}/c_{N-1}| = {ratio:.5f} (4/pi^2 = {4 / math.pi**2:.5f})")
    return [float(x) for x in c]


def check_one_dim(c):
    worst = 0.0
    for n in range(0, 8):
        for w in [0.1 * i for i in range(1, 60)]:
            G = math.exp(-w * w / 2)
            R = sum(c[j] * (-1) ** j * w ** (2 * j) * math.cos(w) for j in range(n + 1))
            bound = 2 * w ** (2 * n + 2)
            worst = max(worst, abs(G - R) / bound)
            assert abs(G - R) <= bound + 1e-12, (n, w)
    print(f"1-D comparison: max |G f - sum c_j R f^(2j)| / (2 M) = {worst:.4f} (<= 1)")


def check_endpoint():
    x = sp.symbols("x")
    for coeffs in itertools.product(range(-2, 3), repeat=5):
        f = sum(a * x**m for m, a in enumerate(coeffs))
        lhs = (f.subs(x, 1) - f.subs(x, -1)) / 2
        d1, d3 = sp.diff(f, x), sp.diff(f, x, 3)
        rhs = (d1.subs(x, 1) + d1.subs(x, -1)) / 2 - (d3.subs(x, 1) + d3.subs(x, -1)) / 6
        assert sp.simplify(lhs - rhs) == 0
    worst = 0.0
    for w in [0.05 * i for i in range(1, 80)]:
        for phi in [0.0, 0.3, 0.7, 1.1, 1.5707963]:
            f = lambda s, k=0: w**k * math.cos(w * s + phi + k * math.pi / 2)
            lhs = (f(1) - f(-1)) / 2
            rhs = (f(1, 1) + f(-1, 1)) / 2 - (f(1, 3) + f(-1, 3)) / 6
            M = w**5
            worst = max(worst, abs(lhs - rhs) / (13 / 60 * M))
            assert abs(lhs - rhs) <= 13 / 60 * M + 1e-12
    print(f"endpoint identity: exact on degree <= 4; max ratio to (13/60) sup|f^(5)| = {worst:.4f}")


def grade(j):
    return sum(max(x - 1, 0) for x in j)


def admissible(n, kmax):
    for j in itertools.product(range(kmax + 3), repeat=n):
        if all(x != 1 for x in j):
            yield j


def check_multi(c):
    worst = 0.0
    for n in (2, 3):
        for k in range(0, 4):
            for a in itertools.product([0.3, 0.8, 1.3], repeat=n):
                G = math.exp(-sum(t * t for t in a) / 2)
                Rcos = math.prod(math.cos(t) for t in a)
                ret = 0.0
                rem = 0.0
                for j in admissible(n, k):
                    g = grade(j)
                    mono = math.prod(t ** (2 * x) for t, x in zip(a, j))
                    if g <= k:
                        cj = math.prod(c[x] for x in j)
                        ret += cj * (-1) ** sum(j) * mono * Rcos
                    elif g == k + 1:
                        rem += mono
                err = abs(G - ret)
                worst = max(worst, err / (2 * rem))
                assert err <= 2 * rem + 1e-12, (n, k, a, err, rem)
    print(f"multi-coordinate comparison: max |E_k| / (2 sum M_j) = {worst:.4f} (<= 1)")


if __name__ == "__main__":
    c = check_coefficients()
    check_one_dim(c)
    check_endpoint()
    check_multi(c)
    print("all checks passed")
