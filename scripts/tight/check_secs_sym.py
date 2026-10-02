#!/usr/bin/env python3
"""Symbolic checks for CHECK_SECS.md (statement checker of Sections A-C).

1. in_E1 interface: the fibre polynomial of SecA/Endpoint.lean,
   Pi(t) = d+(t)^(p-1) d-(t)^p (x - t a (P - x^2)),
   d+(t) = 1 + 2 t a x - t^2 a^2 (P - x^2),  d-(t) = 1 - 2 t a z - t^2 a^2 (Q - z^2),
   has 1! [t^1] Pi = a(-P + (2p-1) x^2 - 2p x z)  (the D1 of in_E1 / RouteDR1.d1x) and
   3! [t^3] Pi = a^3 Kpoly(p, x, z, P, Q)  (Contact/Defs.lean Kpoly), for symbolic p.
   Also checks the minus-branch D1 z of RouteDR1.d1z against the minus fibre.
2. Gaussian IBP 2 G[F] = G[(tr A - q_A) a^(p-1) b^p] (T.GIBP2, used for in_C1): symbolic in
   one dimension is done numerically in check_secs_star.py.

Run: /tmp/tight-venv/bin/python scripts/tight/check_secs_sym.py
"""
import sympy as sp

t, a, x, z, P, Q, p = sp.symbols("t a x z P Q p")


def series_pow(base, expo, order):
    """(base)^expo as a polynomial in t up to t^order, base = 1 + O(t), expo symbolic."""
    u = sp.expand(base - 1)
    s = 0
    for k in range(order + 1):
        s += sp.binomial(expo, k) * u ** k
    return sp.expand(sp.series(s, t, 0, order + 1).removeO())


def coeffs(expr, order):
    e = sp.expand(expr)
    return [sp.simplify(e.coeff(t, k)) for k in range(order + 1)]


def main():
    order = 3
    dp = 1 + 2 * t * a * x - t ** 2 * a ** 2 * (P - x ** 2)
    dm = 1 - 2 * t * a * z - t ** 2 * a ** 2 * (Q - z ** 2)
    Pi = series_pow(dp, p - 1, order) * series_pow(dm, p, order) * (x - t * a * (P - x ** 2))
    c = coeffs(sp.expand(sp.series(sp.expand(Pi), t, 0, order + 1).removeO()), order)
    D1 = sp.factorial(1) * c[1]
    D3 = sp.factorial(3) * c[3]
    D1_target = a * (-P + (2 * p - 1) * x ** 2 - 2 * p * x * z)
    U = (p - 1) * x - p * z
    V = (p - 1) * (P + x ** 2) + p * (Q + z ** 2)
    W = (p - 1) * (3 * P * x + x ** 3) - p * (3 * Q * z + z ** 3)
    K = x * (8 * U ** 3 - 12 * U * V + 4 * W) - 3 * (P - x ** 2) * (4 * U ** 2 - 2 * V)
    print("[t^0] Pi - x                 :", sp.simplify(c[0] - x))
    print("1![t^1] Pi - D1x (in_E1)     :", sp.simplify(sp.expand(D1 - D1_target)))
    print("3![t^3] Pi - a^3 Kpoly       :", sp.simplify(sp.expand(D3 - a ** 3 * K)))
    # minus branch: psi = z = G-_vi; P- = Z - a A, so the fibre of z has d-(t)^(p-1) d+(t)^p and
    # the entry (P- + t(-a)E)^{-1}_vi = (z + t a (Q - z^2))/d-(t)
    Pim = series_pow(dm, p - 1, 1) * series_pow(dp, p, 1) * (z + t * a * (Q - z ** 2))
    cm = coeffs(sp.expand(sp.series(sp.expand(Pim), t, 0, 2).removeO()), 1)
    D1z_target = a * Q - (2 * p - 1) * a * z ** 2 + 2 * p * a * x * z
    print("1![t^1] Pi_minus - D1z       :", sp.simplify(sp.expand(cm[1] - D1z_target)))
    # rank-two inverse entry used by the fibre: (P + tE)^{-1}_vi = (G_vi - t(G_vv G_ii - G_vi^2))/delta
    gvv, gii, gvi, tt = sp.symbols("gvv gii gvi tt")
    Gm = sp.Matrix([[gvv, gvi], [gvi, gii]])
    Pm = Gm.inv()
    E = sp.Matrix([[0, 1], [1, 0]])
    inv_t = (Pm + tt * E).inv()
    delta = 1 + 2 * tt * gvi - tt ** 2 * (gvv * gii - gvi ** 2)
    print("rank-2 entry identity        :",
          sp.simplify(inv_t[0, 1] - (gvi - tt * (gvv * gii - gvi ** 2)) / delta))
    print("rank-2 det identity          :",
          sp.simplify((Pm + tt * E).det() - Pm.det() * delta))


if __name__ == "__main__":
    main()
