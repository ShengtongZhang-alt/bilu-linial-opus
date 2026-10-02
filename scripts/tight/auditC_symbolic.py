"""AUDIT-C symbolic checks (lines 1077-1560 of second_order_bilu_linial_tight.tex).

1. Phi^{-1} D_i^3 (Phi x_i) = K_i  (D = a^{-1} d/dxi_i), with the CR2 rules.
2. The exact scalar inequality (D3) from the corrected loop and (F3).
3. Row-free part of K_i and the 'at least two row factors' claim.
"""
import sympy as sp

p, x, z, P, Q = sp.symbols('p x z P Q')

# derivation rules for D_i acting on the single-index quantities at k=j=i (CR2)
#   D x_i = -x_i^2 - c_ii,  c_ii = P ; D c_ii = -4 x_i P
#   D z_i =  z_i^2 + d_ii,  d_ii = Q ; D d_ii =  4 z_i Q
rules = {x: -x**2 - P, z: z**2 + Q, P: -4 * x * P, Q: 4 * z * Q}


def D(expr):
    return sp.expand(sum(sp.diff(expr, v) * dv for v, dv in rules.items()))


score = 2 * p * (x - z)  # D log Phi


def Dphi(f):
    """Phi^{-1} D (Phi f)."""
    return sp.expand(D(f) + score * f)


lhs = Dphi(Dphi(Dphi(x)))
U = (p - 1) * x - p * z
V = (p - 1) * (P + x**2) + p * (Q + z**2)
W = (p - 1) * (3 * P * x + x**3) - p * (3 * Q * z + z**3)
K = sp.expand(x * (8 * U**3 - 12 * U * V + 4 * W) - 3 * (P - x**2) * (4 * U**2 - 2 * V))
print("K_i identity  Phi^-1 D^3(Phi x) - K =", sp.simplify(lhs - K))

# first-order: Phi^{-1} D (Phi x) = (2p-1) x^2 - 2p x z - P
print("first order:", sp.simplify(Dphi(x) - ((2 * p - 1) * x**2 - 2 * p * x * z - P)))

# row-free part and monomial structure
rowfree = K.subs({x: 0, z: 0})
print("row-free part of K:", sp.factor(rowfree), " expected 6[(p-1)P^2+pPQ]:",
      sp.simplify(rowfree - 6 * ((p - 1) * P**2 + p * P * Q)))
poly = sp.Poly(K - rowfree, x, z)
bad = [m for m in poly.monoms() if m[0] + m[1] < 2]
print("monomials with <2 row factors (should be none):", bad)
maxdeg_p = max(sp.Poly(c, p).degree() for c in poly.coeffs())
print("max p-degree of coefficients of row monomials:", maxdeg_p)
print("max p-degree of whole K:", sp.Poly(K, p).degree())

# --- (D3) algebra ---------------------------------------------------------
# loop:  D r = 1 + sum_i a^2 E[G_vv G_ii] - (2p-1) a^2 S + 2p a^2 T + Qs + O
# F3  :  p a^2 Cov_i <= a^2 E x_i^2 - r l_i K_vi    (summed: a^2 S/p - r J/p after /p)
# E G_vv G_ii = y_v r * y_i (r - delta_i) + Cov_i ; a^2 y_v y_i = l_i
r, L, Cp, S, T, J, a2, Qs, SumLD, Rr = sp.symbols('r L C_+ S T J a2 Q_* SumLD R')
Dplus = 1 + L - Cp
# upper bound for the RHS of loop using F3:
rhs = 1 + (r**2 * L - r * SumLD) + (a2 * S / p - r * J / p) - (2 * p - 1) * a2 * S + 2 * p * a2 * T + Qs
# inequality Dplus*r <= rhs  <=>  Dplus*r - rhs <= 0 ; express with R = (p-1)S - pT
expr = sp.expand(Dplus * r - rhs)
target = sp.expand((r - 1) * (1 - r * L) + r * SumLD + (1 - 1 / p) * a2 * S + (r / p) * J
                   + 2 * a2 * ((p - 1) * S - p * T) - Qs - r * Cp)
print("(D3) LHS-RHS identity residual:", sp.simplify(expr - target))
