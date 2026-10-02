"""Exact counterexample to `d10_real` (BiluLinial/Tight/Contact/Real.lean) when `CB < 0`.

Statement (for all real CB C9 C9b Cc):
  exists C > 0, forall d p h, TRegime d p -> 0 < h -> forall S R Gt Qb Qf,
    (1 - CB*etaBL) Qb - CB*epsBL <= Gt -> |R - Gt| <= C9*ErowP(S) -> Qb <= C9b*p ->
    Qf <= Qb + Cc*p/(d h sqrt h) -> Qf - C*Err10(S) <= R.

Instance: CB = -1, C9 = 1, C9b = 1, Cc = 0; d = 10^51, p = 10^6 (p^17 = d^2, so TRegime holds),
h = 1, S = 0, Qb = Qf = -M, Gt = R = -(1+eta) M + epsBL.  The conclusion is equivalent to
eta*M <= C*Err10 + epsBL, which fails once M > (C*U + epsBL)/eta for an upper bound U >= Err10.
All quantities except the square roots inside Err10/ErowP are rational; we only need Err10 <= U
(proved below with crude rational bounds) and ErowP >= 0 (obvious).
Run: /tmp/tight-venv/bin/python scripts/tight/check_contact_d10.py
"""
from fractions import Fraction as Fr

d = 10**51
p = 10**6
h = Fr(1)
assert p**17 <= d**2 and 10**6 <= p  # TRegime

vth = Fr(1, d**10)
eta = Fr(p**4, d) + Fr(p, d) / h            # etaBL = p^4/d + p/(d h)
eps_bl = vth * (p**5 + Fr(p**2) / h) + vth  # epsBL

# Crude rational upper bound U >= Err10(d,p,h,S=0):
# Err10 = Gam*sqrt(1) + p^13/d^2 + vth + p^5/d + p^2/(d h) + p/(d h sqrt h) + epsBL,
# Gam = p^4 sqrt(p*dbar/d), dbar = eps + p^4/d + (p/d)^(1/3) <= 1 (eps = r - 1 < 1), so
# Gam <= p^4 * sqrt(p/d) <= p^4 * p/... ; use sqrt(p/d) <= 1 (p <= d): Gam <= p^4.  Very crude
# but rational and valid; any finite U works.
U = Fr(p**4) + Fr(p**13, d**2) + vth + Fr(p**5, d) + Fr(p**2, d) + Fr(p, d) + eps_bl

for C in [Fr(1), Fr(10**6), Fr(10**30)]:
    M = (C * U + eps_bl) / eta + 1
    Qb = -M
    Qf = Qb
    Gt = (1 + eta) * Qb + eps_bl          # (1 - CB*eta) Qb - CB*epsBL with CB = -1, equality
    R = Gt
    # hypotheses
    assert (1 - (-1) * eta) * Qb - (-1) * eps_bl <= Gt
    assert abs(R - Gt) == 0                 # <= 1 * ErowP(0), since ErowP >= vth > 0
    assert Qb <= 1 * p
    assert Qf <= Qb + 0
    # conclusion Qf - C*Err10 <= R with Err10 <= U: it suffices to show Qf - C*U > R
    lhs_lower = Qf - C * U                  # Qf - C*Err10 >= Qf - C*U
    print(f"C = {float(C):.3g}: Qf - C*U - R = {float(lhs_lower - R):.6g} (> 0 means conclusion fails)")
    assert lhs_lower > R

print("d10_real is FALSE for CB = -1 (any C): counterexample verified with exact rationals.")

# With CB >= 0 the statement holds: R >= (1 - CB eta) Qb - CB epsBL - C9 Erow and
# -CB*eta*Qb >= -CB*eta*|C9b|*p in both cases Qb >= 0 (Qb <= C9b p) and Qb < 0 (term >= 0).
