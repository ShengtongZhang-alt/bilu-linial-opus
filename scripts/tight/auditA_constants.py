"""AUDIT-A numeric checks for lines 237-625 of docs/second_order_bilu_linial_tight.tex.

1. c_j (coefficients of exp(t^2/2)/cosh t in t^{2j}) via the recursion
   sum_{j=0}^m c_j/(2m-2j)! = 1/(2^m m!), and the bound |c_j| <= 1.
2. K_T: Peano constant of the endpoint functional (E1):
   L(f) = (f(1)-f(-1))/2 - (f'(1)+f'(-1))/2 + (f'''(1)+f'''(-1))/6,
   |L(f)| <= K_T sup_[-1,1] |f^{(5)}|.
3. K_L: remainder constant of the one-coordinate comparison (E4),
   K_L = 1/(2^{L+2}(L+2)!) + sum_{j in {0,2..L+1}} |c_j|/(2L+4-2j)!.
4. Parameter facts: s <= 2+3/d, d a^2 s^2 <= 1+4/d, eps bounds.
"""
from fractions import Fraction as Fr
from math import factorial, cosh
import mpmath as mp

# ---------- 1. c_j ----------
def cj_list(n):
    c = []
    for m in range(n + 1):
        val = Fr(1, 2**m * factorial(m))
        for j in range(m):
            val -= c[j] / factorial(2 * m - 2 * j)
        c.append(val)
    return c

c = cj_list(60)
assert c[0] == 1 and c[1] == 0 and c[2] == Fr(1, 12), (c[:3])
print("c_0..c_8 =", [str(x) for x in c[:9]])
print("max_{j<=60} |c_j| =", float(max(abs(x) for x in c)))
ratios = [float(abs(c[j + 1] / c[j])) for j in range(2, 59) if c[j] != 0]
print("|c_{j+1}/c_j| for large j ->", ratios[-3:], " (4/pi^2 =", 4 / mp.pi**2, ")")
# induction margin for |c_m| <= 1: 1/(2^m m!) + (cosh 1 - 1) <= 1 for m >= 2
print("cosh(1)-1 =", cosh(1) - 1, "; 1/8 + cosh(1)-1 =", 1 / 8 + cosh(1) - 1)
# signs
print("signs of c_2..c_12:", ["+" if x > 0 else "-" for x in c[2:13]])
# series check against mpmath
mp.mp.dps = 40
t = mp.mpf("0.7")
lhs = mp.e ** (t**2 / 2) / mp.cosh(t)
rhs = sum(mp.mpf(c[j].numerator) / c[j].denominator * t ** (2 * j) for j in range(60))
print("series check |lhs-rhs| =", abs(lhs - rhs))

# ---------- 2. K_T (Peano kernel of the endpoint functional) ----------
# L(f) vanishes on polynomials of degree <= 4 (check), so
# L(f) = int_{-1}^{1} K(u) f^{(5)}(u) du, K(u) = L_x[(x-u)_+^4/24].
x = mp.mpf
def L_on_poly(coeffs):
    # f(x)=sum coeffs[k] x^k
    f = lambda z: sum(cf * z**k for k, cf in enumerate(coeffs))
    d1 = lambda z: sum(k * cf * z ** (k - 1) for k, cf in enumerate(coeffs) if k >= 1)
    d3 = lambda z: sum(k * (k - 1) * (k - 2) * cf * z ** (k - 3) for k, cf in enumerate(coeffs) if k >= 3)
    return (f(1) - f(-1)) / 2 - (d1(1) + d1(-1)) / 2 + (d3(1) + d3(-1)) / 6

for k in range(6):
    co = [0] * k + [1]
    print(f"L(x^{k}) =", L_on_poly([Fr(v) for v in co]))

def K(u):
    # (x-u)_+^4/24 evaluated through L; for x = 1 the truncated power is (1-u)^4/24, for x=-1 it is 0
    # derivatives at x=1: d1 = (1-u)^3/6, d3 = (1-u); at x=-1 all vanish (u > -1)
    return ((1 - u) ** 4 / 24) / 2 - ((1 - u) ** 3 / 6) / 2 + (1 - u) / 6

KT = mp.quad(lambda u: abs(K(u)), [-1, 1])
print("K_T = int |K| =", KT, "(sign-definite?)", mp.quad(K, [-1, 1]))
# test with f = x^5: L(x^5) = 1 - 5 + 20 = ... f^{(5)} = 120
print("L(x^5) =", L_on_poly([0, 0, 0, 0, 0, 1]), " vs 120*int K =", 120 * mp.quad(K, [-1, 1]))

# ---------- 3. K_L ----------
best = 0
for L in range(0, 40):
    KL = Fr(1, 2 ** (L + 2) * factorial(L + 2))
    for j in [0] + list(range(2, L + 2)):
        KL += abs(c[j]) / factorial(2 * L + 4 - 2 * j)
    best = max(best, float(KL))
    if L < 6:
        print(f"K_{L} =", float(KL))
print("sup_L K_L (L<40) =", best)

# ---------- 4. parameter facts ----------
def params(d, p):
    q = d - 1
    Delta = mp.mpf(4) / p
    # q eta^2 = Delta (1 - eta)
    eta = (-Delta + mp.sqrt(Delta**2 + 4 * q * Delta)) / (2 * q)
    tau = (1 - eta) / q
    s = (1 + q * tau) / (1 - tau)
    R2 = 4 * q + Delta
    a2 = 1 / R2
    return dict(eta=eta, eps=eta / 2, s=s, a2s2d=a2 * s * s * d, a2=a2, tau=tau)

for d in [11, 20, 100, 10**4, 10**8]:
    for p in [2, 5, max(2, int(d ** (2 / 17)))]:
        P = params(d, p)
        ok1 = P["s"] <= 2 + mp.mpf(3) / d
        ok2 = P["a2s2d"] <= 1 + mp.mpf(4) / d
        ok3 = P["eps"] <= 1 / mp.sqrt(p * (d - 1))
        ok4 = P["eps"] >= 1 / mp.sqrt(2 * p * (d - 1))
        print(f"d={d:>9} p={p:>3}: s-2={float(P['s']-2):.3e} (<=3/d:{ok1}), "
              f"da^2s^2-1={float(P['a2s2d']-1):.3e} (<=4/d:{ok2}), eps bounds:{ok3},{ok4}")

# ---------- 5. regime p <= 2q/9: s <= 2, d a^2 s^2 <= 1, eta >= 3/q ----------
bad = 0
for d in [12, 20, 50, 100, 1000, 10**5, 10**9]:
    q = d - 1
    for p in range(2, max(3, (2 * q) // 9) + 1, max(1, ((2 * q) // 9) // 50)):
        P = params(d, p)
        if not (P["s"] <= 2 and P["a2s2d"] <= 1 and P["eta"] >= mp.mpf(3) / q):
            bad += 1
            print("regime fact fails at", d, p, float(P["s"]), float(P["a2s2d"]))
print("regime facts (s<=2, d a^2 s^2<=1, eta>=3/q for p<=2q/9): failures =", bad)

# ---------- 6. rank-two fibre formulas (symbolic) ----------
import sympy as sp
t, aa = sp.symbols("t a")
Gvv, Gii, Gvi = sp.symbols("Gvv Gii Gvi")
S = sp.Matrix([[Gvv, Gvi], [Gvi, Gii]])
J = sp.Matrix([[0, 1], [1, 0]])
# restricted to span{e_v, e_i}: G(t) block = S (I + t a J S)^{-1}
Gt = sp.simplify(S * (sp.eye(2) + t * aa * J * S).inv())
delta = sp.expand((sp.eye(2) + t * aa * J * S).det())
print("det ratio delta(t) =", sp.factor(delta))
print("G(t)_vi * delta - (Gvi + t a (Gvv Gii - Gvi^2)) =",
      sp.simplify(Gt[0, 1] * delta - (Gvi + t * aa * (Gvv * Gii - Gvi**2))))
print("G(t)_vv * delta =", sp.factor(sp.simplify(Gt[0, 0] * delta)))
