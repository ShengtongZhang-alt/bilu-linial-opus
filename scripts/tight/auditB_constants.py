"""AUDIT-B: explicit constants and the GCI-free score-difference identity.

Run: /tmp/tight-venv/bin/python scripts/tight/auditB_constants.py
"""
import sympy as sp
import mpmath as mp

# (1) c_j in e^{t^2/2}/cosh t = 1 + sum_{j>=2} c_j t^{2j}
t = sp.symbols('t')
ser = sp.series(sp.exp(t**2 / 2) / sp.cosh(t), t, 0, 42).removeO()
cs = [sp.nsimplify(ser.coeff(t, 2 * j)) for j in range(21)]
print("c_0..c_4 =", cs[:5])
print("max_j |c_j|^(1/j), j=2..20:", max(abs(float(cs[j])) ** (1 / j) for j in range(2, 21)))

# (2) endpoint identities on [-1,1]: E xi f(xi) = E f'(xi) + R1, |R1| <= (1/3) sup|f'''|;
#     E xi f = E(f' - f'''/3) + R5, exact through degree 4; Peano constant for R5:
s = sp.symbols('s')
def Lam(f):
    fp, f3 = sp.diff(f, s), sp.diff(f, s, 3)
    return sp.simplify((f.subs(s, 1) - f.subs(s, -1)) / 2 - (fp.subs(s, 1) + fp.subs(s, -1)) / 2
                       + (f3.subs(s, 1) + f3.subs(s, -1)) / 6)
print("Lambda(s^k), k=0..5:", [Lam(s**k) for k in range(6)])
u = sp.symbols('u')
# Peano kernel K(u) = Lambda_s[(s-u)_+^4/4!]
def Kpe(uu):
    f = lambda x: max(x - uu, 0) ** 4 / 24
    fp = lambda x: max(x - uu, 0) ** 3 / 6
    f3 = lambda x: max(x - uu, 0)
    return (f(1) - f(-1)) / 2 - (fp(1) + fp(-1)) / 2 + (f3(1) + f3(-1)) / 6
print("int |Peano kernel| (|R5| <= this * sup|f^(5)|):", mp.quad(lambda x: abs(Kpe(float(x))), [-1, 1]))

# (3) score-difference identity from the two row equations:
#   (2p-1) Sp - 2p T = Bp + Ep,   (2p-1) Sm - 2p T = Bm + Em
p, Sp, Sm, T, Bp, Bm, Ep, Em = sp.symbols('p S_p S_m T B_p B_m E_p E_m')
sol = sp.solve([(2 * p - 1) * Sp - 2 * p * T - Bp - Ep, (2 * p - 1) * Sm - 2 * p * T - Bm - Em], [Sp, Sm])
diff_energy = sp.simplify(sol[Sp] + sol[Sm] - 2 * T)
print("S+ + S- - 2T =", sp.factor(diff_energy))
# sum identity alone cannot bound S+ + S- without a sign on T:
print("S+ + S- =", sp.factor(sol[Sp] + sol[Sm]))
