import sympy as sp
import mpmath as mp

# ---------- Section 5: explicit excess ----------
t, q, z = sp.symbols('t q z', positive=True)
a = 1/t + t
b = 1/t + 2*t
g = lambda eta: 1/(b - 2/(a - eta))
m = sp.simplify((g(1) + g(-1))/2)
m_claim = t*(1+t**2+t**4+2*t**6)/(1+t**2+t**4+4*t**8)
print("S5 mean formula ok:", sp.simplify(m - m_claim) == 0)

# 3x3 effective matrix check of g_eta (triangle o,v1,v2 with signs s1,s2,s3)
s1, s2, s3 = sp.symbols('s1 s2 s3')
Mx = sp.Matrix([[b, -s1, -s2], [-s1, a, -s3], [-s2, -s3, a]])
g00 = sp.simplify(Mx.inv()[0, 0].subs({s1: 1, s2: 1, s3: -1}))
print("S5 3x3 resolvent (eta=-1) ok:", sp.simplify(g00 - g(-1)) == 0)

F = -1 + (q-1)*z + (q-1)*z**2 + q*z**3 + (2*q-4)*z**4
lhs_minus_rhs = sp.expand(q*z*(1+z+z**2+2*z**3) - (1+z+z**2+4*z**4))
print("S5 F_q matches root eqn:", sp.simplify(F - lhs_minus_rhs) == 0)
# m(t) > 1/(q t)  <=>  F_q(t^2) > 0  (denominators positive)
expr = sp.expand((m_claim*q*t - 1)*(1+t**2+t**4+4*t**8))
print("S5 equivalence ok:", sp.simplify(expr - F.subs(z, t**2)) == 0)

mp.mp.dps = 60
for qq in [3, 4, 5, 10, 30, 100]:
    Fq = lambda zz: -1 + (qq-1)*zz + (qq-1)*zz**2 + qq*zz**3 + (2*qq-4)*zz**4
    zq = mp.findroot(Fq, 1.0/qq)
    Rq = zq**-0.5 + qq*mp.sqrt(zq)
    ex = Rq - 2*mp.sqrt(qq)
    print(f"S5 q={qq}: z_q={mp.nstr(zq,12)} <1/q={zq < 1.0/qq}  R_q-2sqrt(q)={mp.nstr(ex,8)}  *q^(11/2)={mp.nstr(ex*mp.mpf(qq)**5.5,8)}")

# ---------- Section 6: buffered map ----------
def section6(qq, c, L):
    qq = mp.mpf(qq); c = mp.mpf(c)
    zz = 2 + c*qq**-4
    tau = (zz - mp.sqrt(zz**2-4))/2
    yp = (zz + mp.sqrt(zz**2-4))/2
    bb = 1 - 2/qq
    kp = (2/qq)/(zz - (1-1/qq)*tau - qq**-0.5)
    km = (2/qq)/(zz - (1-1/qq)*tau + qq**-0.5)
    ap, am = zz - kp, zz - km
    Mt = mp.matrix([[0, 1], [-1, zz]])**L
    A, B, C, D = Mt[0, 0], Mt[0, 1], Mt[1, 0], Mt[1, 1]
    Ep, Em = ap*C - bb*A, am*C - bb*A
    Hp, Hm = ap*D - bb*B, am*D - bb*B
    E0, H0, Dl = (Ep+Em)/2, (Hp+Hm)/2, ap - am
    ML = lambda y: (C*y+D)/(E0*y + H0 - Dl**2*C*(C*y+D)/(4*E0))
    phiL = lambda tt: (A*tt+B)/(C*tt+D)
    chi = lambda aa, tt: 1/(aa - bb*phiL(tt))
    # brute-force minimise (chi+(y+w)+chi-(y-w))/2 over w near the claimed optimum
    y = yp
    wclaim = -Dl*(C*y+D)/(2*E0)
    obj = lambda w: (chi(ap, y+w) + chi(am, y-w))/2
    wnum = mp.findroot(lambda w: mp.diff(obj, w), wclaim)
    return dict(drift=(ML(yp)-yp)*qq**3, lead=4*L/(L+1)-2-4*mp.sqrt(c),
                ML_vs_bruteforce=ML(yp)-obj(wnum), w_claim=wclaim, w_num=wnum,
                w_lead=-2*qq**-1.5/(L+1), dML=(mp.diff(ML, tau)-1)*qq,
                poles=[-Hp/Ep, -Hm/Em], zero=-D/C, signs=(C < 0, Ep < 0, Em < 0),
                below=(yp + wnum < -Hp/Ep, yp - wnum < -Hm/Em))

for (qq, c, L) in [(10**3, 0.2, 20), (10**4, 0.2, 20), (10**5, 0.2, 20), (10**6, 0.24, 60)]:
    r = section6(qq, c, L)
    print(f"S6 q={qq} c={c} L={L}: q^3*drift={mp.nstr(r['drift'],8)} lead={mp.nstr(r['lead'],8)}"
          f" ML-bruteforce={mp.nstr(r['ML_vs_bruteforce'],3)} w_claim/w_num={mp.nstr(r['w_claim']/r['w_num'],8)}"
          f" w/w_lead={mp.nstr(r['w_num']/r['w_lead'],6)} q*(M'(tau)-1)={mp.nstr(r['dML'],6)}"
          f" poles={[mp.nstr(p,8) for p in r['poles']]} 1+1/(L+1)={mp.nstr(1+mp.mpf(1)/(L+1),8)}"
          f" zero={mp.nstr(r['zero'],8)} 1+1/L={mp.nstr(1+mp.mpf(1)/L,8)} C,E+,E-<0:{r['signs']} optimum below poles:{r['below']}")
