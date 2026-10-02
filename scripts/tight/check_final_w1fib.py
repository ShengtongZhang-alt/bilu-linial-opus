"""Independent check of TB.W1fib-d1 / TB.W1fib-d3 (SecB/W1FibD1.lean, W1FibD3.lean) in the
exact Lean model: V = S + one padded vertex, diagD = 1 + sum c(a^2 y_i y_j), a = 1/sqrt(4(d-1)+4/p),
srcDiag only on S, physInv with the identity padding, zero sources allowed, edges ij with j = v,
j in N and j in N(N) \\ N.  mpmath, 40 digits.

d1: deriv fibPhi(+-1) == W * cfgD at the PD endpoint (relative error).
d3: Q_M = sup_[-1,1] |fibPhi'''| / (W(s) Yb_M(s) + W(s') Yb_M(s')) on regular fibres,
    for several p (d decoupled, chosen so that regular fibres exist), M in {0, 2, 4}.
"""
import itertools
import random
import mpmath as mp

mp.mp.dps = 40
random.seed(11)

n = 7                      # vertex 6 is outside S (identity padding)
S = list(range(6))
edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 4), (4, 5), (5, 6), (0, 6)]
adj = [[0] * n for _ in range(n)]
for (k, l) in edges:
    adj[k][l] = adj[l][k] = 1
v = 0
inS = [k in S for k in range(n)]
N = [w for w in S if adj[v][w]]
NN = sorted(set(w for i in N for w in S if adj[i][w]))
ball = sorted(set([v] + N + NN))


def nb(i):
    return [w for w in S if adj[i][w]]


def cRoot(x):
    return (mp.sqrt(1 + 4 * x) - 1) / 2


def precN(a, tau, y, sig):
    P = mp.zeros(n, n)
    for u in range(n):
        for w in range(n):
            if u == w:
                P[u, u] = (1 + sum(cRoot(a ** 2 * y[u] * y[j]) for j in nb(u))) if inS[u] else 1
            elif inS[u] and inS[w] and adj[u][w]:
                P[u, w] = tau * a * mp.sqrt(y[u]) * mp.sqrt(y[w]) * sig[(min(u, w), max(u, w))]
    return P


def srcDiag(y):
    Y = mp.zeros(n, n)
    for k in range(n):
        Y[k, k] = y[k] if inS[k] else 0
    return Y


def physInv(y, A):
    Ai = A ** -1
    return mp.matrix([[mp.sqrt(y[k]) * Ai[k, l] * mp.sqrt(y[l]) for l in range(n)] for k in range(n)])


def isPD(A):
    try:
        mp.cholesky(A)
        return True
    except (ValueError, ZeroDivisionError):
        return False


class Model:
    def __init__(self, d, p, kap, yp, ym):
        self.d, self.p = d, p
        self.a = 1 / mp.sqrt(4 * (d - 1) + mp.mpf(4) / p)
        self.h = mp.mpf(kap) / p ** 4
        self.yp, self.ym = yp, ym
        self.u = [1 / mp.sqrt(d) if k in N else mp.mpf(0) for k in range(n)]
        self.adjS = [[1 if (inS[k] and inS[l] and adj[k][l]) else 0 for l in range(n)] for k in range(n)]

    def obs(self, A, B, k, i, j):
        """cfgPsi-type observable on the precision pair (A, B) = (P~+, P~-)."""
        a, h = self.a, self.h
        Gp, Gm = physInv(self.yp, A), physInv(self.ym, B)
        Xp = physInv(self.yp, A + h * srcDiag(self.yp))
        Xm = physInv(self.ym, B + h * srcDiag(self.ym))
        u, Ad = self.u, self.adjS
        if k in (0, 1):
            H = (Gp[v, v] / 2) ** 2
            dH = -a * Gp[v, v] * Gp[v, i] * Gp[v, j]
            Xe, eps = Xp, 1
        else:
            H = Gp[v, v] * Gm[v, v] / 4
            dH = a / 2 * (Gp[v, v] * Gm[v, i] * Gm[v, j] - Gp[v, i] * Gp[v, j] * Gm[v, v])
            Xe, eps = Xm, -1
        Xn = Xp
        if k == 0 or k == 2:
            f = u
            df = [mp.mpf(0)] * n
        elif k == 1:
            f = [4 * a ** 2 * sum(Ad[q][l] * (Xp[l, l] / 2) ** 2 * u[l] for l in range(n)) for q in range(n)]
            df = [-4 * a ** 3 * sum(Ad[q][l] * u[l] * Xp[l, l] * Xp[l, i] * Xp[l, j] for l in range(n))
                  for q in range(n)]
        else:
            f = [4 * a ** 2 * sum(Ad[q][l] * (Xp[l, l] / 2) * (Xm[l, l] / 2) * u[l] for l in range(n))
                 for q in range(n)]
            df = [2 * a ** 3 * sum(Ad[q][l] * u[l] * (Xp[l, l] * Xm[l, i] * Xm[l, j]
                                                    - Xm[l, l] * Xp[l, i] * Xp[l, j]) for l in range(n))
                  for q in range(n)]
        U = Xe * mp.diag(f) * Xn
        F = Xe[i, i] * U[j, i] - Xe[j, i] * U[i, i]
        Ud = Xe * mp.diag(df) * Xn
        Fd = Xe[i, i] * Ud[j, i] - Xe[j, i] * Ud[i, i]
        p = self.p
        D = (dH * F + 2 * p * a * (Gp[i, j] - Gm[i, j]) * (H * F)
             + H * (-a * (2 * eps * Xe[i, j] * F + Xn[i, j] * F - Xn[i, i] * Xe[i, j] * U[i, j]))
             + H * Fd - a * (H * (Xe[i, i] * Xn[i, i]) * U[j, j]))
        gstar = Gp[i, i] + Gp[j, j] + Gm[i, i] + Gm[j, j]
        Dst = 1 + max(max(Gp[w, w], Gm[w, w]) for w in ball)
        R = abs(Gp[i, j]) + abs(Gm[i, j])
        return dict(Psi=H * F, D=D, gstar=gstar, Dst=Dst, R=R, H=H)

    def pair(self, sig, i, j, t):
        a = self.a
        e = (min(i, j), max(i, j))
        A = precN(a, 1, self.yp, sig)
        B = precN(a, -1, self.ym, sig)
        s0 = sig[e]
        cp = (t - s0) * a * mp.sqrt(self.yp[i]) * mp.sqrt(self.yp[j])
        cm = (t - s0) * (-a) * mp.sqrt(self.ym[i]) * mp.sqrt(self.ym[j])
        A[i, j] += cp; A[j, i] += cp
        B[i, j] += cm; B[j, i] += cm
        return A, B

    def phi(self, sig, i, j, k, t):
        A, B = self.pair(sig, i, j, t)
        return (mp.det(A) * mp.det(B)) ** self.p * self.obs(A, B, k, i, j)["Psi"]

    def endpoint(self, sig, i, j, k, t):
        A, B = self.pair(sig, i, j, t)
        pd = isPD(A) and isPD(B)
        W = (mp.det(A) * mp.det(B)) ** self.p if pd else mp.mpf(0)
        o = self.obs(A, B, k, i, j)
        o.update(W=W, pd=pd)
        return o


def rand_src(zero_frac=0.2, smax=2):
    return [mp.mpf(0) if random.random() < zero_frac else mp.mpf(random.uniform(0.05, smax)) for _ in range(n)]


fibres = [(i, j) for i in N for j in S if adj[i][j]]
kinds = {(i, j): ('root' if j == v else 'N' if j in N else 'NN') for (i, j) in fibres}

# ---------- d1 ----------
# Error floor 1e-30 * W * (1 + |H|): at 100 digits and step 1e-40 the finite difference has roundoff
# far below it, so endpoints where W cfgD = W Psi = 0 analytically are not reported as failures.
mp.mp.dps = 100
worst_d1 = mp.mpf(0)
cnt_d1 = 0
for trial in range(40):
    d = random.choice([7, 30, 1000])
    p = random.choice([2, 3, 7])
    md = Model(d, p, random.uniform(0.1, 1), rand_src(), rand_src())
    sig = {(min(k, l), max(k, l)): random.choice([-1, 1]) for (k, l) in edges}
    for (i, j) in fibres:
        sig[(min(i, j), max(i, j))] = 1
        for k in range(4):
            for t0 in (1, -1):
                o = md.endpoint(sig, i, j, k, t0)
                if not o["pd"]:
                    continue
                dt = mp.mpf('1e-40')
                fd = (md.phi(sig, i, j, k, t0 + dt) - md.phi(sig, i, j, k, t0 - dt)) / (2 * dt)
                pred = o["W"] * o["D"]
                scale = (abs(o["W"] * o["D"]) + abs(o["W"] * o["Psi"]) +
                         mp.mpf('1e-30') * o["W"] * (1 + abs(o["H"])))
                worst_d1 = max(worst_d1, abs(fd - pred) / scale)
                cnt_d1 += 1
print(f"d1: {cnt_d1} PD endpoints, max |phi'(+-1) - W cfgD| / (|W cfgD| + |W Psi| + 1e-30 W(1+|H|))"
      f" = {mp.nstr(worst_d1, 3)}")
mp.mp.dps = 40


# ---------- d3 ----------
def d3_ratio(md, sig, i, j, k, Ms):
    o1 = md.endpoint(sig, i, j, k, 1)
    sig2 = dict(sig); sig2[(min(i, j), max(i, j))] = -1
    o2 = md.endpoint(sig, i, j, k, -1)
    good = [o for o in (o1, o2) if o["W"] > 0 and 64 * md.p * md.a * o["gstar"] <= 1]
    if not good:
        return None
    dl = mp.mpf('1e-6')
    sup3 = mp.mpf(0)
    for t in [mp.mpf(-1) + mp.mpf(2) * q / 10 for q in range(11)]:
        fs = [md.phi(sig, i, j, k, t + m * dl) for m in (-2, -1, 1, 2)]
        sup3 = max(sup3, abs((fs[3] - 2 * fs[2] + 2 * fs[1] - fs[0]) / (2 * dl ** 3)))
    out = {}
    for M in Ms:
        def Yb(o):
            return md.a ** 3 / (mp.sqrt(md.d) * md.h) * o["Dst"] ** M * (md.p ** 3 * o["R"] ** 2 + md.p)
        out[M] = sup3 / (o1["W"] * Yb(o1) + o2["W"] * Yb(o2))
    return out


Ms = (0, 2, 4)
for p in (3, 10, 30, 100):
    worst = {M: mp.mpf(0) for M in Ms}
    nreg = 0
    for trial in range(4):
        g_est = 8
        d = int((64 * p * g_est * 2) ** 2 / 4) + 10      # a ~ 1/(2 sqrt d) small enough for 64 p a g* <= 1
        md = Model(d, p, random.uniform(0.1, 1), rand_src(0.1), rand_src(0.1))
        sig = {(min(k, l), max(k, l)): random.choice([-1, 1]) for (k, l) in edges}
        for (i, j) in fibres:
            sig[(min(i, j), max(i, j))] = 1
            for k in range(4):
                r = d3_ratio(md, sig, i, j, k, Ms)
                if r is None:
                    continue
                nreg += 1
                for M in Ms:
                    worst[M] = max(worst[M], r[M])
    print(f"d3: p={p}: regular fibres {nreg}, max Q_M " +
          ", ".join(f"M={M}: {mp.nstr(worst[M], 3)}" for M in Ms))
