"""Statement checks (workflow rule 2) for BiluLinial/Tight/SourceMax.lean and
BiluLinial/Tight/SourceMax/{Glue,Law,Phys,Jacobian,Deriv,FOC,LinAlg}.lean.

Exact enumeration of the paired law in the normalized coordinates of BiluLinial/Tight/Defs.lean
(precN, wt, Zw, lawE, hN) and Ctx.lean (greenP, walkB, walkK), on tiny graphs, with Lean junk
values (inverse of a singular matrix = 0, sqrt of a negative = 0, x/0 = 0). Only the signs of the
edges inside S are enumerated; the other coordinates of `Config V` multiply numerator and
denominator of `lawE` by the same factor.
Run: /tmp/tight-venv/bin/python scripts/tight/check_tools_sourcemax.py
"""
import itertools
import numpy as np
from scipy import optimize

rng = np.random.default_rng(11)

GRAPHS = {
    "K1": (1, []),
    "K2": (2, [(0, 1)]),
    "P3": (3, [(0, 1), (1, 2)]),
    "K13": (4, [(0, 1), (0, 2), (0, 3)]),
    "K3": (3, [(0, 1), (1, 2), (0, 2)]),
    "C4": (4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
    "K4": (4, [(i, j) for i in range(4) for j in range(i + 1, 4)]),
    "paw": (4, [(0, 1), (1, 2), (0, 2), (2, 3)]),
    "diamond": (4, [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)]),
}


def lsqrt(x):
    return np.sqrt(x) if x > 0 else 0.0


def ldiv(x, y):
    return 0.0 if y == 0 else x / y


def linv(M):
    if M.shape[0] == 0:
        return M
    d = np.linalg.det(M)
    if d == 0:
        return np.zeros_like(M)
    try:
        return np.linalg.inv(M)
    except np.linalg.LinAlgError:
        return np.zeros_like(M)


def is_pd(M):
    return M.shape[0] == 0 or np.linalg.eigvalsh(M)[0] > 0


def params(d, p):
    q, D = d - 1.0, 4.0 / p
    a = 1 / np.sqrt(4 * q + D)
    eta = (np.sqrt(D * D + 4 * q * D) - D) / (2 * q)
    ts = (1 - eta) / q
    s = (1 + q * ts) / (1 - ts)
    return dict(a=a, s=s, r=1 + eta / 2, ts=ts, eta=eta)


class Law:
    def __init__(self, n, edges, S=None):
        self.n = n
        self.adj = np.zeros((n, n), bool)
        for i, j in edges:
            self.adj[i, j] = self.adj[j, i] = True
        self.S = list(range(n)) if S is None else list(S)
        self.inS = np.zeros(n, bool)
        self.inS[self.S] = True
        self.Sedges = [(i, j) for (i, j) in edges if self.inS[i] and self.inS[j]]
        self.sigmas = [dict(zip(self.Sedges, sg)) for sg in itertools.product([1.0, -1.0], repeat=len(self.Sedges))]

    def nbhd(self, u):
        return [j for j in self.S if self.adj[u, j]]

    def sgn(self, sig, u, w):
        return sig.get((u, w), sig.get((w, u), 1.0))

    @staticmethod
    def cRoot(x):
        return (lsqrt(1 + 4 * x) - 1) / 2

    def cEdge(self, a, y, i, j):
        return self.cRoot(a * a * y[i] * y[j])

    def tauEdge(self, a, y, i, j):
        c = self.cEdge(a, y, i, j)
        return ldiv(c, 1 + c)

    def diagD(self, a, y, i):
        return 1 + sum(self.cEdge(a, y, i, j) for j in self.nbhd(i))

    def precZ(self, a, y, i):
        return ldiv(self.diagD(a, y, i), y[i])

    def precN(self, a, tau, y, sig):
        n = self.n
        P = np.eye(n)
        for u in self.S:
            P[u, u] = self.diagD(a, y, u)
        for (u, w) in self.Sedges:
            v = tau * a * (lsqrt(y[u]) * lsqrt(y[w])) * self.sgn(sig, u, w)
            P[u, w] = P[w, u] = v
        return P

    def posSrc(self, y):
        return [u for u in self.S if y[u] > 0]

    def precPhys(self, a, tau, y, sig):
        n, ps = self.n, set(self.posSrc(y))
        P = np.eye(n)
        for u in ps:
            P[u, u] = self.precZ(a, y, u)
        for (u, w) in self.Sedges:
            if u in ps and w in ps:
                P[u, w] = P[w, u] = tau * a * self.sgn(sig, u, w)
        return P

    def walkB(self, a, y):
        n = self.n
        Bm = np.eye(n)
        for u in self.S:
            Bm[u, u] = 1 + sum(self.tauEdge(a, y, u, j) ** 2 / (1 - self.tauEdge(a, y, u, j) ** 2) for j in self.nbhd(u))
        for (u, w) in self.Sedges:
            t = self.tauEdge(a, y, u, w)
            Bm[u, w] = Bm[w, u] = -(t / (1 - t * t))
        return Bm

    def configs(self, p, a, yp, ym):
        """per supported sign vector: weight, P+^-1, P-^-1 (normalized)"""
        out = []
        for sig in self.sigmas:
            Pp, Pm = self.precN(a, 1.0, yp, sig), self.precN(a, -1.0, ym, sig)
            if is_pd(Pp) and is_pd(Pm):
                out.append((sig, (np.linalg.det(Pp) * np.linalg.det(Pm)) ** p, linv(Pp), linv(Pm)))
            else:
                out.append((sig, 0.0, linv(Pp), linv(Pm)))
        return out

    def lawE(self, p, a, yp, ym, f):
        """f(sig, Ginv_plus_normalized, Ginv_minus_normalized)"""
        cf = self.configs(p, a, yp, ym)
        Z = sum(w for (_, w, _, _) in cf)
        return ldiv(sum(w * f(sig, Gp, Gm) for (sig, w, Gp, Gm) in cf), Z), Z

    def moment(self, p, a, yp, ym, i, k):
        return self.lawE(p, a, yp, ym, lambda s, Gp, Gm: Gp[i, i] ** k)[0]

    def greenP(self, y, Ginv, i, j):
        return lsqrt(y[i]) * Ginv[i, j] * lsqrt(y[j])

    def momC(self, p, a, yp, ym, k, i, l):
        E = lambda f: self.lawE(p, a, yp, ym, f)[0]
        g = lambda Gp, u, w: self.greenP(yp, Gp, u, w)
        return (p * (E(lambda s, Gp, Gm: g(Gp, i, i) ** k * g(Gp, l, l))
                     - E(lambda s, Gp, Gm: g(Gp, i, i) ** k) * E(lambda s, Gp, Gm: g(Gp, l, l)))
                - k * E(lambda s, Gp, Gm: g(Gp, i, i) ** (k - 1) * g(Gp, i, l) ** 2))


fails = {}


def record(name, ok, info=""):
    d = fails.setdefault(name, [0, 0, ""])
    d[0] += 1
    if not ok:
        d[1] += 1
        if not d[2]:
            d[2] = info


def rand_src(n, cap, pzero=0.25):
    y = rng.uniform(0, cap, size=n)
    y[rng.uniform(size=n) < pzero] = 0.0
    if rng.uniform() < 0.2:
        y[rng.integers(0, n)] = cap
    return y


def update(y, j, val):
    z = y.copy()
    z[j] = val
    return z


# ======================= Phys + Law identities =======================
for name, (n, edges) in GRAPHS.items():
    for trial in range(25):
        d = max(2, max([sum(1 for e in edges if u in e) for u in range(n)] + [0]))
        p = int(rng.choice([1, 2, 3, 5, 8]))
        a = params(d, max(p, 1))["a"] * rng.choice([1.0, 1.0, 2.5])
        S = sorted(rng.choice(n, size=rng.integers(1, n + 1), replace=False).tolist()) if rng.uniform() < 0.3 else None
        L = Law(n, edges, S)
        cap = params(d, max(p, 1))["s"] * rng.choice([1.0, 1.0, 3.0])
        yp, ym = rand_src(n, cap), rand_src(n, cap)
        ps = L.posSrc(yp)
        m = np.array([lsqrt(yp[u]) if u in ps else 1.0 for u in range(n)])
        fac = np.prod([yp[u] for u in ps]) if ps else 1.0
        tag = f"{name} S={L.S} yp={np.round(yp, 3)}"
        record("physFactor_pos", fac > 0)
        for sig in L.sigmas:
            PN, PP = L.precN(a, 1.0, yp, sig), L.precPhys(a, 1.0, yp, sig)
            record("precPhys_isHermitian", np.allclose(PP, PP.T))
            record("precN_eq_scale", np.allclose(PN, np.diag(m) @ PP @ np.diag(m), atol=1e-12), tag)
            record("det_precN", np.isclose(np.linalg.det(PN), fac * np.linalg.det(PP), rtol=1e-9, atol=1e-12), tag)
            record("posDef_precN_iff", is_pd(PN) == is_pd(PP), tag)
            Gi, Pi = linv(PN), linv(PP)
            for u in ps:
                record("hN_eq_phys", np.isclose(Gi[u, u], Pi[u, u] / yp[u], rtol=1e-9), tag)
                for w in ps:
                    record("greenP_eq_phys", np.isclose(L.greenP(yp, Gi, u, w), Pi[u, w], rtol=1e-9, atol=1e-12), tag)
            PMn = L.precN(a, -1.0, ym, sig)
            wtm = np.linalg.det(PMn) ** p if is_pd(PMn) else 0.0
            posPow = np.linalg.det(PP) ** p if is_pd(PP) else 0.0
            wt = (np.linalg.det(PN) * np.linalg.det(PMn)) ** p if (is_pd(PN) and is_pd(PMn)) else 0.0
            record("wt_eq_phys", np.isclose(wt, fac ** p * wtm * posPow, rtol=1e-9, atol=1e-300), tag)
            record("wt_nonneg", wt >= 0)
            for i in ps:
                for k in range(0, 4):
                    glue = posPow * Pi[i, i] ** k
                    record("wt_mul_hN_pow_eq_phys", np.isclose(wt * Gi[i, i] ** k, fac ** p * wtm * glue / yp[i] ** k,
                                                               rtol=1e-8, atol=1e-300), tag)
            if wt != 0:
                for i in range(n):
                    record("hN_pos", Gi[i, i] > 0, tag)
        # lawE in physical form, with f = a random function of the sign vector
        fvals = {tuple(sorted(s.items())): rng.normal() for s in L.sigmas}
        f = lambda s, Gp, Gm: fvals[tuple(sorted(s.items()))]
        e1, Z = L.lawE(p, a, yp, ym, f)
        num = den = 0.0
        for sig in L.sigmas:
            PP, PMn = L.precPhys(a, 1.0, yp, sig), L.precN(a, -1.0, ym, sig)
            ww = (np.linalg.det(PMn) ** p if is_pd(PMn) else 0.0) * (np.linalg.det(PP) ** p if is_pd(PP) else 0.0)
            num += ww * fvals[tuple(sorted(sig.items()))]
            den += ww
        record("lawE_eq_phys", np.isclose(e1, ldiv(num, den), rtol=1e-9, atol=1e-12), tag)
        record("Zw_nonneg", Z >= 0)
        if Z > 0:
            # Lyapunov
            for i in range(n):
                for k in range(0, 5):
                    mk = L.moment(p, a, yp, ym, i, k)
                    mk1 = L.moment(p, a, yp, ym, i, k + 1)
                    record("lawE_pow_succ_le", mk ** (k + 1) <= mk1 ** k * (1 + 1e-10) + 1e-12, tag)
            # zero source
            for i in range(n):
                y0 = update(yp, i, 0.0)
                e0, Z0 = L.lawE(p, a, y0, ym, lambda s, Gp, Gm: 1.0)
                if Z0 > 0:
                    for k in range(0, 5):
                        record("lawE_hN_pow_of_source_zero", np.isclose(L.moment(p, a, y0, ym, i, k), 1.0, rtol=1e-12), tag)
            # swap
            for i in range(n):
                for k in range(0, 4):
                    lhs = L.lawE(p, a, yp, ym, lambda s, Gp, Gm: Gm[i, i] ** k)[0]
                    rhs = L.lawE(p, a, ym, yp, lambda s, Gp, Gm: Gp[i, i] ** k)[0]
                    record("lawE_hN_neg_pow_swap", np.isclose(lhs, rhs, rtol=1e-10), tag)
        # precPhys_update, posSrc_update
        for j in ps:
            t = float(rng.uniform(-1, 1) * yp[j])
            y2 = update(yp, j, yp[j] - t)
            record("posSrc_update", L.posSrc(y2) == ps)
            for sig in L.sigmas[:2]:
                delta = np.array([L.precZ(a, y2, u) - L.precZ(a, yp, u) if u in ps else 0.0 for u in range(n)])
                record("precPhys_update", np.allclose(L.precPhys(a, 1.0, y2, sig), L.precPhys(a, 1.0, yp, sig) + np.diag(delta)))

# informational: precN_eq_scale needs y >= 0
L = Law(3, GRAPHS["P3"][1])
y = np.array([0.7, -0.5, 1.0])
sig = L.sigmas[0]
ps = L.posSrc(y)
m = np.array([lsqrt(y[u]) if u in ps else 1.0 for u in range(3)])
print("[info] precN_eq_scale with a negative source y_1 = -0.5:",
      np.allclose(L.precN(0.6, 1.0, y, sig), np.diag(m) @ L.precPhys(0.6, 1.0, y, sig) @ np.diag(m)),
      "(hypothesis hy needed, present)")

# ======================= Jacobian =======================
for name, (n, edges) in GRAPHS.items():
    L = Law(n, edges)
    for trial in range(20):
        a = float(rng.uniform(0, 1.5))
        y = rand_src(n, 3.0)
        for u in L.posSrc(y):
            for j in L.posSrc(y):
                h = 1e-6 * y[j]
                fd = (L.precZ(a, update(y, j, y[j] - h), u) - L.precZ(a, update(y, j, y[j] + h), u)) / (2 * h)
                ex = L.walkB(a, y)[u, j] / (y[u] * y[j])
                record("hasDerivAt_precZ_update", abs(fd - ex) <= 1e-6 * (1 + abs(ex)), f"{name} u={u} j={j} fd={fd} ex={ex}")


# ======================= Deriv (moment derivative) =======================
def deriv_formula(L, p, a, yp, ym, i, j, k):
    ps = L.posSrc(yp)
    Bm = L.walkB(a, yp)
    tot = sum(Bm[l, j] / (yp[l] * yp[j]) * L.momC(p, a, yp, ym, k, i, l) for l in ps) / yp[i] ** k
    if i == j:
        tot += k * L.moment(p, a, yp, ym, i, k) / yp[i]
    return tot


def mt(L, p, a, yp, ym, i, j, k, t):
    return L.moment(p, a, update(yp, j, yp[j] - t), ym, i, k)


for name in ("K2", "P3", "K13", "K3", "C4"):
    n, edges = GRAPHS[name]
    L = Law(n, edges)
    for trial in range(12):
        d = max(2, max(sum(1 for e in edges if u in e) for u in range(n)))
        p = int(rng.choice([3, 4, 6, 9]))
        a = params(d, p)["a"] * rng.choice([1.0, 1.6])
        yp, ym = rand_src(n, 2.5), rand_src(n, 2.5)
        if L.lawE(p, a, yp, ym, lambda s, Gp, Gm: 1.0)[1] <= 0:
            continue
        ps = L.posSrc(yp)
        for i in ps:
            for j in ps:
                for k in range(0, p - 1):
                    h = 1e-5 * yp[j]
                    fd = (mt(L, p, a, yp, ym, i, j, k, h) - mt(L, p, a, yp, ym, i, j, k, -h)) / (2 * h)
                    ex = deriv_formula(L, p, a, yp, ym, i, j, k)
                    record("hasDerivAt_moment", abs(fd - ex) <= 1e-5 * (1 + abs(ex)),
                           f"{name} p={p} k={k} i={i} j={j} fd={fd} ex={ex}")

# support-boundary case: a sign vector with P+ singular PSD at t = 0 (glue across the boundary)
n, edges = GRAPHS["K4"]
L = Law(n, edges)
p_ = 4
ym = np.full(n, 0.3)
found = None
for attempt in range(20000):
    a = float(rng.uniform(0.3, 3.0))
    sig_target = L.sigmas[rng.integers(0, len(L.sigmas))]
    base = rng.uniform(0.2, 5.0, size=n)
    lmin = lambda y2: np.linalg.eigvalsh(L.precN(a, 1.0, y2, sig_target))[0]
    if lmin(update(base, 3, 0.01)) > 0 and lmin(update(base, 3, 200.0)) < 0:
        found = (a, sig_target, base, lmin)
        break
if found:
    a, sig_target, base, lmin = found
    lo, hi = 0.01, 200.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if lmin(update(base, 3, mid)) > 0:
            lo = mid
        else:
            hi = mid
    yb = update(base, 3, lo)
    nb = sum(1 for s in L.sigmas if abs(np.linalg.eigvalsh(L.precN(a, 1.0, yb, s))[0]) < 1e-9)
    print(f"[boundary] K4, a={a:.3f}: lambda_min(P+_sigma) at y_3={lo:.12f} is {lmin(yb):.2e}"
          f" ({nb} sign vectors on the boundary)")
    for (k, pp) in ((0, p_), (1, p_), (2, p_), (2, 3), (1, 2)):
        for (i, j) in ((0, 3), (3, 3)):
            h = 1e-6
            fwd = (mt(L, pp, a, yb, ym, i, j, k, h) - mt(L, pp, a, yb, ym, i, j, k, 0)) / h
            bwd = (mt(L, pp, a, yb, ym, i, j, k, 0) - mt(L, pp, a, yb, ym, i, j, k, -h)) / h
            ex = deriv_formula(L, pp, a, yb, ym, i, j, k)
            ok = abs(fwd - ex) <= 1e-3 * (1 + abs(ex)) and abs(bwd - ex) <= 1e-3 * (1 + abs(ex))
            label = "hasDerivAt_moment (support boundary)" if k + 2 <= pp else "[info] k+2>p at boundary"
            if k + 2 <= pp:
                record(label, ok, f"k={k} p={pp} fwd={fwd} bwd={bwd} ex={ex}")
            else:
                print(f"[info] k={k}, p={pp} (k+2 > p) at the boundary: right slope {fwd:.6g}, left slope {bwd:.6g}"
                      f" -> {'kink' if abs(fwd - bwd) > 1e-3 * (1 + abs(fwd)) else 'smooth'}")
    # continuousOn_moment (k + 1 <= p): the moment is continuous across the support boundary
    for (k, pp) in ((0, 4), (2, 4), (3, 4), (4, 4)):
        jumps = []
        for eps in (1e-4, 1e-6, 1e-8):
            up = L.moment(pp, a, update(yb, 3, yb[3] + eps), ym, 0, k)
            dn = L.moment(pp, a, update(yb, 3, yb[3] - eps), ym, 0, k)
            jumps.append(abs(up - dn))
        if k + 1 <= pp:
            record("continuousOn_moment (across the support boundary)", jumps[-1] < 1e-5 * (1 + jumps[0] * 0),
                   f"k={k} p={pp} jumps={jumps}")
        else:
            print(f"[info] k={k}=p at the boundary: |m(y+eps)-m(y-eps)| = {jumps} -> "
                  f"{'jump (k+1<=p needed)' if jumps[-1] > 1e-6 else 'continuous'}")
else:
    print("[boundary] could not bracket a support boundary")


# ======================= Glue (hasDerivAt_glue) =======================
def is_pd_strict(Q):
    return np.linalg.eigvalsh(Q)[0] > 1e-12 * (1 + np.abs(Q).max())


def glue(p, k, i, Q):
    if not is_pd_strict(Q):
        return 0.0
    return np.linalg.det(Q) ** p * linv(Q)[i, i] ** k


def glue_deriv(p, k, i, Q, e):
    if not is_pd_strict(Q):
        return 0.0
    G = linv(Q)
    return np.linalg.det(Q) ** p * (p * G[i, i] ** k * np.dot(np.diag(G), e)
                                     - k * (G[i, i] ** (k - 1) if k >= 1 else 0.0) * np.dot(G[i, :] ** 2, e))


for trial in range(3000):
    n = int(rng.integers(1, 5))
    kind = rng.choice(["pd", "psd_sing", "indef"])
    X = rng.normal(size=(n, n))
    if kind == "pd":
        Q0 = X @ X.T + 0.1 * np.eye(n)
    elif kind == "psd_sing":
        X[:, 0] = 0
        Q0 = X @ X.T
    else:
        Q0 = (X + X.T) / 2
        if is_pd(Q0):
            Q0 = Q0 - 2 * np.linalg.eigvalsh(Q0)[-1] * np.eye(n)
    d1, d2 = rng.normal(size=n), rng.normal(size=n)
    k = int(rng.integers(0, 4))
    p = k + int(rng.integers(2, 4))
    i = int(rng.integers(0, n))
    gt = lambda t: glue(p, k, i, Q0 + np.diag(t * d1 + t * t * d2))
    h = 1e-5
    Dp = lambda hh: (gt(hh) - gt(0)) / hh
    Dm = lambda hh: (gt(0) - gt(-hh)) / hh
    fwd, bwd = 2 * Dp(h / 2) - Dp(h), 2 * Dm(h / 2) - Dm(h)  # Richardson: cancels the O(h) term
    ex = glue_deriv(p, k, i, Q0, d1)
    tol = 1e-4 * (1 + abs(ex)) * (1 + np.abs(Q0).max()) ** (n * p)
    record("hasDerivAt_glue (k+2<=p)", abs(fwd - ex) <= tol and abs(bwd - ex) <= tol, f"{kind} n={n} p={p} k={k}")
# p = k + 1 at a singular PSD Q0: the derivative fails to exist (docstring small case)
Q0 = np.zeros((1, 1))
g1 = lambda t: glue(1, 0, 0, Q0 + np.diag([t]))
print(f"[info] glue p=1,k=0 at Q0=0: right slope {(g1(1e-6) - g1(0)) / 1e-6:.3f}, left slope {(g1(0) - g1(-1e-6)) / 1e-6:.3f}"
      " (kink: k+2<=p is needed)")


# ======================= LinAlg =======================
for name, (n, edges) in GRAPHS.items():
    d = max(2, max([sum(1 for e in edges if u in e) for u in range(n)] + [0]))
    for trial in range(30):
        p = int(rng.choice([3, 5, 10]))
        pr = params(d, p)
        S = sorted(rng.choice(n, size=rng.integers(1, n + 1), replace=False).tolist()) if rng.uniform() < 0.3 else None
        L = Law(n, edges, S)
        y = rand_src(n, pr["s"])
        Bm = L.walkB(pr["a"], y)
        K = linv(Bm)
        ps = L.posSrc(y)
        record("walkB_symm", np.allclose(Bm, Bm.T))
        record("walkK_symm", np.allclose(K, K.T))
        for u in range(n):
            for w in range(n):
                if u != w and (u not in ps or w not in ps):
                    record("walkB_eq_zero_of_not_mem", Bm[u, w] == 0)
        record("walk_facts: K >= 0, K_ii >= 1", (K >= -1e-14).all() and (np.diag(K) >= 1 - 1e-12).all())
        if not ps:
            continue
        i = ps[rng.integers(0, len(ps))]
        c = float(rng.normal() * 3)
        # build C satisfying hfoc with random slack: (B x)_j = -c 1_{i=j} - slack_j on S+
        x = np.zeros(n)
        bvec = np.array([(-c if j == i else 0.0) - (rng.exponential() if j in ps else 0.0) for j in range(n)])
        idx = ps
        x[idx] = np.linalg.solve(Bm[np.ix_(idx, idx)], bvec[idx])
        C = np.array([x[l] * y[l] if l in ps else rng.normal() for l in range(n)])
        hf = all(sum(Bm[l, j] * (C[l] / y[l]) for l in ps) + (c if i == j else 0.0) <= 1e-9 for j in ps)
        concl = all(C[l] <= -(c * y[l] * K[l, i]) + 1e-9 * (1 + abs(C[l])) for l in ps)
        record("walk_dual", (not hf) or concl, f"{name} c={c}")
        # le_mulVec_of_mulVec_le with K B = 1, K >= 0
        xx = rng.normal(size=n)
        bb = Bm @ xx + rng.exponential(size=n)
        record("le_mulVec_of_mulVec_le", (xx <= K @ bb + 1e-9).all())


# ======================= FOC, F2, F3 at numerical maximizers =======================
def maximize(fun, n, cap, starts=4):
    best = None
    for s in range(starts):
        x0 = rng.uniform(0, cap, size=n) if s else np.full(n, cap)
        res = optimize.minimize(lambda y: -fun(y), x0, method="L-BFGS-B", bounds=[(0, cap)] * n,
                                options=dict(ftol=1e-15, gtol=1e-12, maxiter=2000))
        if best is None or -res.fun > best[0]:
            best = (-res.fun, res.x.copy())
    y = best[1]
    y[np.abs(y) < 1e-10] = 0.0
    y[np.abs(y - cap) < 1e-10] = cap
    return fun(y), y


f2_rows, f3_rows = [], []
PLAN = [("K1", (3,), ("zero", "cap"), None), ("K2", (3, 5), ("zero", "cap"), None),
        ("P3", (3, 5), ("cap", "rand"), None), ("K13", (4,), ("cap",), None), ("C4", (4,), ("cap",), [0]),
        ("K3", (3, 4, 6), ("zero", "cap", "rand"), None), ("paw", (4,), ("cap", "rand"), None),
        ("diamond", (4,), ("cap",), None), ("K4", (4,), ("cap",), [0])]
for name, plist, ymodes, ilist in PLAN:
    n, edges = GRAPHS[name]
    L = Law(n, edges)
    d = max(2, max([sum(1 for e in edges if u in e) for u in range(n)] + [0]))
    for p in plist:
        pr = params(d, p)
        a, cap = pr["a"], pr["s"]
        for ymode in ymodes:
            ym = {"zero": np.zeros(n), "cap": np.full(n, cap), "rand": rng.uniform(0, cap, size=n)}[ymode]
            if L.lawE(p, a, np.full(n, cap), ym, lambda s, Gp, Gm: 1.0)[1] <= 0:
                continue
            for i in (range(n) if ilist is None else ilist):
                # B0: sup over the cube of the first mean E h_i (the cap the proof uses)
                B0, yB = maximize(lambda y: L.moment(p, a, y, ym, i, 1), n, cap)
                for k in range(1, p - 1):
                    mk, ys = maximize(lambda y: L.moment(p, a, y, ym, i, k), n, cap)
                    bound = ((p * B0 - k) / (p - k)) ** k
                    record("source_moments (F2, B0 = sup of the mean)", mk <= bound * (1 + 1e-9),
                           f"{name} p={p} i={i} k={k} m={mk} bound={bound}")
                    f2_rows.append((name, p, ymode, i, k, mk, bound))
                    ps = L.posSrc(ys)
                    if ys[i] > 0:
                        # FOC at the maximizer
                        Bm = L.walkB(a, ys)
                        C = {l: L.momC(p, a, ys, ym, k, i, l) for l in ps}
                        for j in ps:
                            val = sum(Bm[l, j] * (C[l] / ys[l]) for l in ps) + (k * mk * ys[i] ** k if i == j else 0.0)
                            scale = 1 + sum(abs(Bm[l, j] * C[l] / ys[l]) for l in ps) + k * mk * ys[i] ** k
                            record("foc_of_max (at numerical maximizer)", val <= 1e-6 * scale,
                                   f"{name} p={p} i={i} k={k} j={j} val={val:.3g} y_j={ys[j]:.4f}")
                        # the C_i inequality used by F2 (walk_dual + K_ii >= 1)
                        K = linv(Bm)
                        mu = L.moment(p, a, ys, ym, i, 1)
                        Mk1 = L.moment(p, a, ys, ym, i, k + 1)
                        record("F2 step: (p-k)E h^{k+1} - p m mu <= -k m K_ii",
                               (p - k) * Mk1 - p * mk * mu <= -k * mk * K[i, i] + 1e-6 * (1 + p * mk * mu))
                        record("F2 step: m <= ((p mu - k)/(p-k))^k at the maximizer",
                               mk <= ((p * mu - k) / (p - k)) ** k * (1 + 1e-6))
                # F3 at the maximizer of the first mean
                ps = L.posSrc(yB)
                if yB[i] > 0:
                    K = linv(L.walkB(a, yB))
                    E = lambda f: L.lawE(p, a, yB, ym, f)[0]
                    g = lambda Gp, u, w: L.greenP(yB, Gp, u, w)
                    for l in range(n):
                        lhs = p * (E(lambda s, Gp, Gm: g(Gp, i, i) * g(Gp, l, l))
                                   - E(lambda s, Gp, Gm: g(Gp, i, i)) * E(lambda s, Gp, Gm: g(Gp, l, l))) \
                            - E(lambda s, Gp, Gm: g(Gp, i, l) ** 2)
                        rhs = -(B0 * yB[i] * yB[l] * K[i, l])
                        record("source_covariance (F3, at the max of the mean)", lhs <= rhs + 1e-6 * (1 + abs(rhs)),
                               f"{name} p={p} v={i} i={l} lhs={lhs} rhs={rhs}")
                        f3_rows.append((name, p, ymode, i, l, B0, lhs, rhs))
                    var = E(lambda s, Gp, Gm: Gp[i, i] ** 2) - B0 ** 2
                    record("[paper] (p-1)Var(h_v) <= r(r-1) at the max", (p - 1) * var <= B0 * (B0 - 1) + 1e-8)

print("\n== SourceMax ==")
for k, (tot, bad, info) in fails.items():
    print(f"{k:58s} trials={tot:5d} fails={bad} {info}")
print("\nF2 samples (graph, p, y-, i, k, sup m_k, ((pB0-k)/(p-k))^k):")
for row in f2_rows:
    if row[5] > 1 + 1e-9:
        print("  ", row[0], row[1], row[2], row[3], row[4], f"{row[5]:.6f}", f"{row[6]:.6f}")
print("F3 samples with max mean > 1 (graph, p, y-, v, i, mean, lhs, rhs):")
for row in f3_rows:
    if row[5] > 1 + 1e-9:
        print("  ", row[0], row[1], row[2], row[3], row[4], f"{row[5]:.6f}", f"{row[6]:.4e}", f"{row[7]:.4e}")
