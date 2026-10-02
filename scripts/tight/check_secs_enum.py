#!/usr/bin/env python3
"""Exact enumeration checks of the Section A-C statements, in the Lean (normalized) formulation.

Objects exactly as in BiluLinial/Tight/{Defs,Ctx,Insertion,Contact/Defs,SecA/Defs,SecC/Defs}.lean:
  precN(tau,y,sig): diag D_u (u in S) / 1 (u not in S); off-diag tau a sqrt(y_u y_w) sig_uw on S-edges;
  D_u = 1 + sum_{j in N_S(u)} c(a^2 y_u y_j),  c(x) = (sqrt(1+4x)-1)/2;
  wt = 1{precN(+1,yp), precN(-1,ym) PD} (det det)^p;  lawE = sum wt f / sum wt;
  greenP = sqrt(y_i) precN^{-1}_ij sqrt(y_j);  hN_i = precN^{-1}_ii;
  precCore = precN with row/col v replaced by the identity;  wtCore, coreE likewise;
  coreGreen = sqrt(y) precCore^{-1} sqrt(y);  rootMat = a^2 y_v / D_v coreGreen[N,N];
  shiftP(z) = sqrt(y) (precN + z Y_S)^{-1} sqrt(y);  hzN(z)_i = (precN + z Y_S)^{-1}_ii;
  coreShift(z) = sqrt(y) (precCore + z Y_{S-v})^{-1} sqrt(y);  rootMzG = a^2 y_v/D_v coreShift[N,N].
Parameters: aOf, sOf from (d, p) as in Tight/Defs.lean (d = a degree bound, may exceed max degree).

Run: /tmp/tight-venv/bin/python scripts/tight/check_secs_enum.py
"""
import itertools
import numpy as np

rng = np.random.default_rng(20261001)


def params(d, p):
    q = d - 1.0
    De = 4.0 / p
    R2 = 4 * q + De
    a = 1 / np.sqrt(R2)
    eta = (np.sqrt(De ** 2 + 4 * q * De) - De) / (2 * q)
    ts = (1 - eta) / q
    s = (1 + q * ts) / (1 - ts)
    r = 1 + eta / 2
    return a, s, r


def cR(x):
    return (np.sqrt(1 + 4 * x) - 1) / 2


class Inst:
    def __init__(self, n, edges, S, yp, ym, d, p):
        self.n, self.S, self.d, self.p = n, sorted(S), d, p
        self.a, self.s, self.r = params(d, p)
        self.adj = np.zeros((n, n), bool)
        for i, j in edges:
            self.adj[i, j] = self.adj[j, i] = True
        self.Sedges = [(i, j) for (i, j) in edges if i in S and j in S]
        self.yp, self.ym = np.array(yp, float), np.array(ym, float)
        self.sigs = list(itertools.product([1.0, -1.0], repeat=len(self.Sedges)))

    def nb(self, u):
        return [j for j in self.S if self.adj[u, j]]

    def D(self, y, u):
        if u not in self.S:
            return 1.0
        return 1 + sum(cR(self.a ** 2 * y[u] * y[j]) for j in self.nb(u))

    def sgnmat(self, sig):
        M = np.zeros((self.n, self.n))
        for k, (i, j) in enumerate(self.Sedges):
            M[i, j] = M[j, i] = sig[k]
        return M

    def precN(self, tau, y, sig):
        n = self.n
        P = np.eye(n)
        for u in self.S:
            P[u, u] = self.D(y, u)
        sq = np.sqrt(y)
        M = self.sgnmat(sig)
        P += tau * self.a * np.outer(sq, sq) * M
        return P

    def precCore(self, tau, y, sig, v):
        P = self.precN(tau, y, sig)
        P[v, :] = 0
        P[:, v] = 0
        P[v, v] = 1
        return P

    def srcDiag(self, y, T):
        return np.diag([y[k] if k in T else 0.0 for k in range(self.n)])

    @staticmethod
    def pd(P):
        return np.linalg.eigvalsh(P)[0] > 0

    def wt(self, sig):
        Pp, Pm = self.precN(1, self.yp, sig), self.precN(-1, self.ym, sig)
        if self.pd(Pp) and self.pd(Pm):
            return (np.linalg.det(Pp) * np.linalg.det(Pm)) ** self.p
        return 0.0

    def wtCore(self, sig, v):
        Pp, Pm = self.precCore(1, self.yp, sig, v), self.precCore(-1, self.ym, sig, v)
        if self.pd(Pp) and self.pd(Pm):
            return (np.linalg.det(Pp) * np.linalg.det(Pm)) ** self.p
        return 0.0

    def phys(self, Minv, y):
        sq = np.sqrt(y)
        return np.outer(sq, sq) * Minv

    def rootSigns(self, sig, v):
        M = self.sgnmat(sig)
        return np.array([M[v, i] for i in self.nb(v)])


def clip(t):
    return max(t, 0.0)


def qf(M, x):
    return float(x @ M @ x)


def star_vectors(m):
    return [np.array(e) for e in itertools.product([1.0, -1.0], repeat=m)]


def check_instance(name, I, v, z=0.3, report=None):
    p, a = I.p, I.a
    N = I.nb(v)
    m = len(N)
    xis = star_vectors(m)
    res = {}
    W = np.array([I.wt(s) for s in I.sigs])
    Wc = np.array([I.wtCore(s, v) for s in I.sigs])
    Z, Zc = W.sum(), Wc.sum()
    if Z <= 0 or Zc <= 0:
        print(f"{name}: law empty (Z={Z}, Zc={Zc}); skipped")
        return
    Dp, Dm = I.D(I.yp, v), I.D(I.ym, v)
    # per-signing objects
    data = []
    for s in I.sigs:
        Pp, Pm = I.precN(1, I.yp, s), I.precN(-1, I.ym, s)
        Cp, Cm = I.precCore(1, I.yp, s, v), I.precCore(-1, I.ym, s, v)
        ok = I.pd(Pp) and I.pd(Pm)
        okc = I.pd(Cp) and I.pd(Cm)
        Pip = np.linalg.inv(Pp) if abs(np.linalg.det(Pp)) > 1e-300 else np.zeros_like(Pp)
        Pim = np.linalg.inv(Pm) if abs(np.linalg.det(Pm)) > 1e-300 else np.zeros_like(Pm)
        Cip, Cim = np.linalg.inv(Cp), np.linalg.inv(Cm)
        Gp, Gm = I.phys(Pip, I.yp), I.phys(Pim, I.ym)
        CGp, CGm = I.phys(Cip, I.yp), I.phys(Cim, I.ym)
        A = a ** 2 * I.yp[v] / Dp * CGp[np.ix_(N, N)]
        B = a ** 2 * I.ym[v] / Dm * CGm[np.ix_(N, N)]
        Ys = lambda y: I.srcDiag(y, I.S)
        Yk = lambda y: I.srcDiag(y, [k for k in I.S if k != v])
        Xp = I.phys(np.linalg.inv(Pp + z * Ys(I.yp)), I.yp)
        Xm = I.phys(np.linalg.inv(Pm + z * Ys(I.ym)), I.ym)
        hzp = np.diag(np.linalg.inv(Pp + z * Ys(I.yp)))
        hzm = np.diag(np.linalg.inv(Pm + z * Ys(I.ym)))
        CSp = I.phys(np.linalg.inv(Cp + z * Yk(I.yp)), I.yp)
        CSm = I.phys(np.linalg.inv(Cm + z * Yk(I.ym)), I.ym)
        Mz = a ** 2 * I.yp[v] / Dp * CSp[np.ix_(N, N)]
        Mzm = a ** 2 * I.ym[v] / Dm * CSm[np.ix_(N, N)]
        xi = I.rootSigns(s, v)
        data.append(dict(ok=ok, okc=okc, Pip=Pip, Pim=Pim, Gp=Gp, Gm=Gm, CGp=CGp, CGm=CGm, A=A, B=B,
                         Xp=Xp, Xm=Xm, hzp=hzp, hzm=hzm, CSp=CSp, CSm=CSm, Mz=Mz, Mzm=Mzm, xi=xi))
    E = lambda f: float(sum(W[k] * f(data[k]) for k in range(len(I.sigs)) if W[k] > 0) / Z)
    Ec = lambda f: float(sum(Wc[k] * f(data[k]) for k in range(len(I.sigs)) if Wc[k] > 0) / Zc)
    Phi = lambda A, B, x: clip(1 - qf(A, x)) ** p * clip(1 - qf(B, x)) ** p
    Rad = lambda g: float(np.mean([g(x) for x in xis])) if m > 0 else g(np.zeros(0))
    FH = Ec(lambda D_: Rad(lambda x: Phi(D_["A"], D_["B"], x)))
    # --- INS: E_H[g(sig, xi_sig)] = E_core R[Phi g] / F_H, g core-measurable
    def g(D_, x):
        return np.sum(D_["A"]) * (x[0] if m else 1.0) + qf(D_["B"], x) + np.trace(D_["A"]) ** 2
    lhs = E(lambda D_: g(D_, D_["xi"]))
    rhs = Ec(lambda D_: Rad(lambda x: Phi(D_["A"], D_["B"], x) * g(D_, x))) / FH
    res["INS"] = abs(lhs - rhs) / (1 + abs(lhs))
    # --- C3 (schur_C3, plus and minus)
    f1 = lambda A, B, x: (np.trace(A) - qf(A, x)) * clip(1 - qf(A, x)) ** (p - 1) * clip(1 - qf(B, x)) ** p
    lhsP = Ec(lambda D_: Rad(lambda x: f1(D_["A"], D_["B"], x))) / FH
    rhsP = 1 - Dp * E(lambda D_: D_["Pip"][v, v]) + a ** 2 * sum(
        E(lambda D_, i=i: D_["Gp"][v, v] * D_["Gp"][i, i] - D_["Gp"][v, i] ** 2) for i in N)
    lhsM = Ec(lambda D_: Rad(lambda x: f1(D_["B"], D_["A"], x))) / FH
    rhsM = 1 - Dm * E(lambda D_: D_["Pim"][v, v]) + a ** 2 * sum(
        E(lambda D_, i=i: D_["Gm"][v, v] * D_["Gm"][i, i] - D_["Gm"][v, i] ** 2) for i in N)
    res["C3"] = max(abs(lhsP - rhsP), abs(lhsM - rhsM))
    # --- pointwise statements on supported signings
    wF1 = wRow = wFrob = 0.0
    c5 = dict(hzpos=np.inf, hzle=-np.inf, cs_le_sh=-np.inf, cg_le_g=-np.inf, cs_le_cg=-np.inf,
              C5c=-np.inf, C5d=0.0, C5e=-np.inf, C5f=-np.inf, S1sign=np.inf, ward=-np.inf)
    for k, D_ in enumerate(data):
        if not D_["ok"]:
            continue
        A, B, xi, Gp, Gm = D_["A"], D_["B"], D_["xi"], D_["Gp"], D_["Gm"]
        al, be = 1 - qf(A, xi), 1 - qf(B, xi)
        tp, tm = Dp * D_["Pip"][v, v], Dm * D_["Pim"][v, v]
        # root_F1
        errs = [abs(tp - 1 / al), abs(tm - 1 / be)]
        for jj, j in enumerate(N):
            errs.append(abs(Gp[v, j] - (-(A @ xi)[jj] / (a * al))))
            errs.append(abs(Gm[v, j] - (-(B @ xi)[jj] / (-a * be))))
            for ii, i in enumerate(N):
                errs.append(abs(Gp[v, v] * Gp[i, j] - (A[ii, jj] / (a * a * al) + Gp[v, i] * Gp[v, j])))
                errs.append(abs(Gm[v, v] * Gm[i, j] - (B[ii, jj] / (a * a * be) + Gm[v, i] * Gm[v, j])))
        wF1 = max(wF1, max(errs) if errs else 0.0, 0.0 if al > 0 and be > 0 else np.inf)
        # rowNum_eq
        F = (p - 1) * qf(A @ A, xi) * clip(al) ** (p - 2) * clip(be) ** p + \
            p * qf(A @ B, xi) * clip(al) ** (p - 1) * clip(be) ** (p - 1)
        Rv = (p - 1) * sum(Gp[v, j] ** 2 for j in N) - p * sum(Gp[v, j] * Gm[v, j] for j in N)
        wRow = max(wRow, abs(F - a * a * Phi(A, B, xi) * Rv) / (1 + abs(F)))
        # frob_root_le (margin: rhs - lhs >= 0)
        lhsF = a ** 4 * Gp[v, v] ** 2 * sum(Gp[i, j] ** 2 for i in N for j in N)
        rhsF = 2 * tp ** 2 * np.trace(A @ A) + 2 * (a * a * sum(Gp[v, j] ** 2 for j in N)) ** 2
        wFrob = min(wFrob, rhsF - lhsF) if k else rhsF - lhsF
        # C5a/b
        c5["hzpos"] = min(c5["hzpos"], D_["hzp"].min(), D_["hzm"].min())
        c5["hzle"] = max(c5["hzle"], (D_["hzp"] - np.diag(D_["Pip"])).max(), (D_["hzm"] - np.diag(D_["Pim"])).max())
        for i in range(I.n):
            if i == v:
                continue
            c5["cs_le_sh"] = max(c5["cs_le_sh"], D_["CSp"][i, i] - D_["Xp"][i, i], D_["CSm"][i, i] - D_["Xm"][i, i])
            c5["cg_le_g"] = max(c5["cg_le_g"], D_["CGp"][i, i] - Gp[i, i], D_["CGm"][i, i] - Gm[i, i])
        for i in range(I.n):
            c5["cs_le_cg"] = max(c5["cs_le_cg"], D_["CSp"][i, i] - D_["CGp"][i, i], D_["CSm"][i, i] - D_["CGm"][i, i])
        # C5c (sum_shift_sub_core_le), both branches
        for (X, CS, Pinv, hz, Dv) in ((D_["Xp"], D_["CSp"], D_["Pip"], D_["hzp"], Dp),
                                      (D_["Xm"], D_["CSm"], D_["Pim"], D_["hzm"], Dm)):
            l = sum(X[i, i] - CS[i, i] for i in N)
            rr = Dv * (Pinv[v, v] - hz[v]) / z
            c5["C5c"] = max(c5["C5c"], l - rr)
        # C5d (inv_hzN_root), both branches
        c5["C5d"] = max(c5["C5d"], abs(1 / D_["hzp"][v] - (Dp * (1 - qf(D_["Mz"], xi)) + z * I.yp[v])),
                        abs(1 / D_["hzm"][v] - (Dm * (1 - qf(D_["Mzm"], xi)) + z * I.ym[v])))
        # C5e (sum_coreShift_mul_coreGreen_le), nu = + and nu = -
        for (CG, CS) in ((D_["CGp"], D_["CSp"]), (D_["CGm"], D_["CSm"])):
            l = sum(D_["CSp"][i, j] * CG[j, i] for i in N for j in N)
            rr = 2 / z * (sum(D_["CGp"][i, i] - D_["CSp"][i, i] for i in N) + sum(CG[i, i] - CS[i, i] for i in N))
            c5["C5e"] = max(c5["C5e"], l - rr)
        # C5f (qForm_Mz_le)
        Mz = D_["Mz"]
        bound = a ** 2 * I.yp[v] / (Dp * z)
        l1 = qf(A @ Mz @ A, xi) * tp ** 2 - bound * a * a * sum(Gp[v, i] ** 2 for i in N)
        l2 = qf(B @ Mz @ B, xi) * tm ** 2 - bound * a * a * sum(Gm[v, i] ** 2 for i in N)
        c5["C5f"] = max(c5["C5f"], l1, l2)
        c5["S1sign"] = min(c5["S1sign"], min(Gp[i, i] - D_["Xp"][i, i] for i in range(I.n)),
                           min(Gm[i, i] - D_["Xm"][i, i] for i in range(I.n)))
        # SecB.ward_diag: (X X)_ii <= (G_ii - X_ii)/h, i in S (physical X = sqrt(y)(P+hY)^-1 sqrt(y))
        for (X, Gx) in ((D_["Xp"], Gp), (D_["Xm"], Gm)):
            XX = X @ X
            c5["ward"] = max(c5.get("ward", -np.inf),
                             max(XX[i, i] - (Gx[i, i] - X[i, i]) / z for i in I.S))
    res.update(F1=wF1, rowNum=wRow, frob_margin=wFrob)
    res.update(c5)
    # SecC.shift_mat_facts on the core support: A, B, M, N >= 0, M <= A, N <= B, M, N <= (s a^2/z) I
    m0 = I.s * a * a / z
    viol = 0.0
    for D_ in data:
        if not D_["okc"] or m == 0:
            continue
        A, B, Mz, Mzm = D_["A"], D_["B"], D_["Mz"], D_["Mzm"]
        sym = lambda X: (X + X.T) / 2
        for X in (A, B, Mz, Mzm, A - Mz, B - Mzm, m0 * np.eye(m) - Mz, m0 * np.eye(m) - Mzm):
            viol = max(viol, -np.linalg.eigvalsh(sym(X))[0])
    res["shiftmat"] = viol
    # shiftQ_eq: (p-1) E X1 + p E X2 = a^2 Q
    def X1(D_):
        Mz = D_["Mz"]
        return np.trace(Mz @ Mz) * (Dp * D_["Pip"][v, v]) ** 2
    def X2(D_):
        return np.trace(D_["Mz"] @ D_["Mzm"]) * (Dp * D_["Pip"][v, v]) * (Dm * D_["Pim"][v, v])
    Qbl = a ** 2 * E(lambda D_: (p - 1) * D_["Gp"][v, v] ** 2 * sum(D_["CSp"][i, j] ** 2 for i in N for j in N)
                     + p * D_["Gp"][v, v] * D_["Gm"][v, v] * sum(D_["CSp"][i, j] * D_["CSm"][i, j] for i in N for j in N))
    res["shiftQ"] = abs((p - 1) * E(X1) + p * E(X2) - a * a * Qbl) / (1 + abs(Qbl))
    # DR1 identity in the Lean form (rowBP uses D_w * meanPlus)
    Sp = sum(E(lambda D_, i=i: D_["Gp"][v, i] ** 2) for i in N)
    Sm = sum(E(lambda D_, i=i: D_["Gm"][v, i] ** 2) for i in N)
    T = sum(E(lambda D_, i=i: D_["Gp"][v, i] * D_["Gm"][v, i]) for i in N)
    Dif = sum(E(lambda D_, i=i: (D_["Gp"][v, i] - D_["Gm"][v, i]) ** 2) for i in N)
    BP = 1 - Dp * E(lambda D_: D_["Pip"][v, v]) + a * a * sum(E(lambda D_, i=i: D_["Gp"][v, v] * D_["Gp"][i, i]) for i in N)
    BM = 1 - Dm * E(lambda D_: D_["Pim"][v, v]) + a * a * sum(E(lambda D_, i=i: D_["Gm"][v, v] * D_["Gm"][i, i]) for i in N)
    sgnE = lambda i, G: E(lambda D_: I.sgnmat(I.sigs[[id(x) for x in data].index(id(D_))])[v, i] * D_[G][v, i])
    R1p = R1m = 0.0
    for i in N:
        ex = sgnE(i, "Gp")
        ez = sgnE(i, "Gm")
        d1x = E(lambda D_: -a * D_["Gp"][v, v] * D_["Gp"][i, i] + (2 * p - 1) * a * D_["Gp"][v, i] ** 2
                - 2 * p * a * D_["Gp"][v, i] * D_["Gm"][v, i])
        d1z = E(lambda D_: a * D_["Gm"][v, v] * D_["Gm"][i, i] - (2 * p - 1) * a * D_["Gm"][v, i] ** 2
                + 2 * p * a * D_["Gp"][v, i] * D_["Gm"][v, i])
        R1p += ex - d1x
        R1m += ez - d1z
    e1 = (2 * p - 1) * a * a * Sp - 2 * p * a * a * T - BP + a * R1p
    e2 = (2 * p - 1) * a * a * Sm - 2 * p * a * a * T - BM - a * R1m
    lhs_dr1 = (2 * p - 1) * a * a * Dif
    rhs_dr1 = BP + BM + 2 * a * a * T + (-a * R1p + a * R1m)
    res["RE_exact"] = max(abs(e1), abs(e2))
    res["DR1_id"] = abs(lhs_dr1 - rhs_dr1) / (1 + abs(lhs_dr1))
    res["E1row_ratio"] = max([abs(R1p), abs(R1m)]) / (p ** 3 * a ** 3 * max(1, m)) if m else 0.0
    if report is not None:
        report.append((name, res))
    return res


def main():
    G = {
        "K4": (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
        "K33": (6, [(i, j) for i in range(3) for j in range(3, 6)]),
        "star+": (6, [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5)]),
        "P4": (4, [(0, 1), (1, 2), (2, 3)]),
        "K2": (2, [(0, 1)]),
        "C5": (5, [(i, (i + 1) % 5) for i in range(5)]),
    }
    report = []
    cases = []
    for name, (n, edges) in G.items():
        dmax = max(sum(1 for e in edges if u in e) for u in range(n))
        for d in sorted({max(dmax, 3), max(dmax, 3) + 3}):
            for p in (3, 5, 12):
                a, s, r = params(d, p)
                for variant in ("random", "zero_root_plus", "zero_nb", "S_sub", "S_single"):
                    yp = rng.uniform(0, s, n)
                    ym = rng.uniform(0, s, n)
                    S = list(range(n))
                    v = 0
                    if variant == "zero_root_plus":
                        yp[v] = 0.0
                    if variant == "zero_nb":
                        yp[1] = 0.0
                        ym[min(2, n - 1)] = 0.0
                    if variant == "S_sub":
                        S = list(range(n - 1)) if n > 2 else [0, 1]
                    if variant == "S_single":
                        S = [v]
                    cases.append((f"{name} d={d} p={p} {variant}", Inst(n, edges, S, yp, ym, d, p), v))
    for (nm, I, v) in cases:
        check_instance(nm, I, v, z=0.37, report=report)
    keys = ["INS", "C3", "F1", "rowNum", "frob_margin", "hzpos", "hzle", "cs_le_sh", "cg_le_g",
            "cs_le_cg", "C5c", "C5d", "C5e", "C5f", "S1sign", "ward", "shiftQ", "shiftmat", "RE_exact", "DR1_id",
            "E1row_ratio"]
    agg = {k: [] for k in keys}
    for nm, res in report:
        for k in keys:
            agg[k].append((res[k], nm))
    print(f"{len(report)} instances (graphs K4, K33, star+, P4, K2, C5; p in 3,5,12; zero sources; S proper; S={{v}})")
    desc = {
        "INS": "max rel |E_H g - E_core R[Phi g]/F_H|            (A-INS, want 0)",
        "C3": "max |(C3) lhs - rhs| both branches               (A-C3, want 0)",
        "F1": "max error of root_F1 identities                  (want 0)",
        "rowNum": "max rel |F - a^2 Phi R_v|                         (rowNum_eq, want 0)",
        "frob_margin": "min (rhs - lhs) of frob_root_le                   (want >= 0)",
        "hzpos": "min hzN on support                               (hzN_pos, want > 0)",
        "hzle": "max (hzN - hN)                                   (hzN_le_hN, want <= 0)",
        "cs_le_sh": "max (coreShift_ii - shiftP_ii), i != v           (want <= 0)",
        "cg_le_g": "max (coreGreen_ii - greenP_ii), i != v           (want <= 0)",
        "cs_le_cg": "max (coreShift_ii - coreGreen_ii)               (want <= 0)",
        "C5c": "max (lhs - rhs) sum_shift_sub_core_le            (want <= 0)",
        "C5d": "max |inv_hzN_root lhs - rhs|                      (want 0)",
        "C5e": "max (lhs - rhs) sum_coreShift_mul_coreGreen_le   (want <= 0)",
        "C5f": "max (lhs - rhs) qForm_Mz_le both conjuncts       (want <= 0)",
        "S1sign": "min (G_ii - X_ii) pointwise                       (S1 lower bound, want >= 0)",
        "shiftQ": "max rel |(p-1)E X1 + p E X2 - a^2 Q|             (shiftQ_eq, want 0)",
        "ward": "max (XX_ii - (G_ii - X_ii)/h), i in S             (ward_diag, want <= 0)",
        "shiftmat": "max PSD violation in shift_mat_facts (core supp.) (want <= 0)",
        "RE_exact": "max |row_eq_exact residual|                       (proved; want 0)",
        "DR1_id": "max rel DR1 identity residual (Lean form)         (want 0)",
        "E1row_ratio": "max |E[sig x]-E D1 x| / (p^3 a^3 |N|)            (TB.E1row size, info)",
    }
    for k in keys:
        vals = [x for x, _ in agg[k] if np.isfinite(x)]
        if k in ("frob_margin", "hzpos", "S1sign"):
            worst = min(agg[k], key=lambda t: t[0])
        else:
            worst = max(agg[k], key=lambda t: t[0])
        print(f"{desc[k]}: {worst[0]: .3e}   [{worst[1]}]  (n={len(vals)})")


if __name__ == "__main__":
    main()
