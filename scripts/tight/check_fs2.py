"""Numerical checks of the node FS2 (exact Schur identity, source l.1686-1695) and of the
deterministic steps of FS1/FS4 (Contact/Leaves3.lean), with the Lean definitions:

  precN[u,w]   = (u in S ? D_u : 1) on the diagonal, tau*a*sqrt(y_u y_w)*sigma_uw on S-edges, else 0
  srcDiag      = diag(k in S ? y_k : 0)
  X = shiftP   = Y^{1/2} (precN + h srcDiag(S))^{-1} Y^{1/2}
  C_i = Cb     = Y^{1/2} (precCore_i + h srcDiag(S - i))^{-1} Y^{1/2},
                 precCore_i = precN with row/column i replaced by e_i
  maskF Xe Xn f j i = Xe_ii (Xe diag f Xn)_ji - Xe_ji (Xe diag f Xn)_ii
  tDir_jl = 1_{l in N} C^e_jl u_l C^+_ll,  tCav_jl = sum_{k in N - {i,l}} C^e_jk u_k C^+_kl

Checks (S a proper subset of V, sources with zeros, random signings, both branches):
  (P1) pure Schur identities for a general invertible M (not symmetric) and M' = M with row and
       column i replaced by e_i:  N_ii N_jk - N_ji N_ik = N_ii N'_jk  and
       N_ki = -N_ii sum_{l != i} N'_kl M_li   (j, k != i; N = M^{-1}, N' = M'^{-1});
  (FS2) maskF(Xe, X+, u) j i = -a Xe_ii X+_ii ((tDir xi)_j + (tCav xi)_j) for i in N, j in J_i;
  (FS2') the source form  -a Xe_ii X+_ii sum_{k in N-i, l ~ i} C^e_jk u_k C^+_kl xi_l;
  (B1) sum_{j in J} (sum_k C_jk w_k)^2 <= h^{-2} |w|^2 for w supported on S - i;
  (B2) X_ii C_kl = X_ii X_kl - X_ki X_il (k, l != i), 0 <= X_ii C_ll <= X_ii X_ll;
  (B3) (X^2)_ii <= X_ii / h;  X_kl^2 <= X_kk X_ll;
  (B4) 4 u^T (K+ - M+) b+ = (a^2/d) sum_{i in N} X_ii^2 sum_{l in J_i} sum_{k in N - l} X_kl^2;
       4 u^T (K+ - M+) u = (1/d) sum_{i != k in N} X_ki^2;
  (B5) the FS1 cavity chain: sum_i Xe_ii^2 X+_ii^2 tr L_cav,i
         <= 2 D^2 h^{-2} (Y1/a^2 + h^{-1} D Y2), Y1 = 4u^T(K-M)b, Y2 = 4u^T(K-M)u, D = max diag;
  (B6) the FS1 direct chain: Xe_ii^2 X+_ii^2 tr L_dir,i
         <= 2 D^6 (1/d) sum_{l in J_i cap N} ((Xe^2)_ll + (Xe^2)_ii), D >= max(X+_ll, Xe_ll, ...);
  (FS4) |dOmP_ij| <= sqrt(OmP) 2a |G_vi||G_vj|,  |dOmM_ij| <= sqrt(OmM) g_ij with
        g_ij = a (sqrt(G+_vv G-_jj) |G-_vi| + sqrt(G-_vv G+_jj) |G+_vi|).
Run: /tmp/tight-venv/bin/python scripts/tight/check_fs2.py
"""
import math
import random

import numpy as np

rng = np.random.default_rng(7)
random.seed(7)


def croot(x):
    return (math.sqrt(1 + 4 * x) - 1) / 2


def check_pure(trials=2000):
    worst = 0.0
    for _ in range(trials):
        n = rng.integers(2, 7)
        M = rng.normal(size=(n, n))
        i = int(rng.integers(0, n))
        Mp = M.copy()
        Mp[i, :] = 0
        Mp[:, i] = 0
        Mp[i, i] = 1
        if abs(np.linalg.det(M)) < 1e-3 or abs(np.linalg.det(Mp)) < 1e-3:
            continue
        N = np.linalg.inv(M)
        Np = np.linalg.inv(Mp)
        for j in range(n):
            for k in range(n):
                if j == i or k == i:
                    continue
                lhs = N[i, i] * N[j, k] - N[j, i] * N[i, k]
                rhs = N[i, i] * Np[j, k]
                worst = max(worst, abs(lhs - rhs) / (1 + abs(lhs)))
        for k in range(n):
            if k == i:
                continue
            rhs = -N[i, i] * sum(Np[k, l] * M[l, i] for l in range(n) if l != i)
            worst = max(worst, abs(N[k, i] - rhs) / (1 + abs(N[k, i])))
    return worst


def build(n, E, S, y, a, tau, sig):
    adj = np.zeros((n, n), dtype=bool)
    for (u, w) in E:
        adj[u, w] = adj[w, u] = True

    def nb(u):
        return [w for w in S if adj[u, w]]

    D = np.array([1 + sum(croot(a * a * y[u] * y[w]) for w in nb(u)) for u in range(n)])
    P = np.zeros((n, n))
    for u in range(n):
        for w in range(n):
            if u == w:
                P[u, w] = D[u] if u in S else 1.0
            elif u in S and w in S and adj[u, w]:
                P[u, w] = tau * a * math.sqrt(y[u] * y[w]) * sig[min(u, w), max(u, w)]
    return adj, nb, P


def phys(y, Minv):
    sq = np.sqrt(y)
    return sq[:, None] * Minv * sq[None, :]


def srcdiag(y, S, n):
    return np.diag([y[k] if k in S else 0.0 for k in range(n)])


def core(P, i):
    Pc = P.copy()
    Pc[i, :] = 0
    Pc[:, i] = 0
    Pc[i, i] = 1
    return Pc


def maskF(Xe, Xn, f, j, i):
    U = Xe @ np.diag(f) @ Xn
    return Xe[i, i] * U[j, i] - Xe[j, i] * U[i, i]


def run_case(n, E, S, v, yp, ym, a, h, sig, stats):
    adj, nb, Pp = build(n, E, S, yp, a, 1.0, sig)
    _, _, Pm = build(n, E, S, ym, a, -1.0, sig)
    if np.linalg.eigvalsh(Pp).min() <= 1e-9 or np.linalg.eigvalsh(Pm).min() <= 1e-9:
        stats["skip"] += 1
        return
    stats["cases"] += 1
    d = max(1, max(len([w for w in range(n) if adj[u, w]]) for u in range(n)))
    N = nb(v)
    u = np.array([1 / math.sqrt(d) if k in N else 0.0 for k in range(n)])
    Gp = phys(yp, np.linalg.inv(Pp))
    Gm = phys(ym, np.linalg.inv(Pm))
    Xp = phys(yp, np.linalg.inv(Pp + h * srcdiag(yp, S, n)))
    Xm = phys(ym, np.linalg.inv(Pm + h * srcdiag(ym, S, n)))

    def Cmat(P, y, i):
        Sm = [k for k in S if k != i]
        return phys(y, np.linalg.inv(core(P, i) + h * srcdiag(y, Sm, n)))

    # (B4) identities
    Kp = Xp * Xp / 4
    Mp = np.diag(np.diag(Xp) ** 2 / 4)
    A = np.array([[1.0 if (k in S and l in S and adj[k, l]) else 0.0 for l in range(n)] for k in range(n)])
    bp = 4 * a * a * A @ (Mp @ u)
    Y1 = 4 * u @ (Kp - Mp) @ bp
    Y2 = 4 * u @ (Kp - Mp) @ u
    Y1r = a * a / d * sum(Xp[i, i] ** 2 * sum(Xp[k, l] ** 2 for l in nb(i) for k in N if k != l) for i in N)
    Y2r = 1 / d * sum(Xp[k, i] ** 2 for i in N for k in N if k != i)
    stats["B4"] = max(stats["B4"], abs(Y1 - Y1r) / (1 + abs(Y1)), abs(Y2 - Y2r) / (1 + abs(Y2)))
    for X in (Xp, Xm):
        X2 = X @ X
        for k in range(n):
            stats["B3"] = max(stats["B3"], X2[k, k] - X[k, k] / h)
            for l in range(n):
                stats["B3"] = max(stats["B3"], X[k, l] ** 2 - X[k, k] * X[l, l] - 1e-12 * (1 + X[k, k] * X[l, l]))
    for Xe, Pe, ye, eps in ((Xp, Pp, yp, 1.0), (Xm, Pm, ym, -1.0)):
        cav_total = 0.0
        for i in N:
            J = nb(i)
            Ce = Cmat(Pe, ye, i)
            Cp = Cmat(Pp, yp, i)
            xi = np.array([sig[min(i, l), max(i, l)] for l in J])
            Tdir = np.array([[Ce[j, l] * u[l] * Cp[l, l] if l in N else 0.0 for l in J] for j in J])
            Tcav = np.array([[sum(Ce[j, k] * u[k] * Cp[k, l] for k in N if k != i and k != l)
                              for l in J] for j in J])
            for jj, j in enumerate(J):
                F = maskF(Xe, Xp, u, j, i)
                rhs = -a * Xe[i, i] * Xp[i, i] * ((Tdir @ xi)[jj] + (Tcav @ xi)[jj])
                src = -a * Xe[i, i] * Xp[i, i] * sum(Ce[j, k] * u[k] * Cp[k, l] * xi[ll]
                                                     for k in N if k != i for ll, l in enumerate(J))
                stats["FS2"] = max(stats["FS2"], abs(F - rhs) / (1 + abs(F)), abs(F - src) / (1 + abs(F)))
            # (B1)
            for _ in range(3):
                w = np.zeros(n)
                for k in S:
                    if k != i:
                        w[k] = rng.normal()
                lhs = sum((Ce[j] @ w) ** 2 for j in J)
                stats["B1"] = max(stats["B1"], lhs - w @ w / h ** 2)
            # (B2)
            for C, X in ((Ce, Xe), (Cp, Xp)):
                for k in range(n):
                    for l in range(n):
                        if k == i or l == i:
                            continue
                        r = X[i, i] * C[k, l] - (X[i, i] * X[k, l] - X[k, i] * X[i, l])
                        stats["B2"] = max(stats["B2"], abs(r) / (1 + abs(X[i, i] * X[k, l])))
                    if k != i:
                        stats["B2"] = max(stats["B2"], -X[i, i] * C[k, k] - 1e-12,
                                          X[i, i] * C[k, k] - X[i, i] * X[k, k] - 1e-12)
            trcav = (Tcav ** 2).sum()
            trdir = (Tdir ** 2).sum()
            cav_total += Xe[i, i] ** 2 * Xp[i, i] ** 2 * trcav
            ball = set([v]) | set(N) | set(w for k in N for w in nb(k))
            Dm = 1 + max(max(Gp[w, w], Gm[w, w]) for w in ball)
            Xe2 = Xe @ Xe
            dirb = 2 * Dm ** 6 / d * sum(Xe2[l, l] + Xe2[i, i] for l in J if l in N)
            stats["B6"] = max(stats["B6"], Xe[i, i] ** 2 * Xp[i, i] ** 2 * trdir - dirb)
        ball = set([v]) | set(N) | set(w for k in N for w in nb(k))
        Dm = 1 + max(max(Gp[w, w], Gm[w, w]) for w in ball)
        cavb = 2 * Dm ** 2 / h ** 2 * (Y1 / (a * a) + Dm / h * Y2)
        stats["B5"] = max(stats["B5"], cav_total - cavb)
    # (FS4)
    Omp = (Gp[v, v] / 2) ** 2
    Omm = Gp[v, v] * Gm[v, v] / 4
    for i in N:
        for j in nb(i):
            dP = -a * Gp[v, v] * Gp[v, i] * Gp[v, j]
            dM = a / 2 * (Gp[v, v] * Gm[v, i] * Gm[v, j] - Gp[v, i] * Gp[v, j] * Gm[v, v])
            gP = 2 * a * abs(Gp[v, i]) * abs(Gp[v, j])
            gM = a * (math.sqrt(max(Gp[v, v] * Gm[j, j], 0)) * abs(Gm[v, i]) +
                      math.sqrt(max(Gm[v, v] * Gp[j, j], 0)) * abs(Gp[v, i]))
            stats["FS4"] = max(stats["FS4"], abs(dP) - math.sqrt(Omp) * gP - 1e-14,
                               abs(dM) - math.sqrt(max(Omm, 0)) * gM - 1e-14)
            stats["FS4g"] = max(stats["FS4g"], gP ** 2 - 4 * a * a * Gp[v, i] ** 2 * Gp[v, v] * Gp[j, j] - 1e-14,
                                gM ** 2 - 2 * a * a * (Gp[v, v] * Gm[j, j] * Gm[v, i] ** 2 +
                                                       Gm[v, v] * Gp[j, j] * Gp[v, i] ** 2) - 1e-14)


def graphs():
    K4 = [(i, j) for i in range(4) for j in range(i + 1, 4)]
    K33 = [(i, j) for i in range(3) for j in range(3, 6)]
    Q3 = [(i, j) for i in range(8) for j in range(i + 1, 8) if bin(i ^ j).count("1") == 1]
    star = [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4), (4, 5), (2, 5)]
    K5 = [(i, j) for i in range(5) for j in range(i + 1, 5)]
    return [(4, K4), (6, K33), (8, Q3), (6, star), (5, K5)]


def main():
    print("(P1) pure Schur identities, worst relative residual:", check_pure())
    stats = dict(cases=0, skip=0, FS2=0.0, B1=-1e9, B2=0.0, B3=-1e9, B4=0.0, B5=-1e9, B6=-1e9,
                 FS4=-1e9, FS4g=-1e9)
    for n, E in graphs():
        for trial in range(40):
            d = max(sum(1 for e in E if k in e) for k in range(n))
            p = random.choice([3, 6, 12])
            q = d - 1.0
            a = 1.0 / math.sqrt(4 * q + 4.0 / p) * random.choice([1.0, 0.8, 1.3])
            s = 2.0
            S = set(range(n))
            if trial % 3 == 1 and n > 4:
                S.discard(n - 1)  # S a proper subset of V
            v = 0
            yp = np.array([random.choice([0.0, random.uniform(0.2, s), random.uniform(0, s)]) for _ in range(n)])
            ym = np.array([random.choice([0.0, random.uniform(0.2, s), random.uniform(0, s)]) for _ in range(n)])
            if trial % 4 == 0:
                yp = np.array([random.uniform(0.5 * s, s) for _ in range(n)])
                ym = np.array([random.uniform(0.5 * s, s) for _ in range(n)])
            h = random.choice([0.05, 0.2, 0.5])
            sig = {}
            for (x, w) in E:
                sig[min(x, w), max(x, w)] = random.choice([-1.0, 1.0])
            run_case(n, E, sorted(S), v, yp, ym, a, h, sig, stats)
    for k, val in stats.items():
        print(f"{k}: {val}")
    ok = (stats["FS2"] < 1e-9 and stats["B1"] <= 1e-9 and stats["B2"] < 1e-9 and stats["B3"] <= 1e-9 and
          stats["B4"] < 1e-9 and stats["B5"] <= 1e-9 and stats["B6"] <= 1e-9 and stats["FS4"] <= 1e-9 and
          stats["FS4g"] <= 1e-9)
    print("ALL OK" if ok else "FAILURE")


if __name__ == "__main__":
    main()
