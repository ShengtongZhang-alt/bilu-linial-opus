"""Exact enumeration checks of the exact/deterministic leaves of BiluLinial/Tight/Contact/Leaves.lean
on small graphs, with the Lean definitions (normalized precisions P~ = diag D(y) + tau*a*Y^{1/2} A_s Y^{1/2},
physical G = Y^{1/2} P~^{-1} Y^{1/2}, shifted X = Y^{1/2} (P~ + h Y)^{-1} Y^{1/2}, core shift with the
row/column of v replaced by the identity).

Checked at random points of the source cube [0, s]^V (including zero sources), S = V, root v = 0:
  root_equation (exact), d15_cs, source_facts (C+ <= J, D+ = 1 + L - C+, L <= Lbar, C+ <= a^2 Lbar s^2),
  energy_psd (all 12 conjuncts), rc4 lower bounds, the identity L_d[(p-1)q+ + p q-] =
  a^2 E[(p-1) G_vv^2 tr X[N,N]^2 + p G+_vv G-_vv tr(X+ X-)[N,N]], d10_corr sign (Q_full >= Q),
  and bm1_det pointwise on every supported signing.
Run: /tmp/tight-venv/bin/python scripts/tight/check_leaves_enum.py
"""
import itertools
import math
import random

import numpy as np

random.seed(3)
np.random.seed(3)


def params(d, p):
    q = d - 1.0
    D = 4.0 / p
    a = 1.0 / math.sqrt(4 * q + D)
    eta0 = (math.sqrt(D * D + 4 * q * D) - D) / (2 * q)
    tau = (1 - eta0) / q
    s = (1 + q * tau) / (1 - tau)
    r = 1 + eta0 / 2
    return a, s, r, eta0


def croot(x):
    return (math.sqrt(1 + 4 * x) - 1) / 2


def graphs():
    K4 = [(i, j) for i in range(4) for j in range(i + 1, 4)]
    K33 = [(i, j) for i in range(3) for j in range(3, 6)]
    Q3 = [(i, j) for i in range(8) for j in range(i + 1, 8) if bin(i ^ j).count("1") == 1]
    star = [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]  # non-regular
    return {"K4": (4, K4), "K33": (6, K33), "Q3": (8, Q3), "star+": (5, star)}


def run(name, n, E, p, h, y_p, y_m):
    deg = [sum(1 for e in E if k in e) for k in range(n)]
    d = max(deg)
    a, s, r, eta0 = params(d, p)
    adj = np.zeros((n, n))
    for (i, j) in E:
        adj[i, j] = adj[j, i] = 1
    v = 0
    N = [i for i in range(n) if adj[v, i]]

    def Dvec(y):
        return np.array([1 + sum(croot(a * a * y[k] * y[j]) for j in range(n) if adj[k, j]) for k in range(n)])

    Dp, Dm = Dvec(y_p), Dvec(y_m)
    sq_p, sq_m = np.sqrt(y_p), np.sqrt(y_m)
    uvec = np.array([1 / math.sqrt(d) if i in N else 0.0 for i in range(n)])
    tot = {}
    Z = 0.0
    bm1_worst = 0.0

    def acc(key, val, w):
        tot[key] = tot.get(key, 0.0) + w * val

    for signs in itertools.product([-1, 1], repeat=len(E)):
        sig = np.zeros((n, n))
        for (e, sgn) in zip(E, signs):
            sig[e[0], e[1]] = sig[e[1], e[0]] = sgn
        Pp = np.diag(Dp) + a * np.outer(sq_p, sq_p) * sig
        Pm = np.diag(Dm) - a * np.outer(sq_m, sq_m) * sig
        if min(np.linalg.eigvalsh(Pp)) <= 0 or min(np.linalg.eigvalsh(Pm)) <= 0:
            continue
        w = (np.linalg.det(Pp) * np.linalg.det(Pm)) ** p
        Z += w
        Ip, Im = np.linalg.inv(Pp), np.linalg.inv(Pm)
        Gp = np.outer(sq_p, sq_p) * Ip
        Gm = np.outer(sq_m, sq_m) * Im
        Xp = np.outer(sq_p, sq_p) * np.linalg.inv(Pp + h * np.diag(y_p))
        Xm = np.outer(sq_m, sq_m) * np.linalg.inv(Pm + h * np.diag(y_m))

        def core_shift(P, y, sq):
            Pc = P.copy()
            Pc[v, :] = 0
            Pc[:, v] = 0
            Pc[v, v] = 1
            yc = y.copy()
            yc[v] = 0
            return np.outer(sq, sq) * np.linalg.inv(Pc + h * np.diag(yc))

        Yp, Ym = core_shift(Pp, y_p, sq_p), core_shift(Pm, y_m, sq_m)
        acc("hv", Ip[v, v], w)
        for i in N:
            acc(("sx", i), sig[v, i] * Gp[v, i], w)
            acc(("x2", i), Gp[v, i] ** 2, w)
        Kp = Xp * Xp / 4
        Km = Xp * Xm / 4
        Mp = np.diag((np.diag(Xp) / 2) ** 2)
        Mm = np.diag(np.diag(Xp) / 2 * np.diag(Xm) / 2)
        bp = 4 * a * a * adj @ (Mp @ uvec)
        bm = 4 * a * a * adj @ (Mm @ uvec)
        Omp = (Gp[v, v] / 2) ** 2
        Omm = Gp[v, v] * Gm[v, v] / 4
        vals = {
            "qP": Omp * uvec @ Kp @ uvec, "zeta": Omp * uvec @ Kp @ bp, "zP": Omp * bp @ Kp @ bp,
            "tP": Omp * uvec @ Mp @ uvec, "alpha": Omp * uvec @ Mp @ bp,
            "qM": Omm * uvec @ Km @ uvec, "zetaM": Omm * uvec @ Km @ bm, "zM": Omm * bm @ Km @ bm,
            "tM": Omm * uvec @ Mm @ uvec, "beta": Omm * uvec @ Mm @ bm,
            "tP0": Gp[v, v] ** 2 * sum(Gp[i, i] ** 2 for i in N) / (16 * d),
            "tM0": Gp[v, v] * Gm[v, v] * sum(Gp[i, i] * Gm[i, i] for i in N) / (16 * d),
            "Qbl": a * a * ((p - 1) * Gp[v, v] ** 2 * sum(Yp[i, j] ** 2 for i in N for j in N)
                            + p * Gp[v, v] * Gm[v, v] * sum(Yp[i, j] * Ym[i, j] for i in N for j in N)),
            "Qfull": a * a * ((p - 1) * Gp[v, v] ** 2 * sum(Xp[i, j] ** 2 for i in N for j in N)
                              + p * Gp[v, v] * Gm[v, v] * sum(Xp[i, j] * Xm[i, j] for i in N for j in N)),
        }
        for k_, val in vals.items():
            acc(k_, val, w)
        # bm1_det pointwise: (X, Y, b) = (Xp, Xp, bp) and (Xm, Xp, bm), I = N, D = max X_ii on N
        for (X, Y, b) in [(Xp, Xp, bp), (Xm, Xp, bm)]:
            if not N:
                continue
            Dm_ = max(X[i, i] for i in N)
            U = X @ np.diag(b) @ Y
            lhs = sum((X[i, i] * U[j, i] - X[j, i] * U[i, i]) ** 2 for i in N for j in range(n))
            rhs = 16 * Dm_ ** 2 / h ** 2 * (b @ ((X * Y / 4) @ b))
            if rhs > 0:
                bm1_worst = max(bm1_worst, lhs / rhs)
            assert lhs <= rhs * (1 + 1e-9) + 1e-300, (name, lhs, rhs)
            # hypotheses of bm1: X, Y PSD with ||X|| <= 1/h (including the padded part)
            assert max(np.linalg.eigvalsh(X)) <= 1 / h * (1 + 1e-9)
    E_ = {k: val / Z for k, val in tot.items()}
    # root_equation
    root = Dp[v] * E_["hv"] + a * sum(E_[("sx", i)] for i in N)
    S = sum(E_[("x2", i)] for i in N)
    cs_l = sum(E_[("sx", i)] for i in N) ** 2
    # source facts at v
    ell = [a * a * y_p[v] * y_p[i] for i in N]
    c = [croot(x) for x in ell]
    Cp = sum(ci ** 2 for ci in c)
    L = sum(ell)
    tau_e = lambda i, j: croot(a * a * y_p[i] * y_p[j]) / (1 + croot(a * a * y_p[i] * y_p[j]))
    B = np.eye(n)
    for i in range(n):
        B[i, i] = 1 + sum(tau_e(i, j) ** 2 / (1 - tau_e(i, j) ** 2) for j in range(n) if adj[i, j])
        for j in range(n):
            if adj[i, j]:
                B[i, j] = -tau_e(i, j) / (1 - tau_e(i, j) ** 2)
    Kw = np.linalg.inv(B)
    J = sum(ell[k] * Kw[v, i] for k, i in enumerate(N))
    Lbar = d * a * a * s * s
    Ld = 16 * d * a * a
    out = {
        "root_eq_resid": root - 1,
        "d15_cs_slack": len(N) * S - cs_l,
        "J-C+": J - Cp, "D+ - (1+L-C+)": Dp[v] - (1 + L - Cp), "Lbar-L": Lbar - L,
        "a2Lbar s2 - C+": a * a * Lbar * s * s - Cp,
        "qP": E_["qP"], "zP": E_["zP"], "qz-zeta2": E_["qP"] * E_["zP"] - E_["zeta"] ** 2,
        "qP-tP": E_["qP"] - E_["tP"], "alpha": E_["alpha"], "zeta-alpha": E_["zeta"] - E_["alpha"],
        "tP": E_["tP"], "qM": E_["qM"], "zM": E_["zM"], "qz-zetaM2": E_["qM"] * E_["zM"] - E_["zetaM"] ** 2,
        "beta": E_["beta"], "tM": E_["tM"],
        "tP0-tP": E_["tP0"] - E_["tP"], "tM0-tM": E_["tM0"] - E_["tM"],
        "Qfull identity": Ld * ((p - 1) * E_["qP"] + p * E_["qM"]) - E_["Qfull"],
        "Qfull-Qbl": E_["Qfull"] - E_["Qbl"],
    }
    return out, bm1_worst


def main(positive=False):
    worst = {}
    bmw = 0.0
    ncase = 0
    for name, (n, E) in graphs().items():
        for p in [3, 6, 12]:
            for trial in range(3 if n <= 6 else 1):
                deg = max(sum(1 for e in E if k in e) for k in range(n))
                a, s, r, eta0 = params(deg, p)
                if positive:
                    y_p = np.array([random.uniform(0.2 * s, s) for _ in range(n)])
                    y_m = np.array([random.uniform(0.2 * s, s) for _ in range(n)])
                else:
                    y_p = np.array([random.choice([0.0, s, random.uniform(0, s)]) for _ in range(n)])
                    y_m = np.array([random.choice([0.0, s, random.uniform(0, s)]) for _ in range(n)])
                y_p[0] = random.uniform(0.5 * s, s)  # contacting source positive
                h = random.choice([0.05, 0.3, 1.0])
                out, bw = run(name, n, E, p, h, y_p, y_m)
                ncase += 1
                bmw = max(bmw, bw)
                for k, val in out.items():
                    worst[k] = min(worst.get(k, math.inf), val) if k not in ("root_eq_resid", "D+ - (1+L-C+)", "Qfull identity") else max(worst.get(k, 0.0), abs(val))
    kind_src = "sources uniform in [0.2s, s]" if positive else "random sources incl. zeros"
    print(f"{ncase} cases (K4, K33, Q3, star+; p = 3, 6, 12; {kind_src}; h in {{0.05, 0.3, 1}})")
    for k, val in worst.items():
        kind = "max |.|" if k in ("root_eq_resid", "D+ - (1+L-C+)", "Qfull identity") else "min (>= 0 required)"
        print(f"  {k:22s} {kind}: {val:.3e}")
    print(f"  bm1_det worst ratio LHS/RHS over all supported signings: {bmw:.4f} (<= 1 required)")


if __name__ == "__main__":
    main()
    main(positive=True)
