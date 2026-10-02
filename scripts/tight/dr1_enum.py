"""DR1 check: exact enumeration of the paired determinantal law on small graphs.

Law: W(sigma) = 1{P+ > 0, P- > 0} (det P+ det P-)^p, P± = diag(Z±) ± a A_sigma.
Root v, x_i = G+_vi, z_i = G-_vi (i ~ v).  Exact first-order residuals
  R+_i = E[sigma_vi x_i] - E[D1 x_i],  R-_i = E[sigma_vi z_i] - E[D1 z_i],
  D1 x_i = -a G+_vv G+_ii + (2p-1) a x_i^2 - 2p a x_i z_i,
  D1 z_i = +a G-_vv G-_ii - (2p-1) a z_i^2 + 2p a x_i z_i,
  E3 = -a sum R+_i + a sum R-_i.
Checks: (1) DR1 identity (2p-1) a^2 sum E(x-z)^2 = B+ + B- + 2a^2 T + E3 (exact);
(2) D1 and d log W = 2pa(G+_vi - G-_vi) pointwise against rank-two closed forms (mpmath);
(3) E3 = -(a/3) sum E D3 x + (a/3) sum E D3 z + O(p^5 a^6 d) in a perturbative regime.
Run: /tmp/tight-venv/bin/python scripts/tight/dr1_enum.py
"""
import itertools
import numpy as np
import mpmath as mp

mp.mp.dps = 40

GRAPHS = {
    "K2": (2, [(0, 1)]),
    "K4": (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    "K33": (6, [(i, j) for i in range(3) for j in range(3, 6)]),
    "K5": (5, [(i, j) for i in range(5) for j in range(i + 1, 5)]),
    "Q3": (8, [(i, i ^ (1 << b)) for i in range(8) for b in range(3) if i < i ^ (1 << b)]),
    "Petersen": (10, [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)]
                 + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]),
    "star+": (5, [(0, 1), (0, 2), (0, 3), (1, 2), (3, 4)]),
}


def paper_Z(n, edges, a, y):
    """Z_i(y) = (1 + sum_j c_ij)/y_i with c(1+c) = a^2 y_i y_j (y_i > 0)."""
    Z = np.zeros(n)
    c = np.zeros(n)
    for (i, j) in edges:
        x = a * a * y[i] * y[j]
        cij = (np.sqrt(1 + 4 * x) - 1) / 2
        c[i] += cij
        c[j] += cij
    for i in range(n):
        Z[i] = (1 + c[i]) / y[i]
    return Z


def enumerate_law(n, edges, Zp, Zm, a, p):
    m = len(edges)
    sig = np.array(list(itertools.product([1.0, -1.0], repeat=m)))
    A = np.zeros((len(sig), n, n))
    for k, (i, j) in enumerate(edges):
        A[:, i, j] = sig[:, k]
        A[:, j, i] = sig[:, k]
    Pp = np.diag(Zp)[None] + a * A
    Pm = np.diag(Zm)[None] - a * A
    ok = (np.linalg.eigvalsh(Pp)[:, 0] > 0) & (np.linalg.eigvalsh(Pm)[:, 0] > 0)
    sig, Pp, Pm = sig[ok], Pp[ok], Pm[ok]
    logw = p * (np.linalg.slogdet(Pp)[1] + np.linalg.slogdet(Pm)[1])
    w = np.exp(logw - logw.max())
    return sig, np.linalg.inv(Pp), np.linalg.inv(Pm), w / w.sum(), ok.mean()


def dr1_quantities(n, edges, Zp, Zm, a, p, v):
    sig, Gp, Gm, w, frac = enumerate_law(n, edges, Zp, Zm, a, p)
    E = lambda f: float(np.dot(w, f))
    nb = [(k, j if i == v else i) for k, (i, j) in enumerate(edges) if v in (i, j)]
    x = {i: Gp[:, v, i] for _, i in nb}
    z = {i: Gm[:, v, i] for _, i in nb}
    Sp = sum(E(x[i] ** 2) for _, i in nb)
    Sm = sum(E(z[i] ** 2) for _, i in nb)
    T = sum(E(x[i] * z[i]) for _, i in nb)
    Diff = sum(E((x[i] - z[i]) ** 2) for _, i in nb)
    Bp = 1 - Zp[v] * E(Gp[:, v, v]) + a * a * sum(E(Gp[:, v, v] * Gp[:, i, i]) for _, i in nb)
    Bm = 1 - Zm[v] * E(Gm[:, v, v]) + a * a * sum(E(Gm[:, v, v] * Gm[:, i, i]) for _, i in nb)
    Rp = Rm = 0.0
    rowres = 0.0
    for k, i in nb:
        D1x = -a * Gp[:, v, v] * Gp[:, i, i] + (2 * p - 1) * a * x[i] ** 2 - 2 * p * a * x[i] * z[i]
        D1z = a * Gm[:, v, v] * Gm[:, i, i] - (2 * p - 1) * a * z[i] ** 2 + 2 * p * a * x[i] * z[i]
        Rp += E(sig[:, k] * x[i]) - E(D1x)
        Rm += E(sig[:, k] * z[i]) - E(D1z)
    # pointwise row equations  a sum sigma x = 1 - Z+_v G+_vv,  -a sum sigma z = 1 - Z-_v G-_vv
    rp = a * sum(sig[:, k] * x[i] for k, i in nb) - (1 - Zp[v] * Gp[:, v, v])
    rm = -a * sum(sig[:, k] * z[i] for k, i in nb) - (1 - Zm[v] * Gm[:, v, v])
    rowres = max(np.abs(rp).max(), np.abs(rm).max())
    E3 = -a * Rp + a * Rm
    lhs = (2 * p - 1) * a * a * Diff
    rhs = Bp + Bm + 2 * a * a * T + E3
    return dict(frac=frac, Sp=a * a * Sp, Sm=a * a * Sm, aT=a * a * T, diff=a * a * Diff,
                Bp=Bp, Bm=Bm, E3=E3, lhs=lhs, rhs=rhs, rowres=rowres,
                bound=(Bp + Bm + a * a * (Sp + Sm) + abs(E3)) / (2 * p - 1)), (sig, Gp, Gm, w, nb)


def fiber_taylor(G, a_eff, v, i, Gother, a_oth, p, order=5):
    """Taylor coefficients at t=0 of g(t) = W(t) psi(t)/W(0), psi = G_vi(t), along sigma_vi -> sigma_vi + t.
    G: inverse of the branch whose entry is tracked (perturbation +a_eff E); Gother: other branch (a_oth)."""
    g_vv, g_ii, g_vi = (mp.mpf(G[v, v]), mp.mpf(G[i, i]), mp.mpf(G[v, i]))
    h_vv, h_ii, h_vi = (mp.mpf(Gother[v, v]), mp.mpf(Gother[i, i]), mp.mpf(Gother[v, i]))

    def g(t):
        ta, tb = t * a_eff, t * a_oth
        d1 = (1 + ta * g_vi) ** 2 - ta ** 2 * g_vv * g_ii
        d2 = (1 + tb * h_vi) ** 2 - tb ** 2 * h_vv * h_ii
        M = mp.matrix([[1 + ta * g_vi, ta * g_ii], [ta * g_vv, 1 + ta * g_vi]])
        psi = g_vi - ta * (mp.matrix([[g_vv, g_vi]]) * mp.inverse(M) * mp.matrix([[g_ii], [g_vi]]))[0, 0]
        return d1 ** p * d2 ** p * psi
    return [c * mp.factorial(k) for k, c in enumerate(mp.taylor(g, 0, order))]


def pointwise_checks(n, edges, Zp, Zm, a, p, v, data, nsamp=6, seed=1):
    sig, Gp, Gm, w, nb = data
    rng = np.random.default_rng(seed)
    worst = 0.0
    for s in rng.choice(len(sig), size=min(nsamp, len(sig)), replace=False):
        for k, i in nb:
            cx = fiber_taylor(Gp[s], mp.mpf(a), v, i, Gm[s], -mp.mpf(a), p, order=1)
            cz = fiber_taylor(Gm[s], -mp.mpf(a), v, i, Gp[s], mp.mpf(a), p, order=1)
            x, zz = Gp[s, v, i], Gm[s, v, i]
            D1x = -a * Gp[s, v, v] * Gp[s, i, i] + (2 * p - 1) * a * x * x - 2 * p * a * x * zz
            D1z = a * Gm[s, v, v] * Gm[s, i, i] - (2 * p - 1) * a * zz * zz + 2 * p * a * x * zz
            worst = max(worst, abs(float(cx[1]) - D1x), abs(float(cz[1]) - D1z))
    return worst


def third_order(n, edges, Zp, Zm, a, p, v, data):
    sig, Gp, Gm, w, nb = data
    t3 = 0.0
    for s in range(len(sig)):
        for k, i in nb:
            cx = fiber_taylor(Gp[s], mp.mpf(a), v, i, Gm[s], -mp.mpf(a), p, order=3)
            cz = fiber_taylor(Gm[s], -mp.mpf(a), v, i, Gp[s], mp.mpf(a), p, order=3)
            t3 += w[s] * (-a / 3 * float(cx[3]) + a / 3 * float(cz[3]))
    return -t3  # E3 = -a sum R+ + a sum R-, R = -(1/3) E D3 + O(5th)


def main():
    rng = np.random.default_rng(0)
    print("== (1) DR1 identity, paper-type parameters (Z from sources), all neighbours of v ==")
    print(f"{'graph':9s} {'p':>3s} {'supp':>5s} {'a2S+':>9s} {'a2S-':>9s} {'a2T':>10s} {'diff':>9s}"
          f" {'E3':>10s} {'idres':>8s} {'diff<=bnd':>9s}")
    worst_id = 0.0
    for name, (n, edges) in GRAPHS.items():
        d = max(sum(1 for e in edges if u in e) for u in range(n))
        for p in (3, 6, 12, 25):
            a = 1 / np.sqrt(4 * (d - 1) + 4 / p)
            y = rng.uniform(0.25, 0.7, size=n) * 2.0
            Zp, Zm = paper_Z(n, edges, a, y), paper_Z(n, edges, a, rng.uniform(0.25, 0.7, size=n) * 2.0)
            q, data = dr1_quantities(n, edges, Zp, Zm, a, p, 0)
            idres = abs(q["lhs"] - q["rhs"]) / max(1e-300, abs(q["lhs"]) + abs(q["rhs"]))
            worst_id = max(worst_id, idres, q["rowres"])
            print(f"{name:9s} {p:3d} {q['frac']:5.2f} {q['Sp']:9.2e} {q['Sm']:9.2e} {q['aT']:10.2e}"
                  f" {q['diff']:9.2e} {q['E3']:10.2e} {idres:8.1e} {str(q['diff'] <= q['bound'] + 1e-15):>9s}")
    print("worst relative identity residual / row-equation residual:", f"{worst_id:.1e}")

    print("\n== zero plus-source at the root (physical row x = 0): DR1 reduces to a minus-row bound ==")
    n, edges = GRAPHS["K33"]
    a, p = 1 / np.sqrt(8 + 4 / 6), 6
    Zp = paper_Z(n, edges, a, rng.uniform(0.5, 1.4, size=n))
    Zp[0] = 1e12  # y_v^+ -> 0: Z_v -> infinity, G+_v. -> 0
    Zm = paper_Z(n, edges, a, rng.uniform(0.5, 1.4, size=n))
    q, _ = dr1_quantities(n, edges, Zp, Zm, a, p, 0)
    print(f"a2S+={q['Sp']:.1e}  a2S-={q['Sm']:.3e}  diff={q['diff']:.3e}  B+={q['Bp']:.1e}"
          f"  (B-+E3)/(2p-1)={(q['Bm'] + q['E3']) / (2 * p - 1):.3e}")

    print("\n== (2) pointwise D1 and score formulas vs rank-two closed forms (mpmath) ==")
    for name in ("K4", "K33", "K5"):
        n, edges = GRAPHS[name]
        d = 3 if name != "K5" else 4
        a, p = 1 / np.sqrt(4 * (d - 1) + 4 / 5), 5
        Zp = paper_Z(n, edges, a, rng.uniform(0.5, 1.4, size=n))
        Zm = paper_Z(n, edges, a, rng.uniform(0.5, 1.4, size=n))
        q, data = dr1_quantities(n, edges, Zp, Zm, a, p, 0)
        print(f"{name}: max |D1 formula - d/dt(W psi)/W| = {pointwise_checks(n, edges, Zp, Zm, a, p, 0, data):.1e}")

    print("\n== (3) E3 versus third-order endpoint term, perturbative regime (Z ~ 1, small a) ==")
    for name in ("K4", "K33"):
        n, edges = GRAPHS[name]
        Zp, Zm = 1 + 0.3 * rng.random(n), 1 + 0.3 * rng.random(n)
        for p in (3, 6):
            for a in (0.04, 0.02):
                q, data = dr1_quantities(n, edges, Zp, Zm, a, p, 0)
                t3 = third_order(n, edges, Zp, Zm, a, p, 0, data)
                print(f"{name} p={p} a={a}: E3={q['E3']:+.4e}  third-order={t3:+.4e}  "
                      f"rel.rem={abs(q['E3'] - t3) / abs(q['E3']):.1e}  E3/(p^3 a^4 deg)="
                      f"{abs(q['E3']) / (p ** 3 * a ** 4 * 3):.2f}")


if __name__ == "__main__":
    main()
