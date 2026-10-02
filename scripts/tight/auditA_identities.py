"""AUDIT-A exact-enumeration checks on a small graph (lines 125-141, 237-625).

Checks
 (I1) insertion factorisation E_H[g] = E_{nu_K} R_xi[Phi g] / F_H, with F1;
 (I2) the exact Schur identity (C3);
 (I3) the derivative calculus (E3) along an edge fibre (finite differences);
 (I4) the fibre form of (E1): |E xi phi - E(phi' - phi'''/3)| <= (2/15) sup|phi^(5)|
      on fibres whose whole segment is good;
 (I5) (C5) and the trace inequality tr(Cz[N,N] C[N,N]) <= 2 d W / z (branchwise form).
"""
import itertools
import numpy as np
import mpmath as mp

rng = np.random.default_rng(1)

# ---------------- small graph and parameters ----------------
n = 7
d = 4
p = 3
q = d - 1
Delta = 4.0 / p
R = np.sqrt(4 * q + Delta)
a = 1.0 / R
eta = (-Delta + np.sqrt(Delta**2 + 4 * q * Delta)) / (2 * q)
tau_s = (1 - eta) / q
s = (1 + q * tau_s) / (1 - tau_s)

edges = []
deg = np.zeros(n, int)
for i, j in itertools.combinations(range(n), 2):
    if rng.random() < 0.55 and deg[i] < d and deg[j] < d:
        edges.append((i, j)); deg[i] += 1; deg[j] += 1
E = len(edges)
adj = {i: [] for i in range(n)}
for (i, j) in edges:
    adj[i].append(j); adj[j].append(i)


def Zvec(y):
    Z = np.zeros(n)
    c = {}
    for (i, j) in edges:
        prod = a * a * y[i] * y[j]
        cij = (-1 + np.sqrt(1 + 4 * prod)) / 2
        c[(i, j)] = c[(j, i)] = cij
    for i in range(n):
        Z[i] = (1 + sum(c[(i, j)] for j in adj[i])) / y[i]
    return Z, c

yp = rng.uniform(0.5, 1.0, n) * s
ym = rng.uniform(0.5, 1.0, n) * s
Zp, _ = Zvec(yp)
Zm, _ = Zvec(ym)


def precisions(sig, Zp_, Zm_, verts):
    idx = {v: k for k, v in enumerate(verts)}
    m = len(verts)
    As = np.zeros((m, m))
    for e, (i, j) in enumerate(edges):
        if i in idx and j in idx:
            As[idx[i], idx[j]] = As[idx[j], idx[i]] = sig[e]
    Pp = np.diag([Zp_[v] for v in verts]) + a * As
    Pm = np.diag([Zm_[v] for v in verts]) - a * As
    return Pp, Pm


def weight(Pp, Pm):
    try:
        np.linalg.cholesky(Pp); np.linalg.cholesky(Pm)
    except np.linalg.LinAlgError:
        return 0.0
    return (np.linalg.det(Pp) * np.linalg.det(Pm)) ** p

allV = list(range(n))
configs = list(itertools.product([-1, 1], repeat=E))
W = np.array([weight(*precisions(sg, Zp, Zm, allV)) for sg in configs])
print(f"graph: n={n}, |E|={E}, max deg={deg.max()}, supported fraction={np.mean(W>0):.3f}")
Ztot = W.sum()
assert Ztot > 0


def EH(func):
    tot = 0.0
    for sg, w in zip(configs, W):
        if w > 0:
            Pp, Pm = precisions(sg, Zp, Zm, allV)
            tot += w * func(sg, np.linalg.inv(Pp), np.linalg.inv(Pm))
    return tot / Ztot

# ---------------- (I1),(I2) at root v ----------------
v = int(np.argmax(deg))
N = adj[v]
K = [u for u in allV if u != v]
kidx = {u: k for k, u in enumerate(K)}
Nk = [kidx[i] for i in N]
core_edges = [e for e, (i, j) in enumerate(edges) if v not in (i, j)]
root_edges = {e: (j if i == v else i) for e, (i, j) in enumerate(edges) if v in (i, j)}
assert set(root_edges.values()) == set(N)


def core_quantities(sg_core_full):
    Pp, Pm = precisions(sg_core_full, Zp, Zm, K)
    w = weight(Pp, Pm)
    if w == 0:
        return 0.0, None, None
    Gp, Gm = np.linalg.inv(Pp), np.linalg.inv(Pm)
    A = (a * a / Zp[v]) * Gp[np.ix_(Nk, Nk)]
    B = (a * a / Zm[v]) * Gm[np.ix_(Nk, Nk)]
    return w, A, B

# enumerate cores: configurations of core edges (root edges irrelevant for the core law)
core_cfgs = list(itertools.product([-1, 1], repeat=len(core_edges)))
xis = list(itertools.product([-1, 1], repeat=len(N)))
num_FH = 0.0; num_NR = 0.0; Zk = 0.0
for cc in core_cfgs:
    sg = np.zeros(E)
    for e, val in zip(core_edges, cc):
        sg[e] = val
    w, A, B = core_quantities(sg)
    if w == 0:
        continue
    Zk += w
    f = 0.0; nr = 0.0
    for xi in xis:
        x = np.array(xi, float)
        al = max(0.0, 1 - x @ A @ x); be = max(0.0, 1 - x @ B @ x)
        f += al**p * be**p
        nr += (np.trace(A) - x @ A @ x) * al ** (p - 1) * be**p
    f /= len(xis); nr /= len(xis)
    num_FH += w * f; num_NR += w * nr
FH = num_FH / Zk
lhs_C3 = (num_NR / Zk) / FH

def rhs_func(sg, Gp, Gm):
    val = 1 - Zp[v] * Gp[v, v]
    for i in N:
        val += a * a * (Gp[v, v] * Gp[i, i] - Gp[v, i] ** 2)
    return val
rhs_C3 = EH(rhs_func)
print(f"(I2) C3: E_nuK N_R/F_H = {lhs_C3:.12f}   RHS = {rhs_C3:.12f}   diff={abs(lhs_C3-rhs_C3):.2e}")

# F1 check on one supported configuration
for sg, w in zip(configs, W):
    if w > 0:
        Pp, Pm = precisions(sg, Zp, Zm, allV)
        Gp, Gm = np.linalg.inv(Pp), np.linalg.inv(Pm)
        sgc = np.array(sg, float).copy()
        for e in root_edges: sgc[e] = 0
        _, A, B = core_quantities(sgc)
        # xi_i = sign of edge (v,i)
        xi = np.zeros(len(N))
        for e, i in root_edges.items():
            xi[N.index(i)] = sg[e]
        al = 1 - xi @ A @ xi; be = 1 - xi @ B @ xi
        errs = [abs(Zp[v] * Gp[v, v] - 1 / al), abs(Zm[v] * Gm[v, v] - 1 / be)]
        for k, i in enumerate(N):
            errs.append(abs(Gp[v, i] + (A @ xi)[k] / (a * al)))
            errs.append(abs(Gm[v, i] - (B @ xi)[k] / (a * be)))
        print("(I1) F1 max error on a supported config:", max(errs))
        break

# ---------------- (I3),(I4) fibre calculus ----------------
mp.mp.dps = 30
i0 = N[0]
e0 = [e for e, j in root_edges.items() if j == i0][0]


def fibre_fun(sg, svar):
    sgl = [mp.mpf(x) for x in sg]
    sgl[e0] = svar
    m = n
    Pp = mp.matrix(m, m); Pm = mp.matrix(m, m)
    for k in range(m):
        Pp[k, k] = Zp[k]; Pm[k, k] = Zm[k]
    for e, (i, j) in enumerate(edges):
        Pp[i, j] = Pp[j, i] = a * sgl[e]
        Pm[i, j] = Pm[j, i] = -a * sgl[e]
    return Pp, Pm


def good(Pp, Pm):
    return min(mp.eigsy(Pp)[0]) > 0 and min(mp.eigsy(Pm)[0]) > 0


def phi(sg, svar):
    Pp, Pm = fibre_fun(sg, svar)
    Gp = Pp ** -1
    return (mp.det(Pp) * mp.det(Pm)) ** p * Gp[v, i0]

maxratio = 0.0
checked = 0
calc_err = 0.0
for sg, w in zip(configs, W):
    if w == 0 or sg[e0] != 1:
        continue
    # whole segment good?  test on a grid
    if not all(good(*fibre_fun(sg, mp.mpf(tt))) for tt in np.linspace(-1, 1, 21)):
        continue
    checked += 1
    f = lambda tt: phi(sg, tt)
    d1 = lambda tt: mp.diff(f, tt, 1)
    d3 = lambda tt: mp.diff(f, tt, 3)
    Lf = (f(1) - f(-1)) / 2 - (d1(1) + d1(-1)) / 2 + (d3(1) + d3(-1)) / 6
    sup5 = max(abs(mp.diff(f, mp.mpf(tt), 5)) for tt in np.linspace(-1, 1, 11))
    maxratio = max(maxratio, float(abs(Lf) / sup5))
    if checked == 1:
        # (E3) at s=1: d/ds G^+_{jl} = -a(G_{jv}G_{il}+G_{ji}G_{vl}); d/ds log W = 2pa(G+_{vi}-G-_{vi})
        Pp, Pm = fibre_fun(sg, mp.mpf(1))
        Gp, Gm = Pp ** -1, Pm ** -1
        for (j, l) in [(v, i0), (i0, i0), (v, v), (N[-1], K[0])]:
            num = mp.diff(lambda tt: (fibre_fun(sg, tt)[0] ** -1)[j, l], mp.mpf(1))
            pred = -a * (Gp[j, v] * Gp[i0, l] + Gp[j, i0] * Gp[v, l])
            calc_err = max(calc_err, float(abs(num - pred)))
            num = mp.diff(lambda tt: (fibre_fun(sg, tt)[1] ** -1)[j, l], mp.mpf(1))
            pred = +a * (Gm[j, v] * Gm[i0, l] + Gm[j, i0] * Gm[v, l])
            calc_err = max(calc_err, float(abs(num - pred)))
        logW = lambda tt: p * (mp.log(mp.det(fibre_fun(sg, tt)[0])) + mp.log(mp.det(fibre_fun(sg, tt)[1])))
        num = mp.diff(logW, mp.mpf(1))
        pred = 2 * p * a * (Gp[v, i0] - Gm[v, i0])
        calc_err = max(calc_err, float(abs(num - pred)))
    if checked >= 6:
        break
print(f"(I3) E3 max error: {calc_err:.2e}")
print(f"(I4) fibres checked={checked}, max |L(phi)|/sup|phi^(5)| = {maxratio:.4f} (bound 2/15={2/15:.4f})")

# ---------------- (I5) C5 and trace inequalities ----------------
worst = []
for trial in range(200):
    m = 6
    Nn = [1, 2, 3, 4]
    X = rng.normal(size=(m, m)); PK = X @ X.T + 0.3 * np.eye(m)
    Zv = rng.uniform(1, 3)
    xi = rng.choice([-1.0, 1.0], size=len(Nn))
    aa = rng.uniform(0.05, 0.4)
    z = rng.uniform(0.01, 1.0)
    C = np.linalg.inv(PK); Cz = np.linalg.inv(PK + z * np.eye(m))
    if Zv - aa * aa * xi @ C[np.ix_(Nn, Nn)] @ xi <= 0:
        continue
    # full matrices with root first
    P = np.zeros((m + 1, m + 1)); P[0, 0] = Zv; P[1:, 1:] = PK
    for k, i in enumerate(Nn):
        P[0, 1 + i] = P[1 + i, 0] = aa * xi[k]
    G = np.linalg.inv(P); Xz = np.linalg.inv(P + z * np.eye(m + 1))
    NN = [1 + i for i in Nn]
    lhs = np.trace(Xz[np.ix_(NN, NN)]) - np.trace(Cz[np.ix_(Nn, Nn)])
    mid = aa * aa * Xz[0, 0] * xi @ Cz[np.ix_(Nn, Nn)] @ Cz[np.ix_(Nn, Nn)] @ xi
    rhs = (Zv / z) * (G[0, 0] - Xz[0, 0])
    schur = aa * aa * xi @ (C - Cz)[np.ix_(Nn, Nn)] @ xi - (1 / Xz[0, 0] - 1 / G[0, 0] - z)
    # trace inequality (branchwise, nu = +): tr(Cz[N,N] C[N,N]) <= 2 * tr((C-Cz)[N,N]) / z
    trl = np.trace(Cz[np.ix_(Nn, Nn)] @ C[np.ix_(Nn, Nn)])
    trr = 2 * np.trace((C - Cz)[np.ix_(Nn, Nn)]) / z
    worst.append((abs(lhs - mid), mid - rhs, abs(schur), trl - trr))
worst = np.array(worst)
print(f"(I5) C5 identity err={worst[:,0].max():.1e}, max(mid-rhs)={worst[:,1].max():.2e} (<=0 expected), "
      f"Schur err={worst[:,2].max():.1e}, max(trace lhs - 2trW/z)={worst[:,3].max():.2e} (<=0 expected)")
