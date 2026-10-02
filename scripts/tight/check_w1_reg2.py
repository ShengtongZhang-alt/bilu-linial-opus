"""Rule-2 check of the TB.W1fib-reg sub-nodes in the exact Lean model (W1FibReg.lean).

Normalized precisions P~(t) = diag(D) + tau a sqrt(y) sqrt(y)^T o Sigma(t) (edge value t on ij),
physical G = Y^1/2 P~^-1 Y^1/2, X = Y^1/2 (P~ + h Y)^-1 Y^1/2, random positive sources y.
phi(t) = (det P~+(t) det P~-(t))^p * Psi_k(P~+(t), P~-(t)).
Checks, for every fibre (sigma_e = +1) with a good endpoint (W > 0, 64 p a g* <= 1):
  seg : P~+-(t) positive definite for t in [-2, 2]                         (TB.W1fib-seg)
  d1  : phi'(1) = W DPsi(sigma), phi'(-1) = W DPsi(sigma') (fibD formula)   (TB.W1fib-d1)
  d3  : sup_[-1,1] |phi'''| / (W(s) Yb(s) + W(s') Yb(s'))  (M = 10)         (TB.W1fib-d3)
"""
import itertools
import numpy as np

rng = np.random.default_rng(7)
n = 6
edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 4), (4, 5)]
A0 = np.zeros((n, n))
for (k, l) in edges:
    A0[k, l] = A0[l, k] = 1
dd = int(A0.sum(1).max())
v = 0
Nset = [k for k in range(n) if A0[v, k]]
ball = sorted(set([v] + Nset + [j for i in Nset for j in range(n) if A0[i, j]]))
u = np.array([1 / np.sqrt(dd) if k in Nset else 0.0 for k in range(n)])
yp = 0.5 + rng.random(n)
ym = 0.5 + rng.random(n)
Dp = 4.0 + 2 * rng.random(n)
Dm = 4.0 + 2 * rng.random(n)
p = 3
h = 0.3
M = 10


def mats(Sg, a):
    sp, sm = np.sqrt(yp), np.sqrt(ym)
    Pp = np.diag(Dp) + a * np.outer(sp, sp) * Sg
    Pm = np.diag(Dm) - a * np.outer(sm, sm) * Sg
    return Pp, Pm


def phys(y, A):
    s = np.sqrt(y)
    return np.outer(s, s) * np.linalg.inv(A)


def obs(Pp, Pm, c, i, j, a):
    """Psi, DPsi and the endpoint data of configuration c (0..3) at (Pp, Pm)."""
    eps = 1 if c in (0, 1) else -1
    Gp, Gm = phys(yp, Pp), phys(ym, Pm)
    Xp = phys(yp, Pp + h * np.diag(yp))
    Xm = phys(ym, Pm + h * np.diag(ym))
    Xe = Xp if eps > 0 else Xm
    Xn = Xp
    if eps > 0:
        H = (Gp[v, v] / 2) ** 2
        dH = -a * Gp[v, v] * Gp[v, i] * Gp[v, j]
        b = 4 * a * a * A0 @ ((np.diag(Xp) / 2) ** 2 * u)
    else:
        H = Gp[v, v] * Gm[v, v] / 4
        dH = a / 2 * (Gp[v, v] * Gm[v, i] * Gm[v, j] - Gp[v, i] * Gp[v, j] * Gm[v, v])
        b = 4 * a * a * A0 @ (np.diag(Xp) / 2 * np.diag(Xm) / 2 * u)
    f = u if c in (0, 2) else b
    U = Xe @ np.diag(f) @ Xn
    F = Xe[i, i] * U[j, i] - Xe[j, i] * U[i, i]
    if c == 0 or c == 2:
        df = np.zeros(n)
    elif c == 1:
        df = -4 * a ** 3 * A0 @ (u * np.diag(Xp) * Xp[:, i] * Xp[:, j])
    else:
        df = 2 * a ** 3 * A0 @ (u * (np.diag(Xp) * Xm[:, i] * Xm[:, j] - np.diag(Xm) * Xp[:, i] * Xp[:, j]))
    Ud = Xe @ np.diag(df) @ Xn
    Fd = Xe[i, i] * Ud[j, i] - Xe[j, i] * Ud[i, i]
    sec = -a * (2 * eps * Xe[i, j] * F + Xn[i, j] * F - Xn[i, i] * Xe[i, j] * U[i, j])
    DPsi = (dH * F + 2 * p * a * (Gp[i, j] - Gm[i, j]) * H * F
            + H * sec + H * Fd - a * H * Xe[i, i] * Xn[i, i] * U[j, j])
    W = (np.linalg.det(Pp) * np.linalg.det(Pm)) ** p
    pd = np.linalg.eigvalsh(Pp).min() > 0 and np.linalg.eigvalsh(Pm).min() > 0
    gstar = Gp[i, i] + Gp[j, j] + Gm[i, i] + Gm[j, j]
    Dst = 1 + max(max(Gp[w, w], Gm[w, w]) for w in ball)
    R = abs(Gp[i, j]) + abs(Gm[i, j])
    Yb = a ** 3 / (np.sqrt(dd) * h) * Dst ** M * (p ** 3 * R ** 2 + p)
    return dict(Psi=H * F, DPsi=DPsi, W=W if pd else 0.0, pd=pd, gstar=gstar, Yb=Yb)


def run(a):
    worst = dict(seg=0, d1=0.0, d3=0.0, nreg=0, nfib=0)
    for signs in itertools.product([-1.0, 1.0], repeat=len(edges)):
        Sg0 = np.zeros((n, n))
        for (k, l), s in zip(edges, signs):
            Sg0[k, l] = Sg0[l, k] = s
        for i in Nset:
            for j in range(n):
                if not A0[i, j] or Sg0[i, j] != 1:
                    continue

                def St(t):
                    S = Sg0.copy()
                    S[i, j] = S[j, i] = t
                    return S

                def phi(t, c):
                    Pp, Pm = mats(St(t), a)
                    o = obs(Pp, Pm, c, i, j, a)
                    return (np.linalg.det(Pp) * np.linalg.det(Pm)) ** p * o["Psi"]

                for c in range(4):
                    worst["nfib"] += 1
                    o1 = obs(*mats(St(1.0), a), c, i, j, a)
                    o2 = obs(*mats(St(-1.0), a), c, i, j, a)
                    good = [o for o in (o1, o2) if o["W"] > 0 and 64 * p * a * o["gstar"] <= 1]
                    if not good:
                        continue
                    worst["nreg"] += 1
                    for t in np.linspace(-2, 2, 21):
                        Pp, Pm = mats(St(t), a)
                        if not (np.linalg.eigvalsh(Pp).min() > 0 and np.linalg.eigvalsh(Pm).min() > 0):
                            worst["seg"] += 1
                    e = 1e-5
                    d1p = (phi(1 + e, c) - phi(1 - e, c)) / (2 * e)
                    d1m = (phi(-1 + e, c) - phi(-1 - e, c)) / (2 * e)
                    scale = (abs(o1["W"] * o1["DPsi"]) + abs(o2["W"] * o2["DPsi"]) +
                             abs(o1["W"] * o1["Psi"]) + abs(o2["W"] * o2["Psi"]) + 1e-300)
                    worst["d1"] = max(worst["d1"], abs(d1p - o1["W"] * o1["DPsi"]) / scale,
                                      abs(d1m - o2["W"] * o2["DPsi"]) / scale)
                    dl = 4e-2
                    sup3 = 0.0
                    for t in np.linspace(-1, 1, 21):
                        fs = [phi(t + k * dl, c) for k in (-2, -1, 1, 2)]
                        sup3 = max(sup3, abs((fs[3] - 2 * fs[2] + 2 * fs[1] - fs[0]) / (2 * dl ** 3)))
                    bound = o1["W"] * o1["Yb"] + o2["W"] * o2["Yb"]
                    worst["d3"] = max(worst["d3"], sup3 / bound)
    return worst


for a in (0.0025, 0.005, 0.0075):
    w = run(a)
    print(f"a={a}: fibres {w['nfib']}, regular {w['nreg']}, seg failures {w['seg']}, "
          f"max err phi'(+-1) - W DPsi, relative to |W Psi| + |W DPsi| {w['d1']:.2e}, max sup|phi'''|/(W Yb + W' Yb') {w['d3']:.2e}")
