"""AUDIT-B: finite-difference check of the exact identities (W2), (W3) of the weak loop.

P^tau = diag(Z) + tau*a*A_sigma (+ h I);  U = X_eps D_f X_nu;
F_ji = (X_eps)_ii U_ji - (X_eps)_ji U_ii.
(W2): U_ii - f_i (X_eps)_ii (X_nu)_ii = -eps*a*sum_{j~i} sigma_ij F_ji
(W3): dF_ji/dsigma_ij = -a{2 eps (X_eps)_ij F_ji + nu (X_nu)_ij F_ji
                          + nu (X_eps)_ii (X_nu)_ii U_jj - nu (X_nu)_ii (X_eps)_ij U_ij}
"""
import numpy as np
rng = np.random.default_rng(5)
n, a, h = 7, 0.3, 0.2
Adj = np.triu((rng.random((n, n)) < 0.6).astype(float), 1); Adj = Adj + Adj.T
S = np.triu(rng.choice([-1.0, 1.0], (n, n)), 1); S = (S + S.T) * Adj
Zp, Zm = 1 + rng.random(n), 1 + rng.random(n)
f = rng.random(n)

def mats(S, eps, nu):
    Pe = np.diag(Zp if eps > 0 else Zm) + eps * a * S + h * np.eye(n)
    Pn = np.diag(Zp if nu > 0 else Zm) + nu * a * S + h * np.eye(n)
    Xe, Xn = np.linalg.inv(Pe), np.linalg.inv(Pn)
    U = Xe @ np.diag(f) @ Xn
    return Xe, Xn, U

def Fm(Xe, U):
    return np.diag(Xe)[None, :] * U - Xe * np.diag(U)[None, :]   # F[j,i]

worst2 = worst3 = 0.0
for eps in (1, -1):
    for nu in (1, -1):
        Xe, Xn, U = mats(S, eps, nu)
        F = Fm(Xe, U)
        for i in range(n):
            lhs = U[i, i] - f[i] * Xe[i, i] * Xn[i, i]
            rhs = -eps * a * sum(S[i, j] * F[j, i] for j in range(n) if Adj[i, j])
            worst2 = max(worst2, abs(lhs - rhs))
        for i in range(n):
            for j in range(n):
                if not Adj[i, j]:
                    continue
                E = np.zeros((n, n)); E[i, j] = E[j, i] = 1.0
                t = 1e-6
                Fp = Fm(*[m for k, m in enumerate(mats(S + t * E, eps, nu)) if k != 1])[j, i]
                Fq = Fm(*[m for k, m in enumerate(mats(S - t * E, eps, nu)) if k != 1])[j, i]
                fd = (Fp - Fq) / (2 * t)
                pred = -a * (2 * eps * Xe[i, j] * F[j, i] + nu * Xn[i, j] * F[j, i]
                             + nu * Xe[i, i] * Xn[i, i] * U[j, j] - nu * Xn[i, i] * Xe[i, j] * U[i, j])
                worst3 = max(worst3, abs(fd - pred))
print("max |W2 residual| =", worst2)
print("max |W3 residual| =", worst3)
