"""AUDIT-C parameter checks for (D1)-(D10) (exact arithmetic in mpmath; d up to 1e200).

Checks
  * the closed form of Lbar = d a^2 s^2 in (D2) and d(r-1)(1-r Lbar) = 1/p + O(eta0);
  * the explicit lower bound  d(r-1)(1-r Lbar) >= 1/p - 2*eta0  (used to fix d0);
  * delta <= c0^{17/6} p^{-5/2} (D5), the exponent arithmetic of (D6)-(D7), E_lambda = O(1);
  * the exponent constant of (E6);
  * the D10 error terms in 'margin units' (multiply by p: margin d(r-1)(1-rL) ~ 1/p, D3 has 2a^2 R).
"""
import mpmath as mp

mp.mp.dps = 500


def params(d, c0):
    d = mp.mpf(d)
    q = d - 1
    p = mp.floor(c0 * d**(mp.mpf(2) / 17))
    Delta = 4 / p
    # q eta^2/(1-eta) = Delta  ->  q eta^2 + Delta eta - Delta = 0
    eta0 = (-Delta + mp.sqrt(Delta**2 + 4 * q * Delta)) / (2 * q)
    R2 = 4 * q + Delta
    a2 = 1 / R2
    s = (2 - eta0) / (1 - (1 - eta0) / q)
    r = 1 + eta0 / 2
    Lbar = d * a2 * s**2
    Lbar_cf = d * q * (1 - eta0) / (q - 1 + eta0)**2
    return dict(d=d, q=q, p=p, eta0=eta0, a2=a2, s=s, r=r, Lbar=Lbar, Lbar_cf=Lbar_cf)


print(f"{'log10 d':>8} {'c0':>5} {'p':>8} {'Lbar-cf':>9} {'p*d(r-1)(1-rL)':>15} "
      f"{'margin>=1/p-2eta':>16} {'(r-1)sqrt(pd)':>13}")
for c0 in [1, mp.mpf('0.1')]:
    for e in [20, 30, 40, 60, 100, 200]:
        P = params(mp.mpf(10)**e, c0)
        if P['p'] < 3:
            continue
        m = P['d'] * (P['r'] - 1) * (1 - P['r'] * P['Lbar'])
        print(f"{e:>8} {float(c0):>5} {int(P['p']):>8} {float(P['Lbar'] - P['Lbar_cf']):>9.1e} "
              f"{float(P['p'] * m):>15.10f} {str(m >= 1 / P['p'] - 2 * P['eta0']):>16} "
              f"{float((P['r'] - 1) * mp.sqrt(P['p'] * P['d'])):>13.6f}")

print("\nExponent checks (c0 = 1, kappa0 = 1); all should tend to 0 or stay O(1):")
hdr = ["log10 d", "p", "delta*p^2.5/c0^(17/6)", "p^9 delta/d", "p^12/d^2", "E_lam~p^5 sqrt(p delta/d)",
       "eta_BL", "p*p^5/d", "p*p^6/d", "p*p^7/d", "p*Gamma", "p*Gamma*sqrt(p)"]
print(" | ".join(hdr))
for e in [20, 30, 40, 60, 100, 200]:
    c0 = 1
    P = params(mp.mpf(10)**e, c0)
    d, p = P['d'], P['p']
    delta = (P['r'] - 1) + p**4 / d + (p / d)**(mp.mpf(1) / 3)
    h = p**-4
    Gamma = p**4 * mp.sqrt(p * delta / d)
    vals = [delta * p**2.5 / mp.mpf(c0)**(mp.mpf(17) / 6), p**9 * delta / d, p**12 / d**2,
            p**5 * mp.sqrt(p * delta / d), p / (d * h) + p**4 / d, p * p**5 / d, p * p**6 / d,
            p * p**7 / d, p * Gamma, p * Gamma * mp.sqrt(p)]
    print(f"{e:>7} | {int(p):>6} | " + " | ".join(f"{float(v):.3e}" for v in vals))

print("\nD9a/E_row scale in the endgame unit p^{-1} (S ~ 4): with GR1 (rho_r = delta/p) vs without (rho_r = delta)")
print("  columns: log10 d, c0, p*Gamma, p*p^5 sqrt(5 delta/(p d)) [GR1], p*p^5 sqrt(5 delta/d) [no GR1], c0^(17/3)")
for c0 in [mp.mpf(1), mp.mpf('0.001')]:
    for e in [60, 200, 1000]:
        P = params(mp.mpf(10)**e, c0)
        d, p = P['d'], P['p']
        delta = (P['r'] - 1) + p**4 / d + (p / d)**(mp.mpf(1) / 3)
        Gamma = p**4 * mp.sqrt(p * delta / d)
        withGR = p**5 * mp.sqrt(5 * delta / (p * d))
        noGR = p**5 * mp.sqrt(5 * delta / d)
        print(f"  {e:>5} {float(c0):>6} {float(p * Gamma):.3e} {float(p * withGR):.3e} {float(p * noGR):.3e}"
              f" {float(c0**(mp.mpf(17) / 3)):.3e}")

print("\n(E6) exponent: log(p 40^p (Cp)^{4k+4} d^{-k}) / p with k = ceil(16p/log d), C = 1, 10")
for C in [1, 10]:
    for e in [30, 60, 100, 200, 400]:
        P = params(mp.mpf(10)**e, 1)
        d, p = P['d'], P['p']
        k = mp.ceil(16 * p / mp.log(d))
        val = (mp.log(p) + p * mp.log(40) + (4 * k + 4) * mp.log(C * p) - k * mp.log(d)) / p
        print(f"  C={C:>3} log10 d={e:>4} p={int(p):>10} k*={int(k):>8}  exponent/p = {float(val):.4f}")
print("  limit as d->inf (p<=d^{2/17}): log 40 - 16*(1 - 8/17) =", float(mp.log(40) - 16 * (1 - mp.mpf(8) / 17)))
