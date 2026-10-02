"""AUDIT-A: (E6) and the parameter regime with explicit constants.

E6 (explicit form used in AUDIT_A.md):
   p * 40^p * (C1 p)^(4k+4) * C2^(k+1) * d^(-k) <= exp(-p),   k = ceil(16 p / log d),
for all p with  P_LO(d) := 120 log d <= p <= d^(1/7)  and  log d >= LOGD0.
Also checks: 8k+12 <= p/2 (moment orders), 4k+4 <= p-3 (regularity),
and the closure inequalities p^5/d <= u, p^4/d <= u, p^2/d <= u^2, p^9/d^2 <= u^2,
eps <= u, exp(-p) <= u^2 with u = (p/d)^(1/3).
Work with logs: log d = Ld, log p = Lp.
"""
import math

C1, C2 = 8.0, 8.0


def log_lhs(Lp, Ld):
    p = math.exp(Lp)
    k = math.ceil(16 * p / Ld)
    return Lp + p * math.log(40) + (4 * k + 4) * (math.log(C1) + Lp) + (k + 1) * math.log(C2) - k * Ld


def check(Ld, samples=400):
    lo = math.log(120 * Ld)
    hi = Ld / 7
    if lo > hi:
        return None
    worst = -1e300
    for t in range(samples + 1):
        Lp = lo + (hi - lo) * t / samples
        p = math.exp(Lp)
        k = math.ceil(16 * p / Ld)
        val = log_lhs(Lp, Ld) + p          # want <= 0
        worst = max(worst, val / p)
        if not (8 * k + 12 <= p / 2 and 4 * k + 4 <= p - 3):
            return float("inf")   # regime (moment orders / regularity) fails
        # closure inequalities, in logs (u = (p/d)^(1/3))
        Lu = (Lp - Ld) / 3
        assert 5 * Lp - Ld <= Lu + 1e-9 and 4 * Lp - Ld <= Lu
        assert 2 * Lp - Ld <= 2 * Lu and 9 * Lp - 2 * Ld <= 2 * Lu
        assert -0.5 * (Lp + math.log(math.exp(Ld) - 1) if Ld < 700 else Lp + Ld) <= Lu  # eps <= (pq)^(-1/2) <= u
        assert -p <= 2 * Lu
    return worst

for Ld in [300, 350, 400, 500, 800, 1500, 4000]:
    w = check(Ld)
    print(f"log d = {Ld:5d}: max_p [log LHS(E6) + p]/p = {w:.4f}  (<= 0 required)")

# threshold search
lo, hi = 50.0, 2000.0
for _ in range(60):
    mid = (lo + hi) / 2
    w = check(mid, 200)
    if w is not None and w <= 0 and all((check(mid + dd, 100) or 1) <= 0 for dd in (5, 50, 300)):
        hi = mid
    else:
        lo = mid
print(f"E6 with C1=C2=8 holds for log d >= ~{hi:.0f} (sampled); AUDIT_A uses LOGD0 = 400")
# asymptotic slope
print("asymptotic coefficient of p: log40 + 1 - 16 + 64/7 =", math.log(40) + 1 - 16 + 64 / 7)
