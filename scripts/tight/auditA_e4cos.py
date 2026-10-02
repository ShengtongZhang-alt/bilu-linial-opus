"""AUDIT-A: sharp analytic test of (E4) on f(x) = cos(<lam, x>) in n = 1,2,3 coordinates.

G f = exp(-|lam|^2/2), R f = prod cos(lam_i), d^{2j} f = (-1)^{|j|} lam^{2j} f, sup |d^{2j} f| = lam^{2j}.
Check |G f - sum_{|j|_g<=k} c_j R d^{2j} f| <= K * sum_{|j|_g=k+1} lam^{2j}, K = 1/8 + cosh(1) - 1.
"""
import itertools
import math
from fractions import Fraction as Fr


def cj_list(n):
    c = []
    for m in range(n + 1):
        val = Fr(1, 2**m * math.factorial(m))
        for j in range(m):
            val -= c[j] / math.factorial(2 * m - 2 * j)
        c.append(val)
    return [float(x) for x in c]

c = cj_list(30)
K = 1 / 8 + math.cosh(1) - 1
worst = 0.0
for lam in [(1.3,), (0.9, 0.7), (1.1, 0.5, 0.8), (1.5, 1.5)]:
    n = len(lam)
    Gf = math.exp(-sum(x * x for x in lam) / 2)
    Rf = math.prod(math.cos(x) for x in lam)
    allowed = [0] + list(range(2, 14))
    for k in range(0, 7):
        ret = 0.0
        rem = 0.0
        for j in itertools.product(allowed, repeat=n):
            g = sum(ji - 1 for ji in j if ji > 0)
            mono = math.prod(x ** (2 * ji) for x, ji in zip(lam, j))
            if g <= k:
                ret += math.prod(c[ji] for ji in j) * (-1) ** sum(j) * mono * Rf
            elif g == k + 1:
                rem += mono
        err = abs(Gf - ret)
        worst = max(worst, err / (K * rem))
        print(f"lam={lam} k={k}: |Gf - retained| = {err:.3e}   K*sum lam^(2j) = {K*rem:.3e}")
print("max ratio error/bound =", worst, "(<= 1 required)")
