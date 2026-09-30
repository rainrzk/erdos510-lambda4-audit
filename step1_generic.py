"""Step 1: independently re-derive Section 3 ("the generic case") of the lambda(4) write-up.

Write-up claim: on S(d, pi) = {t : d t = pi mod 2pi}, with
    w = (1 - cos at) + (1 - cos bt) + 2(1 - cos ct)^2,   g = 3/5 + cos at + cos bt + cos ct,
the averages are <w, g>_S = 0 and <w, 1>_S = 5 when no "collision" holds, and exactly
fourteen linear collision conditions change <w, g>_S, with the deltas in its table.

Independent method (no code shared with the engine):
  * represent cosine polynomials as {frequency vector over (a, b, c): Fraction} and multiply
    with cos x cos y = (cos(x+y) + cos(x-y)) / 2;
  * Lemma A: over S(d, pi), the average of cos(k t) is cos(t' pi) = (-1)^t' if |k| = t' d, else 0;
  * enumerate every condition |k| = t' d that some 4-set 0 < a < b < c < d actually satisfies
    (brute force), and sum each condition's contributions.
Then a direct numerical check: every gcd-1 set with d <= D that activates no positive-delta
condition must have min over S(d, pi) of f_A <= -8/5.
"""
from fractions import Fraction as F
from itertools import combinations
from math import cos, gcd, pi

VARS = "abc"


def canon(v):
    """cos is even: store v and -v under one key (first nonzero coefficient positive)."""
    for x in v:
        if x:
            return v if x > 0 else tuple(-t for t in v)
    return v


def add(p, v, coef):
    v = canon(v)
    p[v] = p.get(v, F(0)) + coef
    if p[v] == 0:
        del p[v]


def mul(p, q):
    out = {}
    for u, cu in p.items():
        for v, cv in q.items():
            add(out, tuple(x + y for x, y in zip(u, v)), cu * cv / 2)
            add(out, tuple(x - y for x, y in zip(u, v)), cu * cv / 2)
    return out


def lin(*terms):
    p = {}
    for coef, v in terms:
        add(p, v, F(coef))
    return p


ZERO, A_, B_, C_ = (0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1)
one_minus = lambda v: lin((1, ZERO), (-1, v))
w = lin()
for part in (one_minus(A_), one_minus(B_), mul(lin((2, ZERO)), mul(one_minus(C_), one_minus(C_)))):
    for v, cf in part.items():
        add(w, v, cf)
g = lin((F(3, 5), ZERO), (1, A_), (1, B_), (1, C_))
wg = mul(w, g)

print("<w,1>_S base =", w.get(ZERO, 0), "   <w,g>_S base =", wg.get(ZERO, 0))

# Enumerate feasible collision conditions |k| = t' d over small sets.
D = 40
sets = [s for s in combinations(range(1, D + 1), 4)]
conds = {}  # normalized (a,b,c,d) vector -> {"delta": F, "example": set}
for v, coef in wg.items():
    if v == ZERO:
        continue
    for tp in range(1, 5):
        for sgn in (1, -1):
            key = tuple(sgn * x for x in v) + (-tp,)  # sgn*(v.x) - tp*d = 0
            ex = next((s for s in sets if sum(k * x for k, x in zip(key, s)) == 0), None)
            if ex is None:
                continue
            entry = conds.setdefault(key, {"delta": F(0), "example": ex})
            entry["delta"] += coef * (-1) ** tp


def show(key):
    lhs = "+".join((f"{k}" if k != 1 else "") + n for k, n in zip(key[:3], VARS) if k > 0)
    rhs = "+".join([(f"{-k}" if k != -1 else "") + n for k, n in zip(key[:3], VARS) if k < 0]
                   + [(f"{-key[3]}" if key[3] != -1 else "") + "d"])
    return f"{lhs} = {rhs}"


claimed = {  # the write-up's table, as (a, b, c, d) vectors of lhs - rhs = 0
    (2, 0, 0, -1): F(1, 2), (0, 2, 0, -1): F(1, 2), (-1, 0, 2, -1): F(-1, 2),
    (0, -1, 2, -1): F(-1, 2), (0, 0, 2, -1): F(7, 5), (0, 0, 3, -2): F(1, 2),
    (0, 0, 3, -1): F(-1, 2), (1, 0, 2, -2): F(1, 2), (1, 0, 2, -1): F(-1, 2),
    (1, 1, 0, -1): F(1), (1, 0, 1, -1): F(5, 2), (0, 1, 2, -2): F(1, 2),
    (0, 1, 2, -1): F(-1, 2), (0, 1, 1, -1): F(5, 2),
}
print(f"\n{'condition':<14}{'delta (mine)':>14}{'claimed':>10}  example")
for key in sorted(conds, key=show):
    mine, theirs = conds[key]["delta"], claimed.get(key, "MISSING")
    flag = "" if mine == theirs else "   <-- MISMATCH"
    print(f"{show(key):<14}{str(mine):>14}{str(theirs):>10}  {conds[key]['example']}{flag}")
print("conditions found:", len(conds), " claimed:", len(claimed),
      " identical:", {k: v['delta'] for k, v in conds.items() if v['delta'] != 0} ==
      {k: v for k, v in claimed.items()})

# Direct numerical check of the generic closure on small sets.
positive = [k for k, v in conds.items() if v["delta"] > 0]
worst, n_checked = -9.0, 0
for s in sets:
    if gcd(gcd(s[0], s[1]), gcd(s[2], s[3])) != 1:
        continue
    if any(sum(k * x for k, x in zip(key, s)) == 0 for key in positive):
        continue
    a, b, c_, d = s
    best = min(sum(cos(k * (pi + 2 * pi * j) / d) for k in s) for j in range(d))
    worst, n_checked = max(worst, best), n_checked + 1
print(f"\ngeneric-case sets with d <= {D}: {n_checked};  largest min over S(d,pi) = {worst:.6f}"
      f"  (claim: <= -1.6)")
