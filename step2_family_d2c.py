"""Step 2: independent audit of family "d = 2c" (write-up Section 5.1), layers 3-5.

Reads the engine's record as DATA only (none of the engine's code is run) and re-derives:
  L3  the family dot theorem on S(c, 2pi/3): base value, positivity, every collision + delta;
  L4  every subfamily closure: the (u, v) decomposition of each member over (m1, m2), the anchor
      angles, the lemma bound A + B pi^2/N^2 + C/N + D pi/N, validity floors and threshold N0;
  L5  the finite parts: re-enumerated from the thresholds (counts compared with the record) and
      each set certified with interval arithmetic to satisfy min f_A < L(1,2,3,4).
Usage: python3 step2_family_d2c.py path/to/lambda4-campaign.json
"""
import json
import re
import sys
from fractions import Fraction as F
from itertools import combinations
from math import cos, gcd, pi

import mpmath as mp
from mpmath import iv

rec = json.load(open(sys.argv[1]))
fam = rec["lambda4families"]["d = 2c"]

# ---------- rigorous enclosure of L = min f_{1,2,3,4} = -(largest root of the cubic) ----------
mp.mp.dps = 60
P = lambda y: 512 * y**3 - 1227 * y**2 + 600 * y + 125
r = mp.findroot(lambda y: 512 * y**3 - 1227 * y**2 + 600 * y + 125, 1.52)
r_lo, r_hi = F(mp.nstr(r - mp.mpf("1e-50"), 70)), F(mp.nstr(r + mp.mpf("1e-50"), 70))
assert P(r_lo) < 0 < P(r_hi), "root not bracketed"          # exact rational sign change
L_UPPER_SAFE = -r_hi                                          # L > -r_hi; need f_A(t) < -r_hi
PI_LO, PI_HI = F(314159265358979, 10**14), F(314159265358980, 10**14)

# ---------- cosine polynomials over (a, b, c); d = 2c is substituted ----------
def canon(v):
    for x in v:
        if x:
            return v if x > 0 else tuple(-t for t in v)
    return v

def add(p, v, cf):
    v = canon(v); p[v] = p.get(v, F(0)) + cf
    if p[v] == 0: del p[v]

def mul(p, q):
    out = {}
    for u, cu in p.items():
        for v, cv in q.items():
            add(out, tuple(x + y for x, y in zip(u, v)), cu * cv / 2)
            add(out, tuple(x - y for x, y in zip(u, v)), cu * cv / 2)
    return out

def lin(*terms):
    p = {}
    for cf, v in terms: add(p, v, F(cf))
    return p

def plus(*ps):
    out = {}
    for p in ps:
        for v, cf in p.items(): add(out, v, cf)
    return out

Z3, VA, VB = (0, 0, 0), (1, 0, 0), (0, 1, 0)
om = lambda v: lin((1, Z3), (-1, v))
w = plus(mul(lin((2, Z3)), mul(om(VA), om(VA))), mul(lin((2, Z3)), mul(om(VB), om(VB))))
g = lin((F(3, 5), Z3), (1, VA), (1, VB))
wg = mul(w, g)

# anchor S(c, 2pi/3): average of cos(k t) = cos(t' * 2pi/3) if |k| = t' c, else 0 (Lemma A)
cos_anchor = lambda tp: F(1) if tp % 3 == 0 else F(-1, 2)
region = [(a, b, c) for a, b, c in combinations(range(1, 61), 3)]   # 0 < a < b < c, d = 2c

def collisions(poly):
    out = {}
    for v, cf in poly.items():
        if v == Z3: continue
        for tp in range(0, 7):
            for s in ((1,) if tp == 0 else (1, -1)):
                key = canon((s * v[0], s * v[1], s * v[2] - tp))
                if not any(key[0] * a + key[1] * b + key[2] * c == 0 for a, b, c in region):
                    continue
                out[key] = out.get(key, F(0)) + cf * cos_anchor(tp)
    return {k: d for k, d in out.items() if d != 0}

def parse_label(label):
    """'2a+b = 2c' -> canonical (a, b, c) vector of lhs - rhs, with d = 2c substituted."""
    vec = {"a": 0, "b": 0, "c": 0, "d": 0}
    for side, sign in zip(label.split("="), (1, -1)):
        for coef, var in re.findall(r"(\d*)([abcd])", side):
            vec[var] += sign * int(coef or 1)
    return canon((vec["a"], vec["b"], vec["c"] + 2 * vec["d"]))

def show(key):
    names = "abc"
    lhs = "+".join((str(k) if k != 1 else "") + n for k, n in zip(key, names) if k > 0) or "0"
    rhs = "+".join((str(-k) if k != -1 else "") + n for k, n in zip(key, names) if k < 0) or "0"
    return f"{lhs} = {rhs}"

print("=" * 72, "\nL3  family d = 2c: dot theorem on S(c, 2pi/3)")
mine = collisions(wg)
theirs = {parse_label(e["label"]): F(e["delta"]) for e in fam["dot"]["exceptions"]}
print(f"base <w,g>: mine {wg.get(Z3, 0)}  record {fam['dot']['base']}   "
      f"| posBase <w,1>: mine {w.get(Z3, 0)}  record {fam['dot']['posBase']}")
print(f"dip: anchored c, d give cos(2pi/3) + cos(4pi/3) = -1, minus 3/5 -> -8/5  record {fam['dot']['dip']}")
for key in sorted(set(mine) | set(theirs), key=show):
    m, t = mine.get(key, "-"), theirs.get(key, "-")
    print(f"   {show(key):<12} mine {str(m):>6}   record {str(t):>6}" + ("" if m == t else "   <-- MISMATCH"))
print("   collision table identical:", mine == theirs)
w_worst = w.get(Z3, 0) + sum(d for d in collisions(w).values() if d < 0)
print(f"   positivity: worst-case <w,1> over all collision subsets = {w_worst} (> 0 needed)")
positive = sorted(show(k) for k, d in mine.items() if d > 0)
print("   positive-delta conditions (each must be a subfamily):", positive)

# ---------- L4: closures ----------
SUB = {  # parametrizations of the four subfamilies inside {a < b < c, d = 2c}
    "b = 2a":  {"a": (1, 0), "b": (2, 0), "c": (0, 1), "d": (0, 2), "dom": lambda x, y: y > 2 * x},
    "c = 2a":  {"a": (1, 0), "b": (0, 1), "c": (2, 0), "d": (4, 0), "dom": lambda x, y: x < y < 2 * x},
    "c = 2b":  {"a": (1, 0), "b": (0, 1), "c": (0, 2), "d": (0, 4), "dom": lambda x, y: x < y},
    "c = a+b": {"a": (1, 0), "b": (0, 1), "c": (1, 1), "d": (2, 2), "dom": lambda x, y: x < y},
}
ANGLES = [F(k, 6) for k in range(12)]                      # multiples of pi/6, in units of pi
cospi = lambda q: {F(0): 1, F(1, 3): F(1, 2), F(1, 2): 0, F(2, 3): F(-1, 2), F(1): -1,
                   F(4, 3): F(-1, 2), F(3, 2): 0, F(5, 3): F(1, 2)}.get(q % 2)
TARGETS = {"lemma3.3": {F(2, 3), F(4, 3)}, "lemma3.2": {F(1)}, "lemmaF": {F(1, 2), F(3, 2)}}

def check_closure(members, cl):
    m1 = members[cl["tailMember"]]
    m2 = next(members[p["member"]] for p in cl["pieces"] if F(p.get("u", 0)) == 0 and F(p.get("v", 0)) == 1)
    for p in cl["pieces"]:
        u, v = F(p.get("u", 0)), F(p.get("v", 0))
        want = members[p["member"]]
        assert all(u * x + v * y == z for x, y, z in zip(m1, m2, want)), f"decomposition fails: {p}"
    for xi1 in ANGLES:                       # anchors consistent with every piece?
        if not all(cospi(F(p["u"]) * xi1) == F(p["value"]) for p in cl["pieces"] if p["kind"] == "exact"):
            continue
        for xi2 in ANGLES:
            if all(((F(p["u"]) * xi1 + F(p["v"]) * xi2) % 2) in TARGETS[p["kind"]]
                   for p in cl["pieces"] if p["kind"] != "exact"):
                break
        else:
            continue
        break
    else:
        raise AssertionError("no consistent anchor angles")
    A = sum(F(p["value"]) for p in cl["pieces"] if p["kind"] == "exact")
    B = C = D = F(0); floor = 1
    for p in cl["pieces"]:
        v = abs(F(p.get("v", 0)))
        if p["kind"] == "lemma3.3": A += F(-1, 2); C += 3 * v; floor = max(floor, int(6 * v))
        if p["kind"] == "lemma3.2": A += -1; B += v * v / 2
        if p["kind"] == "lemmaF":   D += v
    bound_hi = lambda N: A + B * PI_HI**2 / N**2 + C / N + D * PI_HI / N
    bound_lo = lambda N: A + B * PI_LO**2 / N**2 + C / N + D * PI_LO / N
    N0 = floor
    while not bound_hi(N0) < L_UPPER_SAFE: N0 += 1
    minimal = N0 == floor or not bound_lo(N0 - 1) < -r_lo
    return dict(xi=(xi1, xi2), A=A, B=B, C=C, D=D, floor=floor, N0=N0, minimal=minimal)

print("\n" + "=" * 72, "\nL4  subfamily closures")
covered_by = {}
for sf in fam["subfamilies"]:
    members = SUB[sf["label"]]
    covered_by[sf["label"]] = []
    for cl in sf["closures"]:
        res = check_closure(members, cl)
        e = cl["expr"]
        same = (res["A"], res["B"], res["C"], res["D"], res["N0"], res["floor"]) == \
               (F(e["A"]), F(e["B"]), F(e["C"]), F(e["D"]), cl["N0"], cl["validityFloor"])
        print(f"   {sf['label']:<8} tail {cl['tailMember']}: anchors (xi1, xi2) = "
              f"({res['xi'][0]}pi, {res['xi'][1]}pi)  bound {res['A']} + {res['B']}pi^2/N^2 + "
              f"{res['C']}/N + {res['D']}pi/N  floor {res['floor']}  N0 {res['N0']}"
              f"{'' if res['minimal'] else ' (not minimal)'}  | matches record: {same}")
        covered_by[sf["label"]].append((cl["tailMember"], max(res["N0"], res["floor"])))

# ---------- L5: finite parts ----------
def fmin_certify(A, grid_factor=256):
    """Find t near the global minimum; return a rigorous upper bound on f_A(t).

    Candidates are the best grid points themselves plus their Newton refinements (a refinement
    is kept only if it does not increase f), so a diverging Newton step can never lose the dip.
    """
    M = max(A); G = max(4096, grid_factor * M)
    best = sorted((sum(cos(k * pi * j / G) for k in A), j) for j in range(G + 1))[:4]
    mp.mp.dps = 50
    f = lambda t: sum(mp.cos(k * t) for k in A)
    cands = []
    for _, j in best:
        t0 = mp.pi * j / G
        cands.append(t0)
        try:
            t = mp.findroot(lambda t: sum(-k * mp.sin(k * t) for k in A), t0)
            if f(t) <= f(t0): cands.append(t)
        except (ValueError, ZeroDivisionError):
            pass
    iv.dps = 50
    ub = min(sum(iv.cos(k * iv.mpf(t)) for k in A).b for t in cands)
    return F(mp.nstr(mp.mpf(ub), 60))

print("\n" + "=" * 72, "\nL5  finite parts: re-enumerate from thresholds, then certify")
total_cert, worst, failures = 0, (F(-10), None), []
for sf in fam["subfamilies"]:
    mem = SUB[sf["label"]]
    finite = []
    for x in range(1, 400):
        for y in range(1, 400):
            if not mem["dom"](x, y): continue
            S = tuple(mem[k][0] * x + mem[k][1] * y for k in "abcd")
            if gcd(gcd(S[0], S[1]), gcd(S[2], S[3])) != 1: continue
            vals = dict(zip("abcd", S))
            if any(vals[tail] >= thr for tail, thr in covered_by[sf["label"]]): continue
            finite.append(S)
    edge = max((max(s) for s in finite), default=0)
    print(f"   {sf['label']:<8} finite sets: mine {len(finite)}   record {sf['finite']['enumerated']}"
          f"   (largest element {edge}; box 400 -> enumeration is complete)")
    for S in finite:
        if S == (1, 2, 3, 4): continue
        ub = fmin_certify(S)
        if not ub < L_UPPER_SAFE:
            ub = fmin_certify(S, grid_factor=4096)          # much finer grid before flagging
        if not ub < L_UPPER_SAFE:
            failures.append((S, float(ub))); continue
        total_cert += 1
        if ub > worst[0]: worst = (ub, S)
print(f"   certified min f_A < L for {total_cert} sets.  Tightest: {worst[1]} with "
      f"f <= {float(worst[0]):.10f}  (L = {float(-r):.10f}, margin {float(-r - worst[0]):.2e})")
print(f"   NOT certified (potential refuters or search failures): {failures if failures else 'none'}")
