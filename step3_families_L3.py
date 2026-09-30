"""Step 3: layer-3 audit (family dot theorems) for the families that carry a single dot theorem:
d = 2c, d = 2a, d = b+c, d = a+b, d = a+c, 2d = 2c+a  (write-up Sections 5.1-5.6).

Parametrization-free: everything is recomputed in the original variables (a, b, c, d) with the
family relation substituted. The record's cone-parameter labels are NOT decoded; instead each
record exception is matched through its example set: the example must satisfy one of my derived
conditions carrying exactly the same delta, and the two tables must have equal size.
Weights w, targets g and anchors are taken from the write-up's prose (Section 5); g's constant is
the one that reproduces the stated dip.
Usage: python3 step3_families_L3.py path/to/lambda4-campaign.json
"""
import json
import sys
from fractions import Fraction as F
from itertools import combinations



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


def plus(*ps):
    out = {}
    for p in ps:
        for v, cf in p.items(): add(out, v, cf)
    return out


def const(x, n): return {(0,) * n: F(x)}
def cosp(v): return {canon(v): F(1)}
def one_minus_sq(v, n):  # 2 (1 - cos v)^2
    om = plus(const(1, n), {canon(v): F(-1)})
    return mul(const(2, n), mul(om, om))

COS_TABLE = {0: F(1), 1: F(1, 2), 2: F(-1, 2), 3: F(-1), 4: F(-1, 2), 5: F(1, 2)}  # cos(k pi/3)
def cos_multiple(tp, xi_sixths):
    """cos(tp * xi) for xi a multiple of pi/3 given in units of pi/6 (must be even)."""
    return COS_TABLE[(tp * xi_sixths // 2) % 6]


def audit(name, forms, region, anchor, xi_sixths, weight_members, g_members, gconst):
    """forms: member -> integer vector over the base variables; region: list of base points."""
    n = len(next(iter(forms.values())))
    w = plus(*[one_minus_sq(forms[m], n) for m in weight_members])
    g = plus(const(gconst, n), *[cosp(forms[m]) for m in g_members])
    wg = mul(w, g)
    m = anchor
    # anchored members: every member whose frequency is identically t' * m
    anchored = []
    for mem, v in forms.items():
        for tp in range(1, 5):
            if tuple(tp * x for x in m) == v:
                anchored.append((mem, tp))
    dip = sum(cos_multiple(tp, xi_sixths) for _, tp in anchored) - gconst

    def conds(poly):
        out = {}
        for v, cf in poly.items():
            if not any(v): continue
            if any(canon(tuple(tp * x for x in m)) == v for tp in range(1, 8)):
                continue   # identically a multiple of the anchor: part of the base, not a collision
            for tp in range(0, 8):
                for s in ((1,) if tp == 0 else (1, -1)):
                    key = tuple(s * x - tp * y for x, y in zip(v, m))
                    if not any(key):
                        continue
                    key = canon(key)
                    if not any(sum(k * x for k, x in zip(key, pt)) == 0 for pt in region):
                        continue
                    out.setdefault(key, F(0))
                    out[key] += cf * cos_multiple(tp, xi_sixths)
        return {k: d for k, d in out.items() if d != 0}

    def base_value(poly):   # constant term plus every frequency identically on the anchor lattice
        tot = poly.get((0,) * n, F(0))
        for v, cf in poly.items():
            for tp in range(1, 8):
                if canon(tuple(tp * x for x in m)) == v and any(v):
                    tot += cf * cos_multiple(tp, xi_sixths)
        return tot

    mine = conds(wg)
    fam = rec[name]["dot"]
    print(f"\n### family {name}: anchor {anchor} (xi = {xi_sixths}pi/6), anchored {anchored}")
    print(f"   base <w,g>: mine {base_value(wg)}  record {fam['base']}  | posBase <w,1>: mine "
          f"{base_value(w)}  record {fam['posBase']}  | dip: mine {dip}  record {fam['dip']}")
    # match record exceptions through their examples
    to_base = forms["_from_abcd"]
    exc = fam["exceptions"]
    edges = []   # record exception i -> derived conditions its example satisfies with equal delta
    for e in exc:
        ex = e["example"]; pt = to_base(ex["a"], ex["b"], ex["c"], ex["d"])
        edges.append([k for k in mine if sum(c * x for c, x in zip(k, pt)) == 0 and mine[k] == F(e["delta"])])
    match = {}   # derived condition -> record index (Kuhn's augmenting paths: perfect matching?)
    def augment(i, seen):
        for k in edges[i]:
            if k in seen: continue
            seen.add(k)
            if k not in match or augment(match[k], seen):
                match[k] = i; return True
        return False
    matched = sum(augment(i, set()) for i in range(len(exc)))
    ok = matched == len(exc) == len(mine)
    for i, e in enumerate(exc):
        if i not in match.values():
            print(f"   record exception {e['label']} ({e['delta']}): NO matching derived condition")
    pos = sum(1 for d in mine.values() if d > 0)
    w_worst = base_value(w) + sum(d for d in conds(w).values() if d < 0)
    print(f"   conditions: mine {len(mine)}  record {len(fam['exceptions'])}  one-to-one match: {ok}"
          f"   | positive-delta: {pos}  record subfamilies: {len(rec[name]['subfamilies'])}"
          f"   | worst-case <w,1> = {w_worst}")


if __name__ == "__main__":
    rec = json.load(open(sys.argv[1]))["lambda4families"]
    pts3 = lambda lim, pred: [p for p in combinations(range(1, lim), 3) if pred(*p)]

    # d = 2c: base variables (a, b, c)
    audit("d = 2c", {"a": (1, 0, 0), "b": (0, 1, 0), "c": (0, 0, 1), "d": (0, 0, 2),
                     "_from_abcd": lambda a, b, c, d: (a, b, c)},
          pts3(61, lambda a, b, c: True), anchor=(0, 0, 1), xi_sixths=4,
          weight_members="ab", g_members="ab", gconst=F(3, 5))
    # d = 2a: region a < b < c < 2a
    audit("d = 2a", {"a": (1, 0, 0), "b": (0, 1, 0), "c": (0, 0, 1), "d": (2, 0, 0),
                     "_from_abcd": lambda a, b, c, d: (a, b, c)},
          pts3(81, lambda a, b, c: c < 2 * a), anchor=(1, 0, 0), xi_sixths=4,
          weight_members="bc", g_members="bc", gconst=F(3, 5))
    # d = b+c
    audit("d = b+c", {"a": (1, 0, 0), "b": (0, 1, 0), "c": (0, 0, 1), "d": (0, 1, 1),
                      "_from_abcd": lambda a, b, c, d: (a, b, c)},
          pts3(61, lambda a, b, c: True), anchor=(0, 1, 1), xi_sixths=6,
          weight_members="a", g_members="abc", gconst=F(3, 5))
    # d = a+b: region c < a+b
    audit("d = a+b", {"a": (1, 0, 0), "b": (0, 1, 0), "c": (0, 0, 1), "d": (1, 1, 0),
                      "_from_abcd": lambda a, b, c, d: (a, b, c)},
          pts3(61, lambda a, b, c: c < a + b), anchor=(1, 1, 0), xi_sixths=6,
          weight_members="c", g_members="abc", gconst=F(3, 5))
    # d = a+c
    audit("d = a+c", {"a": (1, 0, 0), "b": (0, 1, 0), "c": (0, 0, 1), "d": (1, 0, 1),
                      "_from_abcd": lambda a, b, c, d: (a, b, c)},
          pts3(61, lambda a, b, c: True), anchor=(1, 0, 1), xi_sixths=6,
          weight_members="b", g_members="abc", gconst=F(3, 5))
    # 2d = 2c+a: a = 2t, d = c + t; base variables (t, b, c) with 2t < b < c
    audit("2d = 2c+a", {"a": (2, 0, 0), "b": (0, 1, 0), "c": (0, 0, 1), "d": (1, 0, 1),
                        "_from_abcd": lambda a, b, c, d: (a // 2, b, c)},
          [(t, b, c) for t in range(1, 31) for b in range(2 * t + 1, 61) for c in range(b + 1, 61)],
          anchor=(1, 0, 1), xi_sixths=6, weight_members="a", g_members="abc", gconst=F(3, 5))
