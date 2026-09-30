"""Step 7: full audit of family 2d = 3c (write-up Section 5.9): layers 3, 4, 5.

Parity c = 2*gam, so d = 3*gam. Region a < b < c. Cones:
  W1 : b < gam                       chain (a, b-a, gam-b)
  W2 : b = gam                       closed directly
  W3 : b > gam, p = b - gam; split a vs p, then j = a - p vs p:
       W3a a < p (3D) | W3b a = p (2D) | W3c j < p (3D) | W3d j = p (2D) | W3e j > p (3D)
L3: dot on S(gam, pi/3) with the LINEAR weight w = (1-cos a) + (1-cos b), g = 1/10 + cos a + cos b.
    Chain-variable orders are searched over all permutations and the matching one reported.
L4/L5: W2, X1 (3 cones + 2 rays), X2, X3, X4 closures; the four reduced rays certified directly;
    X5 is a delegation to family d = a+b.
Usage: python3 step7_family_2d3c.py path/to/lambda4-campaign.json
"""
import json
import sys
from fractions import Fraction as F
from itertools import permutations

from audit_lib import L_UPPER_SAFE, certify, check_closure, finite_part
from step3_families_L3 import add, canon, const, cosp, cos_multiple, mul, plus

fam = json.load(open(sys.argv[1]))["lambda4families"]["2d = 3c"]
XI = 2   # pi/3 in units of pi/6


def dot_tables(forms, anchor, region):
    """forms: a, b as vectors over the cone's base variables; anchor = vector of gam."""
    n = len(anchor)
    w = plus(const(2, n), {canon(forms["a"]): F(-1)}, {canon(forms["b"]): F(-1)})
    g = plus(const(F(1, 10), n), cosp(forms["a"]), cosp(forms["b"]))
    wg = mul(w, g)
    def on_lattice(v):   # frequency identically t' * anchor?
        for tp in range(1, 8):
            if canon(tuple(tp * x for x in anchor)) == v: return tp
        return None
    def base(poly):
        tot = poly.get((0,) * n, F(0))
        for v, cf in poly.items():
            tp = on_lattice(v) if any(v) else None
            if tp: tot += cf * cos_multiple(tp, XI)
        return tot
    conds = {}
    for v, cf in wg.items():
        if not any(v) or on_lattice(v): continue
        for tp in range(0, 8):
            for s in ((1,) if tp == 0 else (1, -1)):
                key = tuple(s * x - tp * y for x, y in zip(v, anchor))
                if not any(key): continue
                key = canon(key)
                if not any(sum(k * x for k, x in zip(key, pt)) == 0 for pt in region): continue
                conds[key] = conds.get(key, F(0)) + cf * cos_multiple(tp, XI)
    return base(wg), base(w), {k: d for k, d in conds.items() if d != 0}


# base variables (a, b, gam) for 3D cones
P3 = [(a, b, gm) for gm in range(2, 45) for b in range(1, 2 * gm) for a in range(1, b)]
REG = {
    "W1":  [q for q in P3 if q[1] < q[2]],
    "W3a": [q for q in P3 if q[1] > q[2] and q[0] < q[1] - q[2]],
    "W3c": [q for q in P3 if q[1] > q[2] and q[0] > q[1] - q[2] and q[0] - (q[1] - q[2]) < q[1] - q[2]],
    "W3e": [q for q in P3 if q[1] > q[2] and q[0] > q[1] - q[2] and q[0] - (q[1] - q[2]) > q[1] - q[2]],
}
# chain parametrizations: (a, b, gam) as forms over chain variables (x1, x2, x3)
CHAIN3 = {
    "W1":  {"a": (1, 0, 0), "b": (1, 1, 0), "gam": (1, 1, 1)},          # (a, b-a, gam-b)
    "W3a": {"a": (1, 0, 0), "b": (2, 2, 1), "gam": (1, 1, 1)},          # (a, p-a, gam-p)
    "W3c": {"a": (2, 1, 0), "b": (2, 2, 1), "gam": (1, 1, 1)},          # (j, p-j, gam-p)
    "W3e": {"a": (2, 1, 0), "b": (2, 1, 1), "gam": (1, 1, 1)},          # (p, j-p, gam-j)
}


def pull(key, chain, order):
    cols = [chain["a"], chain["b"], chain["gam"]]
    vec = [sum(key[i] * cols[i][j] for i in range(3)) for j in range(len(order))]
    return canon(tuple(vec[j] for j in order))


def record_table(cone):
    return {canon(tuple(int(x) for x in e["key"].split(","))): F(e["delta"])
            for e in fam["cones"][cone]["exceptions"]}

print("L3  dot on S(gam, pi/3), linear weight")
positive = {}
for cone in ("W1", "W3a", "W3c", "W3e"):
    b0, p0, mine = dot_tables({"a": (1, 0, 0), "b": (0, 1, 0)}, (0, 0, 1), REG[cone])
    theirs = record_table(cone)
    hit = next((o for o in permutations(range(3))
                if {pull(k, CHAIN3[cone], o): d for k, d in mine.items()} == theirs), None)
    print(f"   {cone}: base mine {b0} record {fam['cones'][cone]['base']} | <w,1> {p0} | conditions mine "
          f"{len(mine)} record {len(theirs)} | identical (chain order {hit}): {hit is not None}")
    positive[cone] = {k: d for k, d in mine.items() if d > 0}

# 2D cones: W3b (a = p, i.e. b = a + gam; vars (a, gam)); W3d (a = 2p, b = gam + p; vars (p, gam))
P2 = [(x, gm) for gm in range(2, 60) for x in range(1, gm)]
for cone, forms in (("W3b", {"a": (1, 0), "b": (1, 1)}), ("W3d", {"a": (2, 0), "b": (1, 1)})):
    region = [q for q in P2 if (forms["b"][0] * q[0] + forms["b"][1] * q[1]) < 2 * q[1]]
    b0, p0, mine = dot_tables(forms, (0, 1), region)
    theirs = record_table(cone)
    chains = {"W3b": [((1, 0), (1, 1))], "W3d": [((1, 0), (1, 1))]}   # (x, gam) = forms over (y1, y2)
    hit = None
    for x_form, g_form in chains[cone]:
        for o in permutations(range(2)):
            def pull2(k):
                vec = [k[0] * x_form[j] + k[1] * g_form[j] for j in range(2)]
                return canon(tuple(vec[j] for j in o))
            if {pull2(k): d for k, d in mine.items()} == theirs: hit = o
    print(f"   {cone}: base mine {b0} record {fam['cones'][cone]['base']} | <w,1> {p0} | conditions mine "
          f"{len(mine)} record {len(theirs)} | identical (order {hit}): {hit is not None}")
    positive[cone] = {k: d for k, d in mine.items() if d > 0}

# ---------------- L4/L5 ----------------
subs = fam["subfamilies"]
SUB = {
    "W2": ({"a": (0, 1), "b": (1, 0), "c": (2, 0), "d": (3, 0)}, lambda b, a: 1 <= a < b,
           [fam["cones"]["W2"]["closure"]], [fam["cones"]["W2"]["finite"]]),
    "X1 (3 cones + 2 rays)": ({"a": (0, 1), "b": (3, 0), "c": (4, 0), "d": (6, 0)}, lambda s, a: 1 <= a < 3 * s,
           [subs["X1"]["parts"][0]["closure"]], [p["finite"] for p in subs["X1"]["parts"] + subs["X1"]["rays"]]),
    "X2": ({"a": (0, 1), "b": (2, -1), "c": (2, 0), "d": (3, 0)}, lambda gm, a: 1 <= a < gm,
           [subs["X2"]["closure"]], [subs["X2"]["finite"]]),
    "X3": ({"a": (1, 0), "b": (0, 1), "c": (2, 0), "d": (3, 0)}, lambda gm, b: gm < b < 2 * gm,
           [subs["X3"]["closure"]], [subs["X3"]["finite"]]),
    "X4": ({"a": (3, 0), "b": (0, 1), "c": (4, 0), "d": (6, 0)}, lambda s, b: 3 * s < b < 4 * s,
           [subs["X4"]["closure"]], [subs["X4"]["finite"]]),
}
same_closures = all(p["closure"] == subs["X1"]["parts"][0]["closure"] for p in subs["X1"]["parts"])
print("\nL4/L5   (X1's three cone parts carry identical closures:", same_closures, ")")
total, fails_all = 0, []
for name, (members, domain, closures, finites) in SUB.items():
    results = [check_closure(members, cl) for cl in closures]
    for res in results:
        print(f"   {name:<22} m1={tuple(map(str, res['m1']))} m2={tuple(map(str, res['m2']))} "
              f"anchors=({res['xi'][0]}pi,{res['xi'][1]}pi) bound {res['A']} + {res['B']}pi^2/N^2 + "
              f"{res['C']}/N + {res['D']}pi/N floor {res['floor']} N0 {res['N0']}"
              f"{'' if res['minimal'] else ' (not minimal)'} | record match: {res['matches_record']}")
    fin = finite_part(members, domain, results)
    fails = [S for S in fin if not certify(S) < L_UPPER_SAFE]
    total += len(fin) - len(fails); fails_all += fails
    print(f"          finite: mine {len(fin)} {sorted(fin) if len(fin) <= 5 else ''} record "
          f"{sum(f['enumerated'] for f in finites)} | certified {len(fin) - len(fails)} | failures {fails}")
rays = [tuple(int(x) for x in subs[r]["label"].split("}")[0].strip("{").split(",")) for r in
        ("R1346", "R4569", "R2469", "R67812")]
ray_ok = [r for r in rays if certify(r) < L_UPPER_SAFE]
total += len(ray_ok)
print(f"   rays {rays}: certified {len(ray_ok)}/4")
print(f"\ncertified in family 2d = 3c: {total}  (record: 27)   failures: {fails_all or 'none'}")
print("positive-delta conditions per cone (in cone base variables):",
      {c: {str(k): str(d) for k, d in v.items()} for c, v in positive.items()})
