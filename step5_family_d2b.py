"""Step 5: full audit of family d = 2b (write-up Section 5.7): layers 3, 4, 5.

Region a < b < c < 2b, triangulated on a vs c - b:
  D1: a < c - b, chain parameters (x1, x2, x3) = (a, (c-b) - a, 2b - c)
  D3: a > c - b, chain parameters (x1, x2, x3) = (c - b, a - (c-b), b - a)
  D2: a = c - b (c = a + b), closed directly.
L3: the dot on S(b, 2pi/3) with w = 2(1-cos a)^2 + 2(1-cos c)^2 and g = 3/5 + cos a + cos c is
    re-derived in (a, b, c); each condition is pulled back to chain parameters and compared with
    the record's "key" vectors (hypothesis: key = the condition's linear form on (x1, x2, x3)).
L4/L5: every closure of D2 and U1-U6 is recomputed; finite parts re-enumerated and certified.
Usage: python3 step5_family_d2b.py path/to/lambda4-campaign.json
"""
import json
import sys
from fractions import Fraction as F
from itertools import combinations

from audit_lib import L_FLOAT, L_UPPER_SAFE, certify, check_closure, finite_part
from step3_families_L3 import canon, const, cosp, cos_multiple, mul, one_minus_sq, plus

fam = json.load(open(sys.argv[1]))["lambda4families"]["d = 2b"]

# ---------------- L3 on cones D1, D3 ----------------
n = 3
forms = {"a": (1, 0, 0), "b": (0, 1, 0), "c": (0, 0, 1)}          # d = 2b substituted
w = plus(one_minus_sq(forms["a"], n), one_minus_sq(forms["c"], n))
g = plus(const(F(3, 5), n), cosp(forms["a"]), cosp(forms["c"]))
wg = mul(w, g)
anchor, xi = (0, 1, 0), 4                                          # S(b, 2pi/3)

pts = [(a, b, c) for a, b, c in combinations(range(1, 80), 3) if c < 2 * b]
REGION = {"D1": [p for p in pts if p[0] < p[2] - p[1]], "D3": [p for p in pts if p[0] > p[2] - p[1]]}
# chain parametrizations: (a, b, c) as linear forms in (x1, x2, x3)  [columns = x1, x2, x3]
PARAM = {"D1": {"a": (1, 0, 0), "b": (1, 1, 1), "c": (2, 2, 1)},
         "D3": {"a": (1, 1, 0), "b": (1, 1, 1), "c": (2, 1, 1)}}


def conditions(region):
    out = {}
    for v, cf in wg.items():
        if not any(v): continue
        for tp in range(0, 8):
            for s in ((1,) if tp == 0 else (1, -1)):
                key = tuple(s * x - tp * y for x, y in zip(v, anchor))
                if not any(key): continue
                key = canon(key)
                if not any(sum(k * x for k, x in zip(key, p)) == 0 for p in region): continue
                out[key] = out.get(key, F(0)) + cf * cos_multiple(tp, xi)
    return {k: d for k, d in out.items() if d != 0}


def pull_back(key, par):
    """condition k_a a + k_b b + k_c c = 0  ->  coefficients on (x1, x2, x3)."""
    return canon(tuple(sum(key[i] * par["abc"[i]][j] for i in range(3)) for j in range(3)))


print("L3  dot on S(b, 2pi/3):  base <w,g> =", wg.get((0, 0, 0)), "(record", fam["cones"]["D1"]["base"],
      ")   <w,1> =", w.get((0, 0, 0)))
positives = []
for cone in ("D1", "D3"):
    mine = {pull_back(k, PARAM[cone]): (d, k) for k, d in conditions(REGION[cone]).items()}
    theirs = {canon(tuple(int(x) for x in e["key"].split(","))): F(e["delta"])
              for e in fam["cones"][cone]["exceptions"]}
    same = {k: d for k, (d, _) in mine.items()} == theirs
    print(f"   cone {cone}: conditions mine {len(mine)} record {len(theirs)}  identical: {same}")
    for k in sorted(set(mine) | set(theirs)):
        dm = mine.get(k, ("-", None))[0]; dt = theirs.get(k, "-")
        orig = mine.get(k, (None, None))[1]
        if dm != dt or (dm != "-" and dm > 0):
            tag = "" if dm == dt else "   <-- MISMATCH"
            print(f"      key {k}: mine {dm} record {dt}  (in a,b,c: {orig}){tag}")
        if dm != "-" and dm > 0: positives.append((cone, orig, dm))
print("   positive-delta conditions (to be consolidated into U1..U6):",
      sorted({(o, str(d)) for _, o, d in positives}))

# ---------------- L4/L5 ----------------
SUB = {  # (record path, members over params (x, y), domain)
    "D2":      ({"a": (0, 1), "b": (1, 0), "c": (1, 1), "d": (2, 0)}, lambda b, a: 1 <= a < b),
    "U1/0":    ({"a": (1, 0), "b": (2, 0), "c": (0, 1), "d": (4, 0)}, lambda a, c: 3 * a < c < 4 * a),
    "U1/1":    ({"a": (1, 0), "b": (2, 0), "c": (0, 1), "d": (4, 0)}, lambda a, c: 2 * a < c < 3 * a),
    "U1/2":    ({"a": (1, 0), "b": (2, 0), "c": (3, 0), "d": (4, 0)}, lambda a, y: y == 0),
    "U2/0":    ({"a": (1, -1), "b": (1, 0), "c": (1, 1), "d": (2, 0)}, lambda b, t: 1 <= t < b),
    "U3/0":    ({"a": (0, 1), "b": (1, 0), "c": (3, -2), "d": (2, 0)}, lambda b, a: b < 2 * a and a < b),
    "U4/0":    ({"a": (1, -2), "b": (1, 0), "c": (2, -1), "d": (2, 0)}, lambda b, s: s >= 1 and 2 * s < b),
    "U5/0":    ({"a": (1, 0), "b": (1, 2), "c": (1, 3), "d": (2, 4)}, lambda a, s: s >= 1),
    "U6/0":    ({"a": (1, 0), "b": (0, 1), "c": (2, 0), "d": (0, 2)}, lambda a, b: a < b < 2 * a),
}
subs = {s["label"].split(":")[0]: s for s in fam["subfamilies"]}

def record_part(path):
    if path == "D2":
        return {"closures": [fam["cones"]["D2"]["closure"]], "finite": fam["cones"]["D2"]["finite"]}
    name, idx = path.split("/")
    return subs[name]["parts"][int(idx)]

print("\nL4/L5")
total, all_fail = 0, []
for path, (members, domain) in SUB.items():
    part = record_part(path)
    results = [check_closure(members, cl) for cl in part.get("closures", [])]
    for res in results:
        print(f"   {path:<5} m1={tuple(map(str, res['m1']))} m2={tuple(map(str, res['m2']))} "
              f"anchors=({res['xi'][0]}pi,{res['xi'][1]}pi) bound {res['A']} + {res['B']}pi^2/N^2 + "
              f"{res['C']}/N + {res['D']}pi/N floor {res['floor']} N0 {res['N0']}"
              f"{'' if res['minimal'] else ' (not minimal)'} | record match: {res['matches_record']}")
    fin = finite_part(members, domain, results)
    skipped = [S for S in fin if S == (1, 2, 3, 4)]
    fails, worst = [], None
    for S in fin:
        if S == (1, 2, 3, 4): continue
        ub = certify(S)
        if not ub < L_UPPER_SAFE: fails.append(S); continue
        if worst is None or ub > worst[0]: worst = (ub, S)
    total += len(fin) - len(skipped) - len(fails); all_fail += fails
    r = part["finite"]
    print(f"         finite: mine {len(fin)} (skip {len(skipped)}) record {r['enumerated']} (skip {len(r['skipped'])})"
          f" | certified {len(fin) - len(skipped) - len(fails)} | failures {fails}"
          + (f" | tightest {worst[1]}: {float(worst[0]):.6f}" if worst else ""))
print(f"\ncertified in family d = 2b: {total}  (record closed: "
      f"{sum(record_part(p)['finite']['closed'] for p in SUB)})   failures: {all_fail or 'none'}")
