"""Step 6: full audit of family 2d = 2c+b (write-up Section 5.8): layers 3, 4, 5.

Parity b = 2*beta, so d = c + beta. Region a < b < c, triangulated on a vs beta:
  cone i  : a < beta,          chain (x1, x2, x3) = (a, beta - a, c - 2beta)
  cone ii : a = beta,          closed by a two-closure union (extremal set skipped)
  cone iii: beta < a < 2beta,  chain tried in both orders of (a - beta, 2beta - a), then c - 2beta
L3: dot on S(c, pi), w = 2(1-cos a)^2, g = 3/5 + cos a + cos b + cos d; conditions derived in
    (a, beta, c), pulled back to chain parameters and compared with the record's keys.
L4/L5: cone ii and V1, V2 (3 parts), V5, V6, V7 recomputed; V3/V4 are delegations to families
    d = 2a and d = a+b, whose closures were audited in steps 3-4.
Usage: python3 step6_family_2d2cb.py path/to/lambda4-campaign.json
"""
import json
import sys
from fractions import Fraction as F

from audit_lib import L_UPPER_SAFE, certify, check_closure, finite_part
from step3_families_L3 import canon, const, cosp, cos_multiple, mul, one_minus_sq, plus

fam = json.load(open(sys.argv[1]))["lambda4families"]["2d = 2c+b"]

# ---------------- L3 on cones i and iii (base variables (a, beta, c)) ----------------
n = 3
A_, B_, C_, D_ = (1, 0, 0), (0, 2, 0), (0, 0, 1), (0, 1, 1)       # a, b = 2beta, c, d = c + beta
w = one_minus_sq(A_, n)
g = plus(const(F(3, 5), n), cosp(A_), cosp(B_), cosp(D_))
wg = mul(w, g)
anchor, xi = (0, 0, 1), 6                                          # S(c, pi)
pts = [(a, be, c) for be in range(1, 40) for a in range(1, 2 * be) for c in range(2 * be + 1, 120)]
REGION = {"i": [p for p in pts if p[0] < p[1]], "iii": [p for p in pts if p[0] > p[1]]}
PARAMS = {"i": [{"a": (1, 0, 0), "be": (1, 1, 0), "c": (2, 2, 1)}],
          "iii": [{"a": (2, 1, 0), "be": (1, 1, 0), "c": (2, 2, 1)},     # (a-beta, 2beta-a, c-2beta)
                  {"a": (1, 2, 0), "be": (1, 1, 0), "c": (2, 2, 1)}]}    # (2beta-a, a-beta, c-2beta)


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
    cols = [par["a"], par["be"], par["c"]]
    return canon(tuple(sum(key[i] * cols[i][j] for i in range(3)) for j in range(3)))


def show(k):
    return " + ".join(f"{c}{v}" for c, v in zip(k, ("a", "beta", "c")) if c) + " = 0"

print("L3  dot on S(c, pi): base <w,g> =", wg.get((0, 0, 0)), " <w,1> =", w.get((0, 0, 0)),
      " record base", fam["cones"]["i"]["base"])
for cone in ("i", "iii"):
    mine_abc = conditions(REGION[cone])
    theirs = {canon(tuple(int(x) for x in e["key"].split(","))): F(e["delta"])
              for e in fam["cones"][cone]["exceptions"]}
    for par in PARAMS[cone]:
        mine = {pull_back(k, par): d for k, d in mine_abc.items()}
        if mine == theirs:
            break
    print(f"   cone {cone}: mine {len(mine)} record {len(theirs)}  identical: {mine == theirs}")
    for k, d in sorted(mine_abc.items(), key=lambda kv: -kv[1]):
        if d > 0: print(f"      positive: {show(k):<26} delta {d}")

# ---------------- L4/L5 ----------------
SUB = {
    "cone ii": ({"a": (1, 0), "b": (2, 0), "c": (0, 1), "d": (1, 1)}, lambda a, c: c > 2 * a),
    "V1/0": ({"a": (0, 1), "b": (2, 0), "c": (1, 2), "d": (2, 2)}, lambda be, a: be < 2 * a and a < be),
    "V2/0": ({"a": (0, 1), "b": (2, 0), "c": (2, 1), "d": (3, 1)}, lambda be, a: 1 <= a < be),
    "V2/1": ({"a": (1, 0), "b": (2, 0), "c": (3, 0), "d": (4, 0)}, lambda be, y: y == 0),
    "V2/2": ({"a": (0, 1), "b": (2, 0), "c": (2, 1), "d": (3, 1)}, lambda be, a: be < a < 2 * be),
    "V5/0": ({"a": (0, 1), "b": (2, 0), "c": (1, 2), "d": (2, 2)}, lambda be, a: be < a < 2 * be),
    "V6/0": ({"a": (1, 0), "b": (0, 2), "c": (2, 0), "d": (2, 1)}, lambda a, be: be < a < 2 * be),
    "V7/0": ({"a": (2, 0), "b": (0, 2), "c": (3, 0), "d": (3, 1)}, lambda s, be: s < be and 2 * be < 3 * s),
}


def record_part(path):
    if path == "cone ii":
        c = fam["cones"]["ii"]; return {"closures": c["closures"], "finite": c["finite"]}
    name, idx = path.split("/")
    sf = fam["subfamilies"][name]
    part = sf["parts"][int(idx)] if "parts" in sf else sf
    cls = part.get("closures") or ([part["closure"]] if part.get("closure") else [])
    return {"closures": cls, "finite": part["finite"]}

print("\nL4/L5")
total, all_fail = 0, []
for path, (members, domain) in SUB.items():
    part = record_part(path)
    results = [check_closure(members, cl) for cl in part["closures"]]
    for res in results:
        print(f"   {path:<8} m1={tuple(map(str, res['m1']))} m2={tuple(map(str, res['m2']))} "
              f"anchors=({res['xi'][0]}pi,{res['xi'][1]}pi) bound {res['A']} + {res['B']}pi^2/N^2 + "
              f"{res['C']}/N + {res['D']}pi/N floor {res['floor']} N0 {res['N0']}"
              f"{'' if res['minimal'] else ' (not minimal)'} | record match: {res['matches_record']}")
    fin = finite_part(members, domain, results)
    skipped = [S for S in fin if S == (1, 2, 3, 4)]
    fails = []
    for S in fin:
        if S == (1, 2, 3, 4): continue
        if not certify(S) < L_UPPER_SAFE: fails.append(S)
    total += len(fin) - len(skipped) - len(fails); all_fail += fails
    r = part["finite"]
    print(f"            finite: mine {len(fin)} (skip {len(skipped)}) record {r['enumerated']} "
          f"(skip {len(r['skipped'])}) | certified {len(fin) - len(skipped) - len(fails)} | failures {fails}")
print(f"\ncertified in family 2d = 2c+b: {total}  (record closed: "
      f"{sum(record_part(p)['finite']['closed'] for p in SUB)})   failures: {all_fail or 'none'}")
print("delegations: V3 (d = 2a) -> family d = 2a, V4 (d = a+b) -> family d = a+b; both families were "
      "audited as closing ALL their members (steps 3-4).")
