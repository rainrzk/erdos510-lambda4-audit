"""Step 4: layers 4-5 (closures + finite parts) for the subfamilies of families
d = 2c (regression), d = a+b and d = a+c. Parametrizations come from the write-up (Sections 5.1,
5.4, 5.5); everything else is recomputed and compared with the record.
Usage: python3 step4_L45_families.py path/to/lambda4-campaign.json
"""
import json
import sys

from audit_lib import L_FLOAT, L_UPPER_SAFE, certify, check_closure, finite_part

rec = json.load(open(sys.argv[1]))["lambda4families"]

SUBS = {
    ("d = 2c", "b = 2a"):  ({"a": (1, 0), "b": (2, 0), "c": (0, 1), "d": (0, 2)}, lambda x, y: y > 2 * x),
    ("d = 2c", "c = 2a"):  ({"a": (1, 0), "b": (0, 1), "c": (2, 0), "d": (4, 0)}, lambda x, y: x < y < 2 * x),
    ("d = 2c", "c = 2b"):  ({"a": (1, 0), "b": (0, 1), "c": (0, 2), "d": (0, 4)}, lambda x, y: 0 < x < y),
    ("d = 2c", "c = a+b"): ({"a": (1, 0), "b": (0, 1), "c": (1, 1), "d": (2, 2)}, lambda x, y: 0 < x < y),
    # d = a+b, 2d = 3c: {3p+q, 3p+2q, 4p+2q, 6p+3q}, params (p, q) >= 1
    ("d = a+b", "E: 2d = 3c"): ({"a": (3, 1), "b": (3, 2), "c": (4, 2), "d": (6, 3)}, lambda p, q: q >= 1),
    # d = a+c, AP: {b-t, b, b+t, 2b}, params (b, t) with 1 <= t < b
    ("d = a+c", "AP: 2b = a+c"): ({"a": (1, -1), "b": (1, 0), "c": (1, 1), "d": (2, 0)}, lambda b, t: 1 <= t < b),
    # d = a+c, 3b = 2d: b = 2s, d = 3s, c = 3s - a; params (s, a) with 1 <= a < s
    ("d = a+c", "3b = 2d"): ({"a": (0, 1), "b": (2, 0), "c": (3, -1), "d": (3, 0)}, lambda s, a: 1 <= a < s),
    # 2d = 2c+a: a = 2t, d = c + t (Section 5.6)
    ("2d = 2c+a", "2c = 3a"): ({"a": (2, 0), "b": (0, 1), "c": (3, 0), "d": (4, 0)}, lambda t, b: 2 * t < b < 3 * t),
    ("2d = 2c+a", "b = 2a"): ({"a": (2, 0), "b": (4, 0), "c": (0, 1), "d": (1, 1)}, lambda t, c: c > 4 * t),
    ("2d = 2c+a", "c = 2a, b < 3a/2·2"): ({"a": (2, 0), "b": (0, 1), "c": (4, 0), "d": (5, 0)},
                                               lambda t, b: 2 * t < b < 3 * t),
    ("2d = 2c+a", "c = 2a, b = 3al"): ({"a": (2, 0), "b": (3, 0), "c": (4, 0), "d": (5, 0)}, lambda t, y: y == 0),
    ("2d = 2c+a", "c = 2a, b > 3al"): ({"a": (2, 0), "b": (0, 1), "c": (4, 0), "d": (5, 0)},
                                       lambda t, b: 3 * t < b < 4 * t),
    ("2d = 2c+a", "2c = 2b+a"): ({"a": (2, 0), "b": (0, 1), "c": (1, 1), "d": (2, 1)}, lambda t, b: b > 2 * t),
}

grand_total = 0
for (fname, sname), (members, domain) in SUBS.items():
    sf = next(s for s in rec[fname]["subfamilies"] if s["label"] == sname)
    results = [check_closure(members, cl) for cl in sf["closures"]]
    for cl, res in zip(sf["closures"], results):
        print(f"[{fname}] {sname:<13} m1={res['m1']} m2={res['m2']} anchors=({res['xi'][0]}pi,{res['xi'][1]}pi)"
              f" bound {res['A']} + {res['B']}pi^2/N^2 + {res['C']}/N + {res['D']}pi/N"
              f"  floor {res['floor']} N0 {res['N0']}{'' if res['minimal'] else ' (not minimal)'}"
              f"  | record match: {res['matches_record']}")
    fin = finite_part(members, domain, results)
    skipped = [S for S in fin if S == (1, 2, 3, 4)]
    worst, fails = None, []
    for S in fin:
        if S == (1, 2, 3, 4): continue
        ub = certify(S)
        if not ub < L_UPPER_SAFE: fails.append(S); continue
        if worst is None or ub > worst[0]: worst = (ub, S)
    grand_total += len(fin) - len(skipped) - len(fails)
    r = sf["finite"]
    print(f"      finite: mine {len(fin)} (skipped {skipped}) record {r['enumerated']} "
          f"(skipped {r['skipped']}) | certified {len(fin) - len(skipped) - len(fails)}, failures {fails}"
          + (f" | tightest {worst[1]}: f <= {float(worst[0]):.6f} vs L = {L_FLOAT:.6f}" if worst else ""))
print(f"\ncertified finite sets in this run: {grand_total}")
