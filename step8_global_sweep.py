"""Step 8: proof-independent sweep of the theorem's conclusion.

For EVERY 4-set A = {a<b<c<d} with gcd(A) = 1 and d <= M, other than {1,2,3,4}, show
min_t f_A(t) < L(1,2,3,4) by exhibiting a point t with f_A(t) < L.

Method: f_A on a common grid t_j = pi j / G (vectorised, double precision). A set counts as
certified when f_A(t_j) < L - MARGIN for some grid point. Evaluating 4 cosines of arguments
<= M*pi in double has absolute error far below 1e-12, so MARGIN = 1e-9 leaves a safety factor
above 1000. Sets that miss the margin on the grid get a local refinement and an interval-
arithmetic certificate (audit_lib.certify). The tightest sets are re-certified with intervals
as well.
Usage: python3 step8_global_sweep.py [M]
"""
import sys
import time
from math import gcd

import numpy as np

from audit_lib import L_FLOAT, L_UPPER_SAFE, certify

M = int(sys.argv[1]) if len(sys.argv) > 1 else 80
G = 4096
MARGIN = 1e-9
t = np.pi * np.arange(G + 1) / G
C = np.cos(np.outer(np.arange(M + 1), t))            # C[k, j] = cos(k t_j)

start = time.time()
sets = np.array([(a, b, c, d) for d in range(4, M + 1) for c in range(3, d) for b in range(2, c)
                 for a in range(1, b) if gcd(gcd(a, b), gcd(c, d)) == 1], dtype=np.int64)
is_extremal = np.all(sets == np.array([1, 2, 3, 4]), axis=1)
print(f"M = {M}: {len(sets):,} gcd-reduced 4-sets (enumerated in {time.time() - start:.1f}s)")

mins = np.empty(len(sets))
B = 20000
for i in range(0, len(sets), B):
    S = sets[i:i + B]
    mins[i:i + B] = (C[S[:, 0]] + C[S[:, 1]] + C[S[:, 2]] + C[S[:, 3]]).min(axis=1)
print(f"grid minima computed in {time.time() - start:.1f}s")

ok = (mins < L_FLOAT - MARGIN) & ~is_extremal
todo = np.where(~ok & ~is_extremal)[0]
print(f"certified on the grid with margin {MARGIN}: {ok.sum():,};  needing refinement: {len(todo)}")
refined_fail = []
for idx in todo:
    if not certify(tuple(int(x) for x in sets[idx])) < L_UPPER_SAFE:
        refined_fail.append(tuple(int(x) for x in sets[idx]))
print(f"refined with interval arithmetic: {len(todo) - len(refined_fail)} certified, "
      f"{len(refined_fail)} NOT certified: {refined_fail[:20]}")

# the sets that come closest to the extremal value, re-certified with interval arithmetic
order = np.argsort(-np.where(is_extremal, -np.inf, mins))[:12]
print("\nclosest competitors (grid minimum; interval-certified upper bound):")
for idx in order:
    S = tuple(int(x) for x in sets[idx])
    ub = certify(S)
    print(f"   {S}: grid min {mins[idx]:.9f}   certified f <= {float(ub):.9f}   "
          f"margin below L: {L_FLOAT - float(ub):.3e}   {'OK' if ub < L_UPPER_SAFE else 'FAIL'}")
print(f"\nL(1,2,3,4) = {L_FLOAT:.12f};  total time {time.time() - start:.1f}s")
