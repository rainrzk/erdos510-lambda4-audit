"""Step 0: independently verify the claimed exact value L(1,2,3,4).

Claim (teorth/erdosproblems#392): -min_t sum_{k=1..4} cos(k t) is the root of
512y^3 - 1227y^2 + 600y + 125 near 1.5195578816428.

Method: with c = cos t, sum_{k in A} cos(k t) = sum_{k in A} T_k(c) (Chebyshev), so the
minimum over t equals the minimum of a polynomial over c in [-1, 1]. Its value at an
interior critical point satisfies Res_c(p(c) + y, p'(c)) = 0. Mercer's lambda(2) = 9/8 and
lambda(3) = (17 + 7*sqrt(7))/27 (for the sets {1,2} and {1,2,3}) serve as calibration.
"""
from sympy import (Poly, Rational, chebyshevt, diff, expand, factor_list, real_roots,
                   resultant, sqrt, symbols, N, nsimplify)

c, y = symbols("c y")


def cosine_sum_poly(A):
    return expand(sum(chebyshevt(k, c) for k in A))


def exact_min(A):
    """Global minimum of sum_{k in A} T_k(c) over c in [-1, 1]; returns (min, argmin)."""
    p = cosine_sum_poly(A)
    candidates = [Rational(-1), Rational(1)]
    candidates += [r for r in real_roots(Poly(diff(p, c), c)) if -1 <= r <= 1]
    vals = [(p.subs(c, r), r) for r in candidates]
    return min(vals, key=lambda v: N(v[0], 60)), p


# Calibration against Mercer's proved values (for the conjectured extremal sets).
for A, known in [((1, 2), Rational(9, 8)), ((1, 2, 3), (17 + 7 * sqrt(7)) / 27)]:
    (m, _), _ = exact_min(A)
    print(f"A={A}: -min = {N(-m, 30)}  Mercer: {N(known, 30)}  "
          f"diff = {N(-m - known, 50)}")

# The claimed lambda(4) value.
(m4, c4), p4 = exact_min((1, 2, 3, 4))
print("\nf_{1,2,3,4} as polynomial in c:", p4)
assert expand(p4 - (8*c**4 + 4*c**3 - 6*c**2 - 2*c)) == 0, "quartic mismatch"

R = resultant(p4 + y, diff(p4, c), c)
print("Res_c(p + y, p'):", factor_list(R))
cubic = Poly(512*y**3 - 1227*y**2 + 600*y + 125, y)
quot, rem = Poly(R, y).div(cubic)
print("claimed cubic divides the resultant exactly:", rem.is_zero, " quotient:", quot)

roots = real_roots(cubic)
print("real roots of the cubic:", [N(r, 20) for r in roots], f"({len(roots)} real roots)")
print("argmin c* =", N(c4, 30), " -> t* = arccos(c*)")
print("-min f_{1,2,3,4} =", N(-m4, 50))
print("largest cubic root =", N(roots[-1], 50))
print("difference:", N(-m4 - roots[-1], 60))
