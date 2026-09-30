"""Shared, engine-independent machinery for auditing the lambda(4) write-up.

  * L_UPPER_SAFE: rigorous number below L(1,2,3,4) (exact rational bracketing of the cubic root);
  * check_closure: re-derives one anchored two-set closure (write-up Section 2.4) from the record's
    per-member (u, v, lemma) data and a subfamily parametrization, returning its bound and N0;
  * finite_part: re-enumerates the gcd-reduced subfamily members no closure covers;
  * certify: rigorous interval-arithmetic proof that min f_A < L(1,2,3,4).
"""
from fractions import Fraction as F
from math import cos, gcd, pi

import mpmath as mp
from mpmath import iv

mp.mp.dps = 60
_P = lambda y: 512 * y**3 - 1227 * y**2 + 600 * y + 125
_r = mp.findroot(lambda y: 512 * y**3 - 1227 * y**2 + 600 * y + 125, 1.52)
R_LO = F(mp.nstr(_r - mp.mpf("1e-50"), 70))
R_HI = F(mp.nstr(_r + mp.mpf("1e-50"), 70))
assert _P(R_LO) < 0 < _P(R_HI)
L_UPPER_SAFE = -R_HI            # L > -R_HI, so f_A(t) < -R_HI certifies f_A(t) < L
L_FLOAT = float(-_r)
PI_LO, PI_HI = F(314159265358979, 10**14), F(314159265358980, 10**14)

ANGLES = [F(k, 6) for k in range(12)]          # anchor candidates: multiples of pi/6 (units of pi)
_COS = {F(0): F(1), F(1, 3): F(1, 2), F(1, 2): F(0), F(2, 3): F(-1, 2), F(1): F(-1),
        F(4, 3): F(-1, 2), F(3, 2): F(0), F(5, 3): F(1, 2), F(1, 6): None}
cospi = lambda q: _COS.get(q % 2)
TARGETS = {"lemma3.3": {F(2, 3), F(4, 3)}, "lemma3.2": {F(1)}, "lemma-halfpi": {F(1, 2), F(3, 2)}}


def _scale(v, k): return tuple(F(k) * x for x in v)
def _sub(v, w): return tuple(x - y for x, y in zip(v, w))


def check_closure(members, cl):
    """members: member name -> integer vector over the subfamily parameters."""
    exact = [p for p in cl["pieces"] if p["kind"] == "exact"]
    lemma = [p for p in cl["pieces"] if p["kind"] != "exact"]
    # Solve member_i = u_i m1 + v_i m2 for the two orders from any pair of independent pieces
    # (m1 need not be a member, and a closure may have no exactly-anchored member at all).
    pcs = [(members[p["member"]], F(p.get("u", 0)), F(p.get("v", 0))) for p in cl["pieces"]]
    m1 = m2 = None
    for i in range(len(pcs)):
        for j in range(i + 1, len(pcs)):
            (Mi, ui, vi), (Mj, uj, vj) = pcs[i], pcs[j]
            det = ui * vj - uj * vi
            if det:
                m1 = tuple((vj * x - vi * y) / det for x, y in zip(Mi, Mj))
                m2 = tuple((ui * y - uj * x) / det for x, y in zip(Mi, Mj))
                break
        if m1: break
    assert m1 is not None, "pieces do not determine the two orders"
    if cl.get("tailMember"):
        assert m1 == tuple(F(x) for x in members[cl["tailMember"]]), "tail member is not m1"
    for p in cl["pieces"]:                     # every member = u m1 + v m2 identically
        u, v = F(p.get("u", 0)), F(p.get("v", 0))
        assert _sub(members[p["member"]], tuple(u * x + v * y for x, y in zip(m1, m2))) == \
            (0,) * len(m1), f"decomposition fails for {p}"
        assert u.denominator == 1 and v.denominator == 1, "non-integral decomposition"
    sol = None
    for xi1 in ANGLES:
        if not all(cospi(F(p["u"]) * xi1) == F(p["value"]) for p in exact):
            continue
        for xi2 in ANGLES:
            if all(((F(p["u"]) * xi1 + F(p["v"]) * xi2) % 2) in TARGETS[p["kind"]] for p in lemma):
                sol = (xi1, xi2); break
        if sol: break
    assert sol, "no consistent anchor angles"
    A = sum(F(p["value"]) for p in exact); B = C = D = F(0); floor = 1
    for p in lemma:
        v = abs(F(p["v"]))
        if p["kind"] == "lemma3.3": A += F(-1, 2); C += 3 * v; floor = max(floor, int(6 * v))
        if p["kind"] == "lemma3.2": A += -1; B += v * v / 2
        if p["kind"] == "lemma-halfpi": D += v
    hi = lambda N: A + B * PI_HI**2 / N**2 + C / N + D * PI_HI / N
    lo = lambda N: A + B * PI_LO**2 / N**2 + C / N + D * PI_LO / N
    N0 = floor
    while not hi(N0) < L_UPPER_SAFE: N0 += 1
    minimal = N0 == floor or not lo(N0 - 1) < -R_LO
    e = cl["expr"]
    same = (A, B, C, D, N0, floor) == (F(e["A"]), F(e["B"]), F(e["C"]), F(e["D"]),
                                       cl["N0"], cl["validityFloor"])
    return dict(m1=m1, m2=m2, xi=sol, A=A, B=B, C=C, D=D, floor=floor, N0=N0,
                minimal=minimal, matches_record=same)


def finite_part(members, domain, closures, box=300):
    """gcd-reduced members of the subfamily with every closure's N = m1 below its threshold."""
    names = [k for k in "abcd"]
    out = []
    for x in range(1, box):
        for y in range(-box, box):
            if not domain(x, y): continue
            S = tuple(members[k][0] * x + members[k][1] * y for k in names)
            if min(S) < 1 or gcd(gcd(S[0], S[1]), gcd(S[2], S[3])) != 1: continue
            covered = False
            for res in closures:
                N = res["m1"][0] * x + res["m1"][1] * y
                if N >= max(res["N0"], res["floor"]): covered = True
            if not covered: out.append(S)
    return out


def certify(A, grid_factor=256):
    """Rigorous upper bound on min_t f_A(t) (interval arithmetic at a point near the minimum)."""
    M = max(A); G = max(4096, grid_factor * M)
    best = sorted((sum(cos(k * pi * j / G) for k in A), j) for j in range(G + 1))[:4]
    mp.mp.dps = 50
    f = lambda t: sum(mp.cos(k * t) for k in A)
    cands = []
    for _, j in best:
        t0 = mp.pi * j / G; cands.append(t0)
        try:
            t = mp.findroot(lambda t: sum(-k * mp.sin(k * t) for k in A), t0)
            if f(t) <= f(t0): cands.append(t)
        except (ValueError, ZeroDivisionError):
            pass
    iv.dps = 50
    ub = min(sum(iv.cos(k * iv.mpf(t)) for k in A).b for t in cands)
    ub = F(mp.nstr(mp.mpf(ub), 60))
    if not ub < L_UPPER_SAFE and grid_factor < 4096:
        return certify(A, grid_factor=4096)
    return ub
