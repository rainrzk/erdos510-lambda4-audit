# Independent audit of the λ(4) proof (Erdős #510 / teorth/erdosproblems#392)

**Claim under audit:** λ(4) = −L(1,2,3,4) is the largest root of 512y³ − 1227y² + 600y + 125 (≈ 1.5195578816428).
The proof was machine-derived by the cert-machine engine: write-up `paper/lambda4-proof.md`, record `certs/lambda4-campaign.json`, git e8daa11.

**Method.** Everything was recomputed with our own code. We read the engine's JSON record only as data, and never ran any of its code. The record's per-member closure data (u, v, lemma kind, value) was used only to identify *which* argument is claimed. Each claimed argument (decomposition, anchors, bound, validity floor, threshold) was then re-derived from scratch and compared with the record.

## Status (2026-09-30): all layers checked; no mathematical error found

| Layer | What | Result |
|---|---|---|
| 0 | exact value | ✅ Res_c(p+y, p′) = 2048·(cubic); agrees to 190 digits. Mercer's λ(2) and λ(3) reproduced as calibration (`step0_value.py`) |
| 1 | Lemmas A–F | ✅ Checked by hand. For Lemma C: the differences t₁−t₂ form an AP with step 2πg/(m₁m₂). For E: the chord through (π/2, 0) and (2π/3, −1/2) has slope −3/π |
| 2 | generic case | ✅ 14 collision conditions derived independently; exhaustive, and the deltas are identical. 68,759 sets with d ≤ 40 were checked numerically (`step1_generic.py`) |
| 3 | dot theorems of all 9 families | ✅ Single-dot families (d=2c, d=2a, d=b+c, d=a+b, d=a+c, 2d=2c+a) matched one-to-one through the record's example sets (`step3`). Triangulated families: all 10 cone tables are identical once pulled back to chain parameters — D1, D3 (`step5`); i, iii (`step6`); W1, W3a, W3b (base −13/10), W3c, W3d, W3e (`step7`) |
| 4 | every subfamily closure | ✅ All match the record: (u,v) decomposition over (m₁,m₂), consistent anchor angles, bound A + Bπ²/N² + C/N + Dπ/N, validity floor, and N₀. N₀ minimality was checked with a rigorous π enclosure (`step2`, `step4`–`step7`) |
| 5 | finite certificates | ✅ **2,231 / 2,231** finite sets re-enumerated from our own thresholds; the per-subfamily counts match the record exactly. Each set was certified with interval arithmetic to satisfy min f_A < L. The 6 skips of {1,2,3,4} match the record |
| 6 | coverage / assembly | ✅ In every family, each positive-delta condition maps to a subfamily or a delegation (d=2a, d=a+b), or reduces to a single-set ray. Triangulations are complete by trichotomy. Positivity ⟨w,1⟩ > 0 holds in the worst case |
| — | proof-independent sweep | ✅ All **1,473,833** gcd-reduced 4-sets with d ≤ 80, other than {1,2,3,4}, satisfy min f_A < L; nothing needed rescue. The closest competitor is {2,3,4,6} at −1.7737, 0.254 below L (`step8_global_sweep.py`) |

## Findings (documentation only; none affects correctness)
1. PR #411 describes the cubic as having a "unique real root". It has three real roots (−0.1556, 1.0325, 1.5196); λ(4) is the largest.
2. Write-up §4 says the extremal set "appears exactly once, in a single cone or ray" in each equality family. In the record it is skipped 6 times: once in d=a+c, three times in d=2b (D2, U1 cone 3, U2), and twice in 2d=2c+b (cone ii, V2 part 1). This is harmless, since each skip is the equality case, but the sentence is inaccurate.
3. §5.8's list of finite parts omits cone ii's 89 sets. The overall count is consistent: 2,237 enumerated − 6 skips = 2,231 certified.
4. The write-up never states the target function g of each family's dot theorem. We inferred them from the recorded base value and dip, and each was confirmed by reproducing the full collision table.
5. In family 2d=2c+b, the subfamilies V1 ("d = b+2a") and V5 ("d = 2c−2a") are the same hyperplane c = β + 2a, since the two equations are equivalent under 2d = 2c+b. The triangulation splits it: V1 is the cone-i half, V5 the cone-iii half. The labels hide this.

## Caveats (what "independent" does and does not mean here)
- The subfamily parametrizations are our reading of the prose in §5. Their exact agreement with the record's finite counts, in every one of the ~40 pieces, is strong evidence they are the same.
- Lemmas A–F were checked by hand, not formally. A Lean formalization, which the issue suggests, would close this gap.

## Reproduce
```
pip install -r requirements.txt
bash run_all.sh          # runs step0-step8 on data/lambda4-campaign.json, logs to logs/, ends with ALL CHECKS PASSED
```
The record file comes from cert-machine and is bundled under MIT. See `data/PROVENANCE.md` for the commit and SHA-256.
