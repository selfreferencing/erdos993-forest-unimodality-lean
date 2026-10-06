import Erdos993Lean.Fiber.Cert

/-!
# The certificates of the binomial-fiber return with `n ≤ 20`, checked by the kernel

Data: the 130 certificates with `n ≤ 20` of `CERTIFICATES.json` of the 29 Sep 2026 binomial-fiber
return (`ProofRuns/2026-09-28_analytic_large_n/LEAN/pro_six/return_binomial_fiber_20260929/
BINOMIAL_FIBER_COMPLETION/CERTIFICATES.json`, **sha256 `ac4d890f43f2acd377ce981486a38609ca524a3fecb3e2dffeafcd791a13c975`**), in file order, transcribed by the
generator `ProofRuns/2026-09-28_analytic_large_n/LEAN/lanes/FIBER_FLOOR/gen_certdata.py` (lane FIBER-FLOOR):
`left ↦ alpha`, `right ↦ beta`, `epsilon ↦ eps`, `equalities ↦ (z0, z1)`, `rows ↦ prices` (row names
`edge_budget`, `matching_excess_h`, `subset_count_h`, `missing_edge_union_h`, `pair_extension_h` ↦ the
`RowId` constructors).  The file order is the order of `parameter_domain` of `CHECKER.py`.

* `certs_ok : ∀ c ∈ certs20, c.ok = true`: every certificate passes the checker `Cert.ok`
  (`decide +kernel`: evaluated by the Lean kernel, no `native_decide`, standard axioms only);
* `certs_cover : certs20.map Cert.key = paramDomain 20`: the keys `(n, a, k)` are exactly the parameter
  domain (11) through order `20`, in order.
-/

namespace Erdos993Lean
namespace Fiber

/-- The 130 certificates of `CERTIFICATES.json` with `n ≤ 20`, as `⟨n, a, k, α, β, ε, z0, z1, prices⟩`. -/
def certs20 : List Cert := [
  ⟨7, 6, 3, 0, 1, 5, 5, 0, []⟩,
  ⟨8, 6, 3, (2/5 : ℚ), (3/5 : ℚ), (28/5 : ℚ), -4, -1, [(.edgeBudget, (3/5 : ℚ)), ((.matchingExcess 2), (1/10 : ℚ)), ((.subsetCount 2), (3/5 : ℚ))]⟩,
  ⟨8, 7, 3, 1, 0, 13, 14, -1, []⟩,
  ⟨9, 8, 4, 0, 1, 14, 14, 0, []⟩,
  ⟨10, 8, 4, (1/3 : ℚ), (2/3 : ℚ), (89/6 : ℚ), (-56/3 : ℚ), (-7/2 : ℚ), [(.edgeBudget, (7/6 : ℚ)), ((.subsetCount 2), (3/2 : ℚ))]⟩,
  ⟨10, 9, 4, 1, 0, 40, 42, -2, []⟩,
  ⟨11, 7, 4, (1/3 : ℚ), (2/3 : ℚ), (37/2 : ℚ), (-301/6 : ℚ), -13, [(.edgeBudget, (17/6 : ℚ)), ((.matchingExcess 2), (1/2 : ℚ)), ((.subsetCount 2), (4/3 : ℚ)), ((.subsetCount 3), (1/3 : ℚ)), ((.pairExtension 4), (1/6 : ℚ))]⟩,
  ⟨11, 8, 4, (1/2 : ℚ), (1/2 : ℚ), 19, -56, (-23/2 : ℚ), [(.edgeBudget, (5/2 : ℚ)), ((.matchingExcess 2), (1/2 : ℚ)), ((.subsetCount 2), (1/2 : ℚ)), ((.subsetCount 3), (1/2 : ℚ))]⟩,
  ⟨11, 9, 4, 1, 0, 37, 42, -2, [((.subsetCount 2), 1)]⟩,
  ⟨11, 10, 4, 1, 0, 88, 90, -2, []⟩,
  ⟨11, 10, 5, 0, 1, 42, 42, 0, []⟩,
  ⟨12, 7, 4, (2/5 : ℚ), (3/5 : ℚ), (112/5 : ℚ), (-777/10 : ℚ), (-217/10 : ℚ), [(.edgeBudget, (41/10 : ℚ)), ((.matchingExcess 2), (3/5 : ℚ)), ((.matchingExcess 3), (1/10 : ℚ)), ((.subsetCount 2), (54/25 : ℚ)), ((.subsetCount 4), (4/5 : ℚ)), ((.pairExtension 5), (3/50 : ℚ))]⟩,
  ⟨12, 8, 4, (5/8 : ℚ), (3/8 : ℚ), (219/8 : ℚ), (-273/2 : ℚ), (-127/4 : ℚ), [(.edgeBudget, (43/8 : ℚ)), ((.matchingExcess 2), 1), ((.matchingExcess 3), (1/4 : ℚ)), ((.missingEdgeUnion 3), (5/8 : ℚ)), ((.missingEdgeUnion 4), (11/20 : ℚ)), ((.pairExtension 4), (7/40 : ℚ))]⟩,
  ⟨12, 9, 4, 1, 0, 44, -174, -34, [(.edgeBudget, 6), ((.matchingExcess 2), 1), ((.subsetCount 2), (7/3 : ℚ)), ((.pairExtension 3), (1/3 : ℚ))]⟩,
  ⟨12, 10, 4, 1, 0, 87, 0, -10, [(.edgeBudget, 2), ((.subsetCount 2), 3)]⟩,
  ⟨12, 10, 5, (14/43 : ℚ), (29/43 : ℚ), (1825/43 : ℚ), (-849/43 : ℚ), (-249/43 : ℚ), [(.edgeBudget, (59/43 : ℚ)), ((.subsetCount 2), (73/43 : ℚ))]⟩,
  ⟨12, 11, 4, 1, 0, 163, 165, -2, []⟩,
  ⟨12, 11, 5, 1, 0, 127, 132, -5, []⟩,
  ⟨13, 9, 5, (1/5 : ℚ), (4/5 : ℚ), (151/3 : ℚ), (-756/5 : ℚ), (-424/15 : ℚ), [(.edgeBudget, (77/15 : ℚ)), ((.matchingExcess 2), (3/5 : ℚ)), ((.subsetCount 3), (109/30 : ℚ)), ((.missingEdgeUnion 3), (43/30 : ℚ)), ((.pairExtension 4), (8/15 : ℚ))]⟩,
  ⟨13, 10, 5, (24/71 : ℚ), (47/71 : ℚ), (10529/213 : ℚ), (-7878/71 : ℚ), (-3511/213 : ℚ), [(.edgeBudget, (724/213 : ℚ)), ((.matchingExcess 2), (19/213 : ℚ)), ((.subsetCount 2), (1004/213 : ℚ)), ((.pairExtension 3), (322/213 : ℚ))]⟩,
  ⟨13, 11, 5, 1, 0, 120, 132, -5, [((.subsetCount 2), 2)]⟩,
  ⟨13, 12, 5, 1, 0, 292, 297, -5, []⟩,
  ⟨13, 12, 6, 0, 1, 132, 132, 0, []⟩,
  ⟨14, 9, 5, (5/14 : ℚ), (9/14 : ℚ), (409/7 : ℚ), (-4167/14 : ℚ), (-3481/56 : ℚ), [(.edgeBudget, (505/56 : ℚ)), ((.matchingExcess 2), (71/56 : ℚ)), ((.matchingExcess 3), (1/14 : ℚ)), ((.subsetCount 4), (2669/840 : ℚ)), ((.missingEdgeUnion 4), (167/120 : ℚ)), ((.pairExtension 5), (11/70 : ℚ))]⟩,
  ⟨14, 10, 5, (14/29 : ℚ), (15/29 : ℚ), (1894/29 : ℚ), (-8007/29 : ℚ), (-1405/29 : ℚ), [(.edgeBudget, (205/29 : ℚ)), ((.matchingExcess 2), (30/29 : ℚ)), ((.pairExtension 3), (14/87 : ℚ)), ((.missingEdgeUnion 4), (529/145 : ℚ)), ((.pairExtension 4), (427/435 : ℚ))]⟩,
  ⟨14, 11, 5, 1, 0, 120, -143, -35, [(.edgeBudget, 5), ((.subsetCount 2), (22/3 : ℚ)), ((.pairExtension 3), (1/3 : ℚ))]⟩,
  ⟨14, 12, 5, 1, 0, 285, 297, -5, [((.subsetCount 2), 2)]⟩,
  ⟨14, 12, 6, (6/19 : ℚ), (13/19 : ℚ), (2502/19 : ℚ), (1056/19 : ℚ), (-121/19 : ℚ), [(.edgeBudget, (22/19 : ℚ)), ((.subsetCount 2), (28/19 : ℚ))]⟩,
  ⟨14, 13, 5, 1, 0, 567, 572, -5, []⟩,
  ⟨14, 13, 6, 1, 0, 415, 429, -14, []⟩,
  ⟨15, 8, 5, (1/3 : ℚ), (2/3 : ℚ), (401/6 : ℚ), -476, -129, [(.edgeBudget, (35/2 : ℚ)), ((.matchingExcess 2), (11/6 : ℚ)), ((.matchingExcess 3), (1/2 : ℚ)), ((.missingEdgeUnion 3), (5/3 : ℚ)), ((.pairExtension 4), (1/18 : ℚ)), ((.pairExtension 5), (1/10 : ℚ)), ((.pairExtension 6), (2/45 : ℚ)), ((.missingEdgeUnion 7), (749/120 : ℚ)), ((.pairExtension 7), (107/360 : ℚ))]⟩,
  ⟨15, 9, 5, (1/2 : ℚ), (1/2 : ℚ), (153/2 : ℚ), -555, -127, [(.edgeBudget, 16), ((.matchingExcess 2), 2), ((.matchingExcess 3), (1/2 : ℚ)), ((.subsetCount 5), 1), ((.missingEdgeUnion 3), 2), ((.missingEdgeUnion 4), (61/150 : ℚ)), ((.pairExtension 4), (34/225 : ℚ)), ((.pairExtension 6), (1/30 : ℚ))]⟩,
  ⟨15, 10, 5, (4/7 : ℚ), (3/7 : ℚ), (653/7 : ℚ), (-4521/7 : ℚ), (-860/7 : ℚ), [(.edgeBudget, (107/7 : ℚ)), ((.matchingExcess 2), 2), ((.matchingExcess 3), (3/7 : ℚ)), ((.subsetCount 2), (123/70 : ℚ)), ((.missingEdgeUnion 3), 2), ((.pairExtension 4), (1/6 : ℚ)), ((.pairExtension 5), (4/35 : ℚ))]⟩,
  ⟨15, 11, 5, 1, 0, 149, -858, -142, [(.edgeBudget, 18), ((.matchingExcess 2), 2), ((.matchingExcess 4), (1/7 : ℚ)), ((.subsetCount 3), 6), ((.missingEdgeUnion 3), 5)]⟩,
  ⟨15, 11, 6, (6/61 : ℚ), (55/61 : ℚ), (25535/183 : ℚ), (-95590/183 : ℚ), (-13912/183 : ℚ), [(.edgeBudget, (2134/183 : ℚ)), ((.matchingExcess 2), (43/61 : ℚ)), ((.subsetCount 3), (5333/366 : ℚ)), ((.missingEdgeUnion 3), (1721/366 : ℚ)), ((.pairExtension 4), (343/183 : ℚ))]⟩,
  ⟨15, 12, 5, 1, 0, 304, -627, -98, [(.edgeBudget, 14), ((.subsetCount 2), (49/3 : ℚ)), ((.pairExtension 3), (1/3 : ℚ))]⟩,
  ⟨15, 12, 6, (35/108 : ℚ), (73/108 : ℚ), (7693/54 : ℚ), (-8899/18 : ℚ), (-3329/54 : ℚ), [(.edgeBudget, (1025/108 : ℚ)), ((.matchingExcess 2), (1/36 : ℚ)), ((.subsetCount 2), (1501/108 : ℚ)), ((.pairExtension 3), (77/18 : ℚ))]⟩,
  ⟨15, 13, 5, 1, 0, 560, 572, -5, [((.subsetCount 2), 2)]⟩,
  ⟨15, 13, 6, 1, 0, 396, 429, -14, [((.subsetCount 2), 5)]⟩,
  ⟨15, 14, 5, 1, 0, 996, 1001, -5, []⟩,
  ⟨15, 14, 6, 1, 0, 987, 1001, -14, []⟩,
  ⟨15, 14, 7, 0, 1, 429, 429, 0, []⟩,
  ⟨16, 8, 5, (4/7 : ℚ), (3/7 : ℚ), 86, -1092, (-2115/7 : ℚ), [(.edgeBudget, (274/7 : ℚ)), ((.matchingExcess 2), 2), ((.matchingExcess 3), 1), ((.matchingExcess 4), (5/14 : ℚ)), ((.missingEdgeUnion 3), (61/14 : ℚ)), ((.pairExtension 3), (1/2 : ℚ)), ((.missingEdgeUnion 4), (6/7 : ℚ)), ((.pairExtension 5), (1/35 : ℚ)), ((.pairExtension 6), (1/35 : ℚ))]⟩,
  ⟨16, 9, 5, (5/8 : ℚ), (3/8 : ℚ), (895/8 : ℚ), (-4557/4 : ℚ), (-547/2 : ℚ), [(.edgeBudget, (385/12 : ℚ)), ((.matchingExcess 2), (35/12 : ℚ)), ((.matchingExcess 3), 1), ((.matchingExcess 4), (1/4 : ℚ)), ((.missingEdgeUnion 3), (15/4 : ℚ)), ((.missingEdgeUnion 4), (5/8 : ℚ)), ((.pairExtension 5), (1/20 : ℚ)), ((.pairExtension 6), (1/40 : ℚ))]⟩,
  ⟨16, 10, 5, (520/801 : ℚ), (281/801 : ℚ), (40262/267 : ℚ), (-323716/267 : ℚ), (-592538/2403 : ℚ), [(.edgeBudget, (66986/2403 : ℚ)), ((.matchingExcess 2), (2600/801 : ℚ)), ((.matchingExcess 3), (239/267 : ℚ)), ((.matchingExcess 4), (260/2403 : ℚ)), ((.missingEdgeUnion 3), (3346/801 : ℚ)), ((.pairExtension 5), (302/4005 : ℚ)), ((.pairExtension 6), (281/12015 : ℚ))]⟩,
  ⟨16, 11, 5, 1, 0, (4491/20 : ℚ), (-9735/4 : ℚ), (-8303/20 : ℚ), [(.edgeBudget, (933/20 : ℚ)), ((.matchingExcess 2), 5), ((.matchingExcess 3), 1), ((.matchingExcess 4), (13/20 : ℚ)), ((.missingEdgeUnion 3), 5), ((.missingEdgeUnion 4), (71/20 : ℚ)), ((.missingEdgeUnion 5), 1)]⟩,
  ⟨16, 11, 6, (14/43 : ℚ), (29/43 : ℚ), (6529/43 : ℚ), (-81719/86 : ℚ), (-14207/86 : ℚ), [(.edgeBudget, (1625/86 : ℚ)), ((.matchingExcess 2), (271/86 : ℚ)), ((.pairExtension 3), (14/129 : ℚ)), ((.missingEdgeUnion 4), (3626/1075 : ℚ)), ((.pairExtension 4), (4438/3225 : ℚ)), ((.pairExtension 5), (191/430 : ℚ))]⟩,
  ⟨16, 12, 5, 1, 0, 377, -1881, -270, [(.edgeBudget, 33), ((.matchingExcess 2), 2), ((.matchingExcess 3), 1), ((.matchingExcess 4), (1/8 : ℚ)), ((.subsetCount 3), (11/2 : ℚ)), ((.missingEdgeUnion 3), (23/2 : ℚ))]⟩,
  ⟨16, 12, 6, (6/13 : ℚ), (7/13 : ℚ), (2234/13 : ℚ), (-11484/13 : ℚ), -120, [(.edgeBudget, (200/13 : ℚ)), ((.matchingExcess 2), (9/13 : ℚ)), ((.subsetCount 4), (237/13 : ℚ)), ((.pairExtension 3), (2/13 : ℚ)), ((.missingEdgeUnion 4), (161/13 : ℚ))]⟩,
  ⟨16, 13, 5, 1, 0, 607, -520, -98, [(.edgeBudget, 14), ((.subsetCount 3), 17), ((.missingEdgeUnion 3), 16)]⟩,
  ⟨16, 13, 6, 1, 0, 370, 429, -14, [((.subsetCount 2), (17/3 : ℚ)), ((.pairExtension 3), (2/3 : ℚ))]⟩,
  ⟨16, 14, 5, 1, 0, 994, 546, -35, [(.edgeBudget, 5), ((.subsetCount 2), 7)]⟩,
  ⟨16, 14, 6, 1, 0, 968, 1001, -14, [((.subsetCount 2), 5)]⟩,
  ⟨16, 14, 7, (19/62 : ℚ), (43/62 : ℚ), (855/2 : ℚ), (11297/31 : ℚ), (-158/31 : ℚ), [(.edgeBudget, (22/31 : ℚ)), ((.subsetCount 2), (77/62 : ℚ))]⟩,
  ⟨16, 15, 5, 1, 0, 1633, 1638, -5, []⟩,
  ⟨16, 15, 6, 1, 0, 1988, 2002, -14, []⟩,
  ⟨16, 15, 7, 1, 0, 1388, 1430, -42, []⟩,
  ⟨17, 10, 6, (1/3 : ℚ), (2/3 : ℚ), (1027/6 : ℚ), -1649, -344, [(.edgeBudget, (113/3 : ℚ)), ((.matchingExcess 2), (10/3 : ℚ)), ((.matchingExcess 3), (7/6 : ℚ)), ((.subsetCount 2), (136/21 : ℚ)), ((.missingEdgeUnion 3), (14/3 : ℚ)), ((.pairExtension 4), (1/18 : ℚ)), ((.pairExtension 5), (1/5 : ℚ)), ((.pairExtension 6), (1/9 : ℚ)), ((.pairExtension 7), (2/63 : ℚ))]⟩,
  ⟨17, 11, 6, (5/11 : ℚ), (6/11 : ℚ), (1880/11 : ℚ), -1658, (-3246/11 : ℚ), [(.edgeBudget, (346/11 : ℚ)), ((.matchingExcess 2), (30/11 : ℚ)), ((.matchingExcess 3), (12/11 : ℚ)), ((.missingEdgeUnion 3), (56/11 : ℚ)), ((.pairExtension 4), (7/33 : ℚ)), ((.missingEdgeUnion 5), (224/297 : ℚ)), ((.pairExtension 5), (1007/2970 : ℚ)), ((.pairExtension 6), (19/165 : ℚ))]⟩,
  ⟨17, 12, 6, (7/15 : ℚ), (8/15 : ℚ), (1092/5 : ℚ), (-6666/5 : ℚ), -202, [(.edgeBudget, (111/5 : ℚ)), ((.matchingExcess 2), (8/3 : ℚ)), ((.matchingExcess 3), (1/15 : ℚ)), ((.subsetCount 4), (79/9 : ℚ)), ((.missingEdgeUnion 4), (143/45 : ℚ)), ((.pairExtension 5), (7/15 : ℚ))]⟩,
  ⟨17, 13, 6, 1, 0, 390, -663, -126, [(.edgeBudget, 14), ((.subsetCount 2), (41/2 : ℚ)), ((.pairExtension 3), (2/3 : ℚ)), ((.pairExtension 4), (1/6 : ℚ))]⟩,
  ⟨17, 13, 7, 0, 1, 411, -1755, -204, [(.edgeBudget, 28), ((.subsetCount 2), 63), ((.pairExtension 3), 14), ((.pairExtension 4), 7)]⟩,
  ⟨17, 14, 6, 1, 0, 970, -273, -126, [(.edgeBudget, 14), ((.subsetCount 3), 21), ((.missingEdgeUnion 3), 19)]⟩,
  ⟨17, 14, 7, (19/43 : ℚ), (24/43 : ℚ), (18914/43 : ℚ), (-18499/43 : ℚ), (-3300/43 : ℚ), [(.edgeBudget, (406/43 : ℚ)), ((.subsetCount 2), (458/43 : ℚ)), ((.subsetCount 3), (33/43 : ℚ))]⟩,
  ⟨17, 15, 6, 1, 0, 1969, 2002, -14, [((.subsetCount 2), 5)]⟩,
  ⟨17, 15, 7, 1, 0, 1332, 1430, -42, [((.subsetCount 2), 14)]⟩,
  ⟨17, 16, 6, 1, 0, 3626, 3640, -14, []⟩,
  ⟨17, 16, 7, 1, 0, 3390, 3432, -42, []⟩,
  ⟨17, 16, 8, 0, 1, 1430, 1430, 0, []⟩,
  ⟨18, 10, 6, (9/25 : ℚ), (16/25 : ℚ), (4504/25 : ℚ), (-54018/25 : ℚ), (-2294/5 : ℚ), [(.edgeBudget, (1224/25 : ℚ)), ((.matchingExcess 2), (16/5 : ℚ)), ((.matchingExcess 3), (32/25 : ℚ)), ((.matchingExcess 4), (2/25 : ℚ)), ((.subsetCount 5), (44/25 : ℚ)), ((.missingEdgeUnion 3), (126/25 : ℚ)), ((.missingEdgeUnion 4), (1/25 : ℚ)), ((.missingEdgeUnion 6), (1663/2450 : ℚ)), ((.pairExtension 6), (1097/7350 : ℚ)), ((.pairExtension 7), (16/525 : ℚ))]⟩,
  ⟨18, 11, 6, (14/29 : ℚ), (15/29 : ℚ), (7070/29 : ℚ), (-165825/58 : ℚ), (-31073/58 : ℚ), [(.edgeBudget, (3087/58 : ℚ)), ((.matchingExcess 2), 5), ((.matchingExcess 3), (165/116 : ℚ)), ((.missingEdgeUnion 3), (182/29 : ℚ)), ((.pairExtension 4), (7/87 : ℚ)), ((.pairExtension 5), (13/58 : ℚ)), ((.missingEdgeUnion 6), (9991/5684 : ℚ)), ((.pairExtension 6), (19007/85260 : ℚ)), ((.pairExtension 7), (5/203 : ℚ))]⟩,
  ⟨18, 12, 6, (4/7 : ℚ), (3/7 : ℚ), (6794/21 : ℚ), (-120912/35 : ℚ), (-19674/35 : ℚ), [(.edgeBudget, (1902/35 : ℚ)), ((.matchingExcess 2), 5), ((.matchingExcess 3), (181/105 : ℚ)), ((.missingEdgeUnion 3), (184/21 : ℚ)), ((.pairExtension 4), (2/21 : ℚ)), ((.pairExtension 5), (9/35 : ℚ)), ((.pairExtension 6), (11/105 : ℚ))]⟩,
  ⟨18, 13, 6, 1, 0, 509, -4017, -573, [(.edgeBudget, 57), ((.matchingExcess 2), 5), ((.pairExtension 3), (2/3 : ℚ)), ((.pairExtension 4), (1/6 : ℚ)), ((.missingEdgeUnion 5), 44), ((.pairExtension 5), (9/2 : ℚ))]⟩,
  ⟨18, 13, 7, (6/19 : ℚ), (13/19 : ℚ), 427, (-57369/19 : ℚ), (-7935/19 : ℚ), [(.edgeBudget, (807/19 : ℚ)), ((.matchingExcess 2), (87/19 : ℚ)), ((.pairExtension 3), (2/19 : ℚ)), ((.pairExtension 4), (43/19 : ℚ)), ((.missingEdgeUnion 5), (5204/171 : ℚ)), ((.pairExtension 5), (740/171 : ℚ))]⟩,
  ⟨18, 14, 6, 1, 0, 1088, -2821, -378, [(.edgeBudget, 42), ((.subsetCount 3), (51/2 : ℚ)), ((.subsetCount 4), 1), ((.missingEdgeUnion 3), (47/2 : ℚ))]⟩,
  ⟨18, 14, 7, (19/43 : ℚ), (24/43 : ℚ), (21714/43 : ℚ), (-73463/43 : ℚ), (-8746/43 : ℚ), [(.edgeBudget, (1010/43 : ℚ)), ((.matchingExcess 2), (1/43 : ℚ)), ((.subsetCount 2), (2355/86 : ℚ)), ((.subsetCount 3), (33/43 : ℚ)), ((.pairExtension 4), (245/86 : ℚ))]⟩,
  ⟨18, 15, 6, 1, 0, 2027, -2408, -378, [(.edgeBudget, 42), ((.missingEdgeUnion 3), (143/2 : ℚ)), ((.pairExtension 3), (49/2 : ℚ))]⟩,
  ⟨18, 15, 7, 1, 0, 1257, 1430, -42, [((.subsetCount 2), 14), ((.subsetCount 3), 5)]⟩,
  ⟨18, 16, 6, 1, 0, 3607, 3640, -14, [((.subsetCount 2), 5)]⟩,
  ⟨18, 16, 7, 1, 0, 3334, 3432, -42, [((.subsetCount 2), 14)]⟩,
  ⟨18, 16, 8, (215/718 : ℚ), (503/718 : ℚ), (512301/359 : ℚ), (512890/359 : ℚ), (-843/718 : ℚ), [(.edgeBudget, (4/359 : ℚ)), ((.subsetCount 2), (290/359 : ℚ))]⟩,
  ⟨18, 17, 6, 1, 0, 6174, 6188, -14, []⟩,
  ⟨18, 17, 7, 1, 0, 7030, 7072, -42, []⟩,
  ⟨18, 17, 8, 1, 0, 4730, 4862, -132, []⟩,
  ⟨19, 10, 6, (1/2 : ℚ), (1/2 : ℚ), 272, (-9087/2 : ℚ), -994, [(.edgeBudget, (203/2 : ℚ)), ((.matchingExcess 2), 5), ((.matchingExcess 3), 2), ((.matchingExcess 4), (1/2 : ℚ)), ((.missingEdgeUnion 3), (13/2 : ℚ)), ((.missingEdgeUnion 4), 2), ((.pairExtension 5), (1/20 : ℚ)), ((.missingEdgeUnion 6), (79/392 : ℚ)), ((.pairExtension 6), (157/1960 : ℚ)), ((.pairExtension 7), (1/42 : ℚ))]⟩,
  ⟨19, 11, 6, (4/7 : ℚ), (3/7 : ℚ), (4947/14 : ℚ), (-256223/49 : ℚ), (-49545/49 : ℚ), [(.edgeBudget, (4709/49 : ℚ)), ((.matchingExcess 2), (711/98 : ℚ)), ((.matchingExcess 3), 2), ((.matchingExcess 4), (3/7 : ℚ)), ((.missingEdgeUnion 3), (57/7 : ℚ)), ((.missingEdgeUnion 4), 2), ((.pairExtension 5), (1/10 : ℚ)), ((.pairExtension 6), (8/105 : ℚ)), ((.pairExtension 7), (1/49 : ℚ))]⟩,
  ⟨19, 12, 6, (4131/6784 : ℚ), (2653/6784 : ℚ), (840577/1696 : ℚ), (-9942801/1696 : ℚ), (-1690503/1696 : ℚ), [(.edgeBudget, (308081/3392 : ℚ)), ((.matchingExcess 2), (28917/3392 : ℚ)), ((.matchingExcess 3), 2), ((.matchingExcess 4), (1781/6784 : ℚ)), ((.missingEdgeUnion 3), (67537/6784 : ℚ)), ((.missingEdgeUnion 4), (521/424 : ℚ)), ((.pairExtension 5), (3089/16960 : ℚ)), ((.pairExtension 6), (4567/50880 : ℚ)), ((.pairExtension 7), (379/20352 : ℚ))]⟩,
  ⟨19, 12, 7, (14/43 : ℚ), (29/43 : ℚ), (35247/86 : ℚ), (-297033/43 : ℚ), (-50778/43 : ℚ), [(.edgeBudget, (4603/43 : ℚ)), ((.matchingExcess 2), (406/43 : ℚ)), ((.matchingExcess 3), (271/86 : ℚ)), ((.missingEdgeUnion 3), (588/43 : ℚ)), ((.pairExtension 4), (7/129 : ℚ)), ((.pairExtension 5), (21/43 : ℚ)), ((.missingEdgeUnion 6), (5637/2107 : ℚ)), ((.pairExtension 6), (14996/31605 : ℚ)), ((.pairExtension 7), (34/301 : ℚ))]⟩,
  ⟨19, 13, 6, 1, 0, 754, -12129, -1787, [(.edgeBudget, 161), ((.matchingExcess 2), 14), ((.matchingExcess 3), 2), ((.matchingExcess 4), 1), ((.matchingExcess 5), 1), ((.missingEdgeUnion 3), 10), ((.missingEdgeUnion 4), 6), ((.missingEdgeUnion 5), 7), ((.missingEdgeUnion 6), 1)]⟩,
  ⟨19, 13, 7, (61/166 : ℚ), (105/166 : ℚ), (71609/166 : ℚ), (-847899/166 : ℚ), (-64353/83 : ℚ), [(.edgeBudget, (5724/83 : ℚ)), ((.matchingExcess 2), (735/83 : ℚ)), ((.matchingExcess 3), (193/166 : ℚ)), ((.missingEdgeUnion 3), (540/83 : ℚ)), ((.pairExtension 4), (247/166 : ℚ)), ((.pairExtension 5), (86/83 : ℚ)), ((.missingEdgeUnion 6), (3081/166 : ℚ)), ((.pairExtension 6), (279/166 : ℚ))]⟩,
  ⟨19, 14, 6, 1, 0, 1401, -11557, -1530, [(.edgeBudget, 138), ((.matchingExcess 2), 14), ((.matchingExcess 3), 2), ((.matchingExcess 5), 1), ((.subsetCount 3), 8), ((.subsetCount 4), 1), ((.missingEdgeUnion 3), 20), ((.missingEdgeUnion 5), 8)]⟩,
  ⟨19, 14, 7, (11/24 : ℚ), (13/24 : ℚ), (1789/3 : ℚ), (-45253/8 : ℚ), (-2955/4 : ℚ), [(.edgeBudget, (535/8 : ℚ)), ((.matchingExcess 2), (91/12 : ℚ)), ((.matchingExcess 3), (17/24 : ℚ)), ((.missingEdgeUnion 3), (33/8 : ℚ)), ((.pairExtension 4), (115/48 : ℚ)), ((.missingEdgeUnion 5), (719/27 : ℚ)), ((.pairExtension 5), (1739/432 : ℚ))]⟩,
  ⟨19, 15, 6, 1, 0, 2326, -8498, -1008, [(.edgeBudget, 100), ((.matchingExcess 2), 5), ((.subsetCount 2), (421/6 : ℚ)), ((.subsetCount 3), 2), ((.pairExtension 4), (1/6 : ℚ))]⟩,
  ⟨19, 15, 7, 1, 0, 1240, -2980, -462, [(.edgeBudget, 42), ((.subsetCount 2), (179/3 : ℚ)), ((.pairExtension 3), (5/3 : ℚ)), ((.pairExtension 4), (1/3 : ℚ))]⟩,
  ⟨19, 15, 8, (4/235 : ℚ), (231/235 : ℚ), (294297/235 : ℚ), (-376026/47 : ℚ), (-39141/47 : ℚ), [(.edgeBudget, (21052/235 : ℚ)), ((.matchingExcess 2), (43/47 : ℚ)), ((.subsetCount 2), (43844/235 : ℚ)), ((.pairExtension 3), (9768/235 : ℚ)), ((.pairExtension 4), (4972/235 : ℚ))]⟩,
  ⟨19, 16, 6, 1, 0, 3749, -1400, -378, [(.edgeBudget, 42), ((.subsetCount 2), (143/3 : ℚ)), ((.pairExtension 3), (2/3 : ℚ))]⟩,
  ⟨19, 16, 7, 1, 0, 3259, 3432, -42, [((.subsetCount 2), (47/3 : ℚ)), ((.pairExtension 3), (5/3 : ℚ))]⟩,
  ⟨19, 16, 8, (215/503 : ℚ), (288/503 : ℚ), (721622/503 : ℚ), (144010/503 : ℚ), (-45690/503 : ℚ), [(.edgeBudget, (4794/503 : ℚ)), ((.subsetCount 3), (6648/503 : ℚ)), ((.missingEdgeUnion 3), (6076/503 : ℚ))]⟩,
  ⟨19, 17, 6, 1, 0, 6155, 6188, -14, [((.subsetCount 2), 5)]⟩,
  ⟨19, 17, 7, 1, 0, 6974, 7072, -42, [((.subsetCount 2), 14)]⟩,
  ⟨19, 17, 8, 1, 0, 4556, 4862, -132, [((.subsetCount 2), 42)]⟩,
  ⟨19, 18, 6, 1, 0, 9982, 9996, -14, []⟩,
  ⟨19, 18, 7, 1, 0, 13218, 13260, -42, []⟩,
  ⟨19, 18, 8, 1, 0, 11802, 11934, -132, []⟩,
  ⟨19, 18, 9, 0, 1, 4862, 4862, 0, []⟩,
  ⟨20, 10, 6, (693/1094 : ℚ), (401/1094 : ℚ), (254052/547 : ℚ), (-5409168/547 : ℚ), (-3560203/1641 : ℚ), [(.edgeBudget, (360844/1641 : ℚ)), ((.matchingExcess 2), 5), ((.matchingExcess 3), (3465/1094 : ℚ)), ((.matchingExcess 4), (1715/1641 : ℚ)), ((.matchingExcess 5), (146/547 : ℚ)), ((.missingEdgeUnion 3), (8935/1094 : ℚ)), ((.missingEdgeUnion 4), (2116/547 : ℚ)), ((.missingEdgeUnion 5), (767/1094 : ℚ)), ((.pairExtension 6), (17/547 : ℚ)), ((.pairExtension 7), (401/22974 : ℚ))]⟩,
  ⟨20, 11, 6, (2477/3793 : ℚ), (1316/3793 : ℚ), (2387980/3793 : ℚ), (-40876913/3793 : ℚ), (-7946785/3793 : ℚ), [(.edgeBudget, (746375/3793 : ℚ)), ((.matchingExcess 2), (34678/3793 : ℚ)), ((.matchingExcess 3), (12385/3793 : ℚ)), ((.matchingExcess 4), (3483/3793 : ℚ)), ((.matchingExcess 5), (503/3793 : ℚ)), ((.missingEdgeUnion 3), (43735/3793 : ℚ)), ((.missingEdgeUnion 4), (16254/3793 : ℚ)), ((.missingEdgeUnion 5), (541/3793 : ℚ)), ((.pairExtension 6), (929/18965 : ℚ)), ((.pairExtension 7), (188/11379 : ℚ))]⟩,
  ⟨20, 12, 6, (7/10 : ℚ), (3/10 : ℚ), (28307/35 : ℚ), (-2370918/245 : ℚ), (-82452/49 : ℚ), [(.edgeBudget, (36413/245 : ℚ)), ((.matchingExcess 2), (49/5 : ℚ)), ((.matchingExcess 3), (7/2 : ℚ)), ((.matchingExcess 4), (787/2450 : ℚ)), ((.matchingExcess 5), (1/10 : ℚ)), ((.missingEdgeUnion 3), (31/2 : ℚ)), ((.missingEdgeUnion 4), (1871/1225 : ℚ)), ((.pairExtension 6), (4/75 : ℚ)), ((.pairExtension 7), (1/70 : ℚ))]⟩,
  ⟨20, 12, 7, (24/71 : ℚ), (47/71 : ℚ), (96713/213 : ℚ), (-621071/71 : ℚ), (-107714/71 : ℚ), [(.edgeBudget, (28721/213 : ℚ)), ((.matchingExcess 2), (658/71 : ℚ)), ((.matchingExcess 3), (235/71 : ℚ)), ((.matchingExcess 4), (19/213 : ℚ)), ((.missingEdgeUnion 3), (1008/71 : ℚ)), ((.missingEdgeUnion 4), (183977/74550 : ℚ)), ((.pairExtension 4), (169277/447300 : ℚ)), ((.pairExtension 5), (161/355 : ℚ)), ((.pairExtension 6), (101/355 : ℚ)), ((.pairExtension 7), (164/1491 : ℚ)), ((.pairExtension 8), (47/1988 : ℚ))]⟩,
  ⟨20, 13, 6, 1, 0, (122353/96 : ℚ), (-131599/8 : ℚ), (-120055/48 : ℚ), [(.edgeBudget, (10387/48 : ℚ)), ((.matchingExcess 2), 14), ((.matchingExcess 3), 5), ((.matchingExcess 4), (277/480 : ℚ)), ((.matchingExcess 5), (1/8 : ℚ)), ((.missingEdgeUnion 3), 25), ((.missingEdgeUnion 4), (1459/480 : ℚ)), ((.missingEdgeUnion 6), 1)]⟩,
  ⟨20, 13, 7, (6/13 : ℚ), (7/13 : ℚ), (7335/13 : ℚ), -8085, (-16002/13 : ℚ), [(.edgeBudget, (1386/13 : ℚ)), ((.matchingExcess 2), (98/13 : ℚ)), ((.matchingExcess 3), (35/13 : ℚ)), ((.missingEdgeUnion 3), (173/13 : ℚ)), ((.missingEdgeUnion 4), (4684/2275 : ℚ)), ((.pairExtension 4), (2867/6825 : ℚ)), ((.pairExtension 5), (38/65 : ℚ)), ((.pairExtension 6), (62/195 : ℚ)), ((.pairExtension 7), (29/273 : ℚ))]⟩,
  ⟨20, 14, 6, 1, 0, (157019/81 : ℚ), (-395122/27 : ℚ), (-54092/27 : ℚ), [(.edgeBudget, (4639/27 : ℚ)), ((.matchingExcess 2), 14), ((.matchingExcess 3), (1361/324 : ℚ)), ((.matchingExcess 4), (1/8 : ℚ)), ((.matchingExcess 5), (1/9 : ℚ)), ((.missingEdgeUnion 3), (1361/54 : ℚ)), ((.missingEdgeUnion 6), 1)]⟩,
  ⟨20, 14, 7, (13/24 : ℚ), (11/24 : ℚ), (4651/6 : ℚ), (-83759/12 : ℚ), (-2860/3 : ℚ), [(.edgeBudget, (977/12 : ℚ)), ((.matchingExcess 2), (77/12 : ℚ)), ((.matchingExcess 3), (55/24 : ℚ)), ((.missingEdgeUnion 3), (103/8 : ℚ)), ((.pairExtension 4), (5/48 : ℚ)), ((.missingEdgeUnion 5), (22/27 : ℚ)), ((.pairExtension 5), (1769/2160 : ℚ)), ((.pairExtension 6), (43/120 : ℚ))]⟩,
  ⟨20, 15, 6, 1, 0, 2930, -20468, -2418, [(.edgeBudget, 214), ((.matchingExcess 2), 14), ((.matchingExcess 3), 2), ((.matchingExcess 4), 1), ((.matchingExcess 5), (1/10 : ℚ)), ((.subsetCount 2), 64), ((.missingEdgeUnion 3), 14), ((.missingEdgeUnion 4), 8)]⟩,
  ⟨20, 15, 7, 1, 0, 1361, -12430, -1452, [(.edgeBudget, 132), ((.missingEdgeUnion 3), (1521/20 : ℚ)), ((.pairExtension 3), (1621/60 : ℚ)), ((.pairExtension 4), (1/3 : ℚ)), ((.pairExtension 5), (1/10 : ℚ))]⟩,
  ⟨20, 15, 8, (19/62 : ℚ), (43/62 : ℚ), (77229/62 : ℚ), (-320165/31 : ℚ), (-72969/62 : ℚ), [(.edgeBudget, (3342/31 : ℚ)), ((.matchingExcess 2), (168/31 : ℚ)), ((.pairExtension 3), (11/62 : ℚ)), ((.pairExtension 4), (847/124 : ℚ)), ((.missingEdgeUnion 5), (31120/279 : ℚ)), ((.pairExtension 5), (16849/1116 : ℚ))]⟩,
  ⟨20, 16, 6, 1, 0, 4324, -17360, -1843, [(.edgeBudget, 175), ((.matchingExcess 2), 5), ((.pairExtension 3), (2/3 : ℚ)), ((.missingEdgeUnion 4), (849/5 : ℚ)), ((.pairExtension 4), (427/15 : ℚ))]⟩,
  ⟨20, 16, 7, 1, 0, 3458, -12408, -1452, [(.edgeBudget, 132), ((.pairExtension 3), (5/3 : ℚ)), ((.missingEdgeUnion 4), (898/5 : ℚ)), ((.pairExtension 4), (454/15 : ℚ))]⟩,
  ⟨20, 16, 8, (215/503 : ℚ), (288/503 : ℚ), (797475/503 : ℚ), (-3842630/503 : ℚ), (-399036/503 : ℚ), [(.edgeBudget, (38016/503 : ℚ)), ((.missingEdgeUnion 3), (264487/4024 : ℚ)), ((.pairExtension 3), (269063/12072 : ℚ)), ((.pairExtension 4), (26411/3018 : ℚ))]⟩,
  ⟨20, 17, 6, 1, 0, 6477, -6052, -858, [(.edgeBudget, 90), ((.subsetCount 3), 97), ((.missingEdgeUnion 3), 95)]⟩,
  ⟨20, 17, 7, 1, 0, 6983, 1360, -462, [(.edgeBudget, 42), ((.subsetCount 3), 61), ((.missingEdgeUnion 3), 56)]⟩,
  ⟨20, 17, 8, 1, 0, 4326, 4862, -132, [((.subsetCount 2), (140/3 : ℚ)), ((.pairExtension 3), (14/3 : ℚ))]⟩,
  ⟨20, 18, 6, 1, 0, 9977, 7854, -126, [(.edgeBudget, 14), ((.subsetCount 2), 19)]⟩,
  ⟨20, 18, 7, 1, 0, 13162, 13260, -42, [((.subsetCount 2), 14)]⟩,
  ⟨20, 18, 8, 1, 0, 11628, 11934, -132, [((.subsetCount 2), 42)]⟩,
  ⟨20, 18, 9, (159/541 : ℚ), (382/541 : ℚ), (2627296/541 : ℚ), 4862, (-1237/541 : ℚ), [((.subsetCount 2), (572/541 : ℚ))]⟩,
  ⟨20, 19, 6, 1, 0, 15490, 15504, -14, []⟩,
  ⟨20, 19, 7, 1, 0, 23214, 23256, -42, []⟩,
  ⟨20, 19, 8, 1, 0, 25062, 25194, -132, []⟩,
  ⟨20, 19, 9, 1, 0, 16367, 16796, -429, []⟩
]

set_option maxHeartbeats 0 in
/-- Every certificate with `n ≤ 20` passes the checker (evaluated by the kernel). -/
theorem certs_ok : ∀ c ∈ certs20, c.ok = true := by
  have h00 : ((certs20.drop 0).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h01 : ((certs20.drop 4).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h02 : ((certs20.drop 8).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h03 : ((certs20.drop 12).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h04 : ((certs20.drop 16).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h05 : ((certs20.drop 20).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h06 : ((certs20.drop 24).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h07 : ((certs20.drop 28).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h08 : ((certs20.drop 32).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h09 : ((certs20.drop 36).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h10 : ((certs20.drop 40).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h11 : ((certs20.drop 44).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h12 : ((certs20.drop 48).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h13 : ((certs20.drop 52).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h14 : ((certs20.drop 56).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h15 : ((certs20.drop 60).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h16 : ((certs20.drop 64).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h17 : ((certs20.drop 68).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h18 : ((certs20.drop 72).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h19 : ((certs20.drop 76).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h20 : ((certs20.drop 80).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h21 : ((certs20.drop 84).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h22 : ((certs20.drop 88).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h23 : ((certs20.drop 92).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h24 : ((certs20.drop 96).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h25 : ((certs20.drop 100).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h26 : ((certs20.drop 104).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h27 : ((certs20.drop 108).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h28 : ((certs20.drop 112).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h29 : ((certs20.drop 116).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h30 : ((certs20.drop 120).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h31 : ((certs20.drop 124).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  have h32 : ((certs20.drop 128).take 4).all Cert.ok = true := by
    as_aux_lemma => decide +kernel
  intro c hc
  have hsplit : certs20 = ((certs20.drop 0).take 4) ++ ((certs20.drop 4).take 4) ++ ((certs20.drop 8).take 4) ++ ((certs20.drop 12).take 4) ++ ((certs20.drop 16).take 4) ++ ((certs20.drop 20).take 4) ++ ((certs20.drop 24).take 4) ++ ((certs20.drop 28).take 4) ++ ((certs20.drop 32).take 4) ++ ((certs20.drop 36).take 4) ++ ((certs20.drop 40).take 4) ++ ((certs20.drop 44).take 4) ++ ((certs20.drop 48).take 4) ++ ((certs20.drop 52).take 4) ++ ((certs20.drop 56).take 4) ++ ((certs20.drop 60).take 4) ++ ((certs20.drop 64).take 4) ++ ((certs20.drop 68).take 4) ++ ((certs20.drop 72).take 4) ++ ((certs20.drop 76).take 4) ++ ((certs20.drop 80).take 4) ++ ((certs20.drop 84).take 4) ++ ((certs20.drop 88).take 4) ++ ((certs20.drop 92).take 4) ++ ((certs20.drop 96).take 4) ++ ((certs20.drop 100).take 4) ++ ((certs20.drop 104).take 4) ++ ((certs20.drop 108).take 4) ++ ((certs20.drop 112).take 4) ++ ((certs20.drop 116).take 4) ++ ((certs20.drop 120).take 4) ++ ((certs20.drop 124).take 4) ++ ((certs20.drop 128).take 4) := by
    rfl
  rw [hsplit] at hc
  simp only [List.mem_append, or_assoc] at hc
  rcases hc with hc00 | hc01 | hc02 | hc03 | hc04 | hc05 | hc06 | hc07 | hc08 | hc09 | hc10 | hc11 | hc12 | hc13 | hc14 | hc15 | hc16 | hc17 | hc18 | hc19 | hc20 | hc21 | hc22 | hc23 | hc24 | hc25 | hc26 | hc27 | hc28 | hc29 | hc30 | hc31 | hc32
  · exact (List.all_eq_true.mp h00) c hc00
  · exact (List.all_eq_true.mp h01) c hc01
  · exact (List.all_eq_true.mp h02) c hc02
  · exact (List.all_eq_true.mp h03) c hc03
  · exact (List.all_eq_true.mp h04) c hc04
  · exact (List.all_eq_true.mp h05) c hc05
  · exact (List.all_eq_true.mp h06) c hc06
  · exact (List.all_eq_true.mp h07) c hc07
  · exact (List.all_eq_true.mp h08) c hc08
  · exact (List.all_eq_true.mp h09) c hc09
  · exact (List.all_eq_true.mp h10) c hc10
  · exact (List.all_eq_true.mp h11) c hc11
  · exact (List.all_eq_true.mp h12) c hc12
  · exact (List.all_eq_true.mp h13) c hc13
  · exact (List.all_eq_true.mp h14) c hc14
  · exact (List.all_eq_true.mp h15) c hc15
  · exact (List.all_eq_true.mp h16) c hc16
  · exact (List.all_eq_true.mp h17) c hc17
  · exact (List.all_eq_true.mp h18) c hc18
  · exact (List.all_eq_true.mp h19) c hc19
  · exact (List.all_eq_true.mp h20) c hc20
  · exact (List.all_eq_true.mp h21) c hc21
  · exact (List.all_eq_true.mp h22) c hc22
  · exact (List.all_eq_true.mp h23) c hc23
  · exact (List.all_eq_true.mp h24) c hc24
  · exact (List.all_eq_true.mp h25) c hc25
  · exact (List.all_eq_true.mp h26) c hc26
  · exact (List.all_eq_true.mp h27) c hc27
  · exact (List.all_eq_true.mp h28) c hc28
  · exact (List.all_eq_true.mp h29) c hc29
  · exact (List.all_eq_true.mp h30) c hc30
  · exact (List.all_eq_true.mp h31) c hc31
  · exact (List.all_eq_true.mp h32) c hc32

/-- The keys of the certificates are exactly the parameter domain (11) through order 20, in order. -/
theorem certs_cover : certs20.map Cert.key = paramDomain 20 := by
  decide +kernel

end Fiber
end Erdos993Lean
