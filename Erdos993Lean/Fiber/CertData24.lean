import Erdos993Lean.Fiber.CertData

/-!
# The added certificates at orders 21--24, reusing the checked order-20 prefix

Source: `TWIN_v1.5`, Part I Theorem `p1:thm:certificates` and the certificate appendix;
the original `BINOMIAL_FIBER_COMPLETION/CERTIFICATES.json`, SHA256
`ac4d890f43f2acd377ce981486a38609ca524a3fecb3e2dffeafcd791a13c975`.

The original 130-record definition and public theorem statements are retained verbatim from
commit `aa8ba75` in `Fiber/CertData.lean`. Its checker proof now uses 33 kernel slices of at most four
records plus ordinary membership assembly to bound the kernel cache.  This module adds the exact 119 records with `21 <= n <= 24`, in the
same source order, without changing the checker, certificate field translation or statements.
The combined list has all 249 certificates through order 24.  Every new chunk has at most
four certificates, evaluated sequentially by `decide +kernel`; the original 130-check theorem
is used directly on original-list membership.  Coverage is checked by the kernel for the
combined list.  No compiled evaluation, new axiom or forest enumeration is used.

Named consumers: `Fiber.unimodal_of_card_le_24` and `Fiber.floorStatement_25_fiber`.
Namespace `Order24` preserves the original `Fiber.certs_ok` / `Fiber.certs_cover` without
collision.  This is a lane-local formalization, with no campaign promotion verdict.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace Erdos993Lean.Fiber.Order24

private def addedPart00 : List Cert := [
  ⟨21, 11, 7, (9/25 : ℚ), (16/25 : ℚ), (11562/25 : ℚ), (-344278/25 : ℚ), (-68112/25 : ℚ), [(.edgeBudget, (6286/25 : ℚ)), ((.matchingExcess 2), (224/25 : ℚ)), ((.matchingExcess 3), (16/5 : ℚ)), ((.matchingExcess 4), (32/25 : ℚ)), ((.matchingExcess 5), (2/25 : ℚ)), ((.missingEdgeUnion 3), (259/25 : ℚ)), ((.missingEdgeUnion 4), (126/25 : ℚ)), ((.missingEdgeUnion 5), (1724/4725 : ℚ)), ((.pairExtension 5), (307/9450 : ℚ)), ((.pairExtension 6), (44/375 : ℚ)), ((.pairExtension 7), (13/175 : ℚ)), ((.pairExtension 8), (4/175 : ℚ))]⟩,
  ⟨21, 12, 7, (14/29 : ℚ), (15/29 : ℚ), (209026/435 : ℚ), (-3624269/290 : ℚ), (-321739/145 : ℚ), [(.edgeBudget, (331849/1740 : ℚ)), ((.matchingExcess 2), (19507/1740 : ℚ)), ((.matchingExcess 3), (75/29 : ℚ)), ((.matchingExcess 4), (30/29 : ℚ)), ((.missingEdgeUnion 3), 10), ((.missingEdgeUnion 4), (137/29 : ℚ)), ((.pairExtension 5), (7/145 : ℚ)), ((.pairExtension 6), (13/87 : ℚ)), ((.pairExtension 7), (46/609 : ℚ)), ((.pairExtension 8), (15/812 : ℚ))]⟩,
  ⟨21, 13, 7, (43271/86667 : ℚ), (43396/86667 : ℚ), (62689231/86667 : ℚ), (-472501354/28889 : ℚ), (-75448397/28889 : ℚ), [(.edgeBudget, (6137269/28889 : ℚ)), ((.matchingExcess 2), 14), ((.matchingExcess 3), 5), ((.matchingExcess 4), (16529/28889 : ℚ)), ((.missingEdgeUnion 3), (272507/12381 : ℚ)), ((.missingEdgeUnion 4), (84792/28889 : ℚ)), ((.pairExtension 5), (58278/144445 : ℚ)), ((.pairExtension 6), (347918/1300005 : ℚ)), ((.pairExtension 7), (19301/202223 : ℚ)), ((.pairExtension 8), (10849/606669 : ℚ))]⟩,
  ⟨21, 14, 7, (14510/26257 : ℚ), (11747/26257 : ℚ), (28662710/26257 : ℚ), (-2101541/121 : ℚ), (-64595536/26257 : ℚ), [(.edgeBudget, (165650/847 : ℚ)), ((.matchingExcess 2), 14), ((.matchingExcess 3), 5), ((.matchingExcess 4), (6899/26257 : ℚ)), ((.missingEdgeUnion 3), (98514/3751 : ℚ)), ((.missingEdgeUnion 4), (2820/2387 : ℚ)), ((.pairExtension 5), (86043/131285 : ℚ)), ((.pairExtension 6), (26674/78771 : ℚ)), ((.pairExtension 7), (7996/78771 : ℚ))]⟩
]

private theorem addedPart00_ok : addedPart00.all Cert.ok = true := by
  decide +kernel

private def addedPart01 : List Cert := [
  ⟨21, 14, 8, (6/19 : ℚ), (13/19 : ℚ), 1089, (-352287/19 : ℚ), (-49303/19 : ℚ), [(.edgeBudget, (3986/19 : ℚ)), ((.matchingExcess 2), (280/19 : ℚ)), ((.matchingExcess 3), (87/19 : ℚ)), ((.subsetCount 4), (6/19 : ℚ)), ((.subsetCount 5), (258/19 : ℚ)), ((.missingEdgeUnion 3), (446/19 : ℚ)), ((.pairExtension 6), (244/285 : ℚ)), ((.missingEdgeUnion 7), (6639/190 : ℚ)), ((.pairExtension 7), (1157/570 : ℚ))]⟩,
  ⟨21, 15, 7, 1, 0, 1751, -18310, -2292, [(.edgeBudget, 188), ((.matchingExcess 2), 14), ((.subsetCount 3), (2317/60 : ℚ)), ((.missingEdgeUnion 3), (2017/60 : ℚ)), ((.pairExtension 4), (1/3 : ℚ)), ((.pairExtension 5), (1/10 : ℚ)), ((.pairExtension 6), (1/15 : ℚ))]⟩,
  ⟨21, 15, 8, (19/43 : ℚ), (24/43 : ℚ), (52420/43 : ℚ), (-469470/43 : ℚ), (-57846/43 : ℚ), [(.edgeBudget, (4798/43 : ℚ)), ((.matchingExcess 2), (406/43 : ℚ)), ((.matchingExcess 3), (1/43 : ℚ)), ((.subsetCount 3), (4212/215 : ℚ)), ((.missingEdgeUnion 3), (3987/215 : ℚ)), ((.pairExtension 4), (11/86 : ℚ)), ((.pairExtension 5), (147/86 : ℚ)), ((.pairExtension 6), (213/215 : ℚ))]⟩,
  ⟨21, 16, 7, 1, 0, 3947, -17448, -2124, [(.edgeBudget, 174), ((.matchingExcess 2), 14), ((.pairExtension 3), (5/3 : ℚ)), ((.missingEdgeUnion 4), (1101/25 : ℚ)), ((.pairExtension 4), (1151/150 : ℚ)), ((.pairExtension 5), (1/10 : ℚ))]⟩
]

private theorem addedPart01_ok : addedPart01.all Cert.ok = true := by
  decide +kernel

private def addedPart02 : List Cert := [
  ⟨21, 16, 8, (149/288 : ℚ), (139/288 : ℚ), (249337/144 : ℚ), (-16945/2 : ℚ), (-95083/96 : ℚ), [(.edgeBudget, (3961/48 : ℚ)), ((.matchingExcess 2), (301/48 : ℚ)), ((.subsetCount 2), (31553/576 : ℚ)), ((.pairExtension 3), (323/432 : ℚ)), ((.pairExtension 4), (77/432 : ℚ)), ((.pairExtension 5), (1309/576 : ℚ))]⟩,
  ⟨21, 17, 7, 1, 0, 7494, -10880, -1452, [(.edgeBudget, 132), ((.subsetCount 4), (454/3 : ℚ)), ((.pairExtension 3), (5/3 : ℚ)), ((.missingEdgeUnion 4), (448/3 : ℚ))]⟩,
  ⟨21, 17, 8, 1, 0, 4021, 4862, -132, [((.subsetCount 2), 42), ((.subsetCount 3), 14), ((.subsetCount 4), 5)]⟩,
  ⟨21, 17, 9, (49/1597 : ℚ), (1548/1597 : ℚ), (6108058/1597 : ℚ), (-28670840/1597 : ℚ), (-2868745/1597 : ℚ), [(.edgeBudget, (266156/1597 : ℚ)), ((.matchingExcess 2), (8602/1597 : ℚ)), ((.subsetCount 2), (2136376/4791 : ℚ)), ((.pairExtension 3), (615043/4791 : ℚ)), ((.pairExtension 4), (318032/4791 : ℚ))]⟩
]

private theorem addedPart02_ok : addedPart02.all Cert.ok = true := by
  decide +kernel

private def addedPart03 : List Cert := [
  ⟨21, 18, 7, 1, 0, 13345, -6936, -1452, [(.edgeBudget, 132), ((.missingEdgeUnion 3), (443/2 : ℚ)), ((.pairExtension 3), (151/2 : ℚ))]⟩,
  ⟨21, 18, 8, 1, 0, 11398, 11934, -132, [((.missingEdgeUnion 3), 70), ((.pairExtension 3), 28)]⟩,
  ⟨21, 18, 9, (359/863 : ℚ), (504/863 : ℚ), (4207335/863 : ℚ), (-1277210/863 : ℚ), (-397287/863 : ℚ), [(.edgeBudget, (35772/863 : ℚ)), ((.subsetCount 2), (120274/2589 : ℚ)), ((.pairExtension 3), (2002/2589 : ℚ))]⟩,
  ⟨21, 19, 7, 1, 0, 23158, 23256, -42, [((.subsetCount 2), 14)]⟩
]

private theorem addedPart03_ok : addedPart03.all Cert.ok = true := by
  decide +kernel

private def addedPart04 : List Cert := [
  ⟨21, 19, 8, 1, 0, 24888, 25194, -132, [((.subsetCount 2), 42)]⟩,
  ⟨21, 19, 9, 1, 0, 15806, 16796, -429, [((.subsetCount 2), 132)]⟩,
  ⟨21, 20, 7, 1, 0, 38718, 38760, -42, []⟩,
  ⟨21, 20, 8, 1, 0, 48318, 48450, -132, []⟩
]

private theorem addedPart04_ok : addedPart04.all Cert.ok = true := by
  decide +kernel

private def addedPart05 : List Cert := [
  ⟨21, 20, 9, 1, 0, 41561, 41990, -429, []⟩,
  ⟨21, 20, 10, 0, 1, 16796, 16796, 0, []⟩,
  ⟨22, 11, 7, (1680/3533 : ℚ), (1853/3533 : ℚ), (1681995/3533 : ℚ), (-95102865/3533 : ℚ), (-18863334/3533 : ℚ), [(.edgeBudget, (1730670/3533 : ℚ)), ((.matchingExcess 2), (25942/3533 : ℚ)), ((.matchingExcess 3), 5), ((.matchingExcess 4), 2), ((.matchingExcess 5), (1507/3533 : ℚ)), ((.missingEdgeUnion 3), (43607/3533 : ℚ)), ((.missingEdgeUnion 4), (23397/3533 : ℚ)), ((.missingEdgeUnion 5), (5855/3533 : ℚ)), ((.pairExtension 6), (509/10599 : ℚ)), ((.pairExtension 7), (1293/24731 : ℚ)), ((.pairExtension 8), (1853/98924 : ℚ))]⟩,
  ⟨22, 12, 7, (2623/5020 : ℚ), (2397/5020 : ℚ), (3725529/5020 : ℚ), (-136555881/5020 : ℚ), (-6091896/1255 : ℚ), [(.edgeBudget, (2074569/5020 : ℚ)), ((.matchingExcess 2), 14), ((.matchingExcess 3), 5), ((.matchingExcess 4), (37941/20080 : ℚ)), ((.matchingExcess 5), (1929/10040 : ℚ)), ((.missingEdgeUnion 3), (41879/2510 : ℚ)), ((.missingEdgeUnion 4), (19943/2510 : ℚ)), ((.missingEdgeUnion 5), (791/1255 : ℚ)), ((.pairExtension 6), (4229/37650 : ℚ)), ((.pairExtension 7), (199/3012 : ℚ)), ((.pairExtension 8), (2397/140560 : ℚ))]⟩
]

private theorem addedPart05_ok : addedPart05.all Cert.ok = true := by
  decide +kernel

private def addedPart06 : List Cert := [
  ⟨22, 13, 7, (4/7 : ℚ), (3/7 : ℚ), (102731/91 : ℚ), (-42453/2 : ℚ), (-95979/28 : ℚ), [(.edgeBudget, (99915/364 : ℚ)), ((.matchingExcess 2), 14), ((.matchingExcess 3), 5), ((.matchingExcess 4), (2147/2548 : ℚ)), ((.missingEdgeUnion 3), 21), ((.missingEdgeUnion 4), (5531/1274 : ℚ)), ((.pairExtension 5), (2/35 : ℚ)), ((.pairExtension 6), (6/35 : ℚ)), ((.pairExtension 7), (11/147 : ℚ)), ((.pairExtension 8), (3/196 : ℚ))]⟩,
  ⟨22, 14, 7, (12/19 : ℚ), (7/19 : ℚ), (900083/532 : ℚ), (-8115315/266 : ℚ), (-593301/133 : ℚ), [(.edgeBudget, (633033/1862 : ℚ)), ((.matchingExcess 2), (504/19 : ℚ)), ((.matchingExcess 3), 5), ((.matchingExcess 4), (41799/37240 : ℚ)), ((.missingEdgeUnion 3), (478/19 : ℚ)), ((.missingEdgeUnion 4), (122457/18620 : ℚ)), ((.pairExtension 5), (6/95 : ℚ)), ((.pairExtension 6), (56/285 : ℚ)), ((.pairExtension 7), (10/133 : ℚ)), ((.pairExtension 8), (1/76 : ℚ))]⟩,
  ⟨22, 14, 8, (7/22 : ℚ), (15/22 : ℚ), (10897/11 : ℚ), (-241150/11 : ℚ), (-68557/22 : ℚ), [(.edgeBudget, (2716/11 : ℚ)), ((.matchingExcess 2), (161/11 : ℚ)), ((.matchingExcess 3), (50/11 : ℚ)), ((.matchingExcess 4), (1/22 : ℚ)), ((.subsetCount 5), (147/11 : ℚ)), ((.missingEdgeUnion 3), (256/11 : ℚ)), ((.pairExtension 6), (28/33 : ℚ)), ((.pairExtension 7), (4/11 : ℚ)), ((.missingEdgeUnion 8), (18178/297 : ℚ)), ((.pairExtension 8), (62/27 : ℚ))]⟩,
  ⟨22, 15, 7, 1, 0, 2561, -53590, -7014, [(.edgeBudget, 524), ((.matchingExcess 2), 42), ((.matchingExcess 3), 5), ((.matchingExcess 4), 2), ((.matchingExcess 5), 1), ((.matchingExcess 6), 1), ((.missingEdgeUnion 3), 25), ((.missingEdgeUnion 4), 12), ((.missingEdgeUnion 5), 7), ((.missingEdgeUnion 6), 8), ((.missingEdgeUnion 7), 1)]⟩
]

private theorem addedPart06_ok : addedPart06.all Cert.ok = true := by
  decide +kernel

private def addedPart07 : List Cert := [
  ⟨22, 15, 8, (19/43 : ℚ), (24/43 : ℚ), (60577/43 : ℚ), (-954570/43 : ℚ), (-127146/43 : ℚ), [(.edgeBudget, (9418/43 : ℚ)), ((.matchingExcess 2), (1008/43 : ℚ)), ((.matchingExcess 3), (121/43 : ℚ)), ((.subsetCount 4), (33/43 : ℚ)), ((.missingEdgeUnion 3), (675/43 : ℚ)), ((.missingEdgeUnion 5), (55052/8127 : ℚ)), ((.pairExtension 5), (193967/81270 : ℚ)), ((.pairExtension 6), (213/215 : ℚ)), ((.pairExtension 7), (347/903 : ℚ))]⟩,
  ⟨22, 16, 7, 1, 0, 5238, -55968, -6600, [(.edgeBudget, 495), ((.matchingExcess 2), 42), ((.matchingExcess 3), 5), ((.missingEdgeUnion 3), 30), ((.pairExtension 4), (1/3 : ℚ)), ((.pairExtension 5), (1/10 : ℚ)), ((.missingEdgeUnion 6), (1256/7 : ℚ)), ((.pairExtension 6), (421/35 : ℚ))]⟩,
  ⟨22, 16, 8, (149/288 : ℚ), (139/288 : ℚ), (317009/144 : ℚ), -25405, (-285595/96 : ℚ), [(.edgeBudget, (1789/8 : ℚ)), ((.matchingExcess 2), (973/48 : ℚ)), ((.matchingExcess 3), (253/144 : ℚ)), ((.missingEdgeUnion 3), (181/18 : ℚ)), ((.pairExtension 4), (77/432 : ℚ)), ((.pairExtension 5), (1309/576 : ℚ)), ((.missingEdgeUnion 6), (99335/1008 : ℚ)), ((.pairExtension 6), (3919/504 : ℚ))]⟩,
  ⟨22, 17, 7, 1, 0, 8859, -39032, -4146, [(.edgeBudget, 339), ((.matchingExcess 2), 14), ((.subsetCount 4), (266/3 : ℚ)), ((.subsetCount 5), 1), ((.pairExtension 3), (5/3 : ℚ)), ((.missingEdgeUnion 4), (260/3 : ℚ))]⟩
]

private theorem addedPart07_ok : addedPart07.all Cert.ok = true := by
  decide +kernel

private def addedPart08 : List Cert := [
  ⟨22, 17, 8, 1, 0, 4143, -13090, -1716, [(.edgeBudget, 132), ((.subsetCount 2), (1907/10 : ℚ)), ((.pairExtension 3), (14/3 : ℚ)), ((.pairExtension 4), (5/6 : ℚ)), ((.pairExtension 5), (1/5 : ℚ))]⟩,
  ⟨22, 17, 9, (215/718 : ℚ), (503/718 : ℚ), (2774569/718 : ℚ), (-7830115/359 : ℚ), (-791851/359 : ℚ), [(.edgeBudget, (133131/718 : ℚ)), ((.matchingExcess 2), (2020/359 : ℚ)), ((.subsetCount 2), (1616321/7180 : ℚ)), ((.pairExtension 3), (286/1077 : ℚ)), ((.pairExtension 4), (92807/4308 : ℚ)), ((.pairExtension 5), (45133/3590 : ℚ))]⟩,
  ⟨22, 18, 7, 1, 0, 14573, -32181, -3432, [(.edgeBudget, 297), ((.subsetCount 3), (321/2 : ℚ)), ((.subsetCount 4), 2), ((.missingEdgeUnion 3), (311/2 : ℚ))]⟩,
  ⟨22, 18, 8, 1, 0, 11489, -8262, -1716, [(.edgeBudget, 132), ((.subsetCount 3), 101), ((.subsetCount 4), 5), ((.missingEdgeUnion 3), 87)]⟩
]

private theorem addedPart08_ok : addedPart08.all Cert.ok = true := by
  decide +kernel

private def addedPart09 : List Cert := [
  ⟨22, 18, 9, (359/863 : ℚ), (504/863 : ℚ), (4455649/863 : ℚ), (-11455994/863 : ℚ), (-1195623/863 : ℚ), [(.edgeBudget, (102300/863 : ℚ)), ((.subsetCount 3), (2002/863 : ℚ)), ((.missingEdgeUnion 4), (780857/4315 : ℚ)), ((.pairExtension 4), (251097/4315 : ℚ))]⟩,
  ⟨22, 19, 7, 1, 0, 23605, 684, -1452, [(.edgeBudget, 132), ((.subsetCount 3), 151), ((.missingEdgeUnion 3), 146)]⟩,
  ⟨22, 19, 8, 1, 0, 24658, 25194, -132, [((.subsetCount 3), 56), ((.missingEdgeUnion 3), 42)]⟩,
  ⟨22, 19, 9, 1, 0, 15071, 16796, -429, [((.subsetCount 2), 132), ((.subsetCount 3), 42)]⟩
]

private theorem addedPart09_ok : addedPart09.all Cert.ok = true := by
  decide +kernel

private def addedPart10 : List Cert := [
  ⟨22, 20, 7, 1, 0, 38662, 38760, -42, [((.subsetCount 2), 14)]⟩,
  ⟨22, 20, 8, 1, 0, 48144, 48450, -132, [((.subsetCount 2), 42)]⟩,
  ⟨22, 20, 9, 1, 0, 41000, 41990, -429, [((.subsetCount 2), 132)]⟩,
  ⟨22, 20, 10, (4870/16831 : ℚ), (11961/16831 : ℚ), (282532072/16831 : ℚ), 16796, (-62801/16831 : ℚ), [((.subsetCount 2), (35802/16831 : ℚ))]⟩
]

private theorem addedPart10_ok : addedPart10.all Cert.ok = true := by
  decide +kernel

private def addedPart11 : List Cert := [
  ⟨22, 21, 7, 1, 0, 61974, 62016, -42, []⟩,
  ⟨22, 21, 8, 1, 0, 87078, 87210, -132, []⟩,
  ⟨22, 21, 9, 1, 0, 90011, 90440, -429, []⟩,
  ⟨22, 21, 10, 1, 0, 57356, 58786, -1430, []⟩
]

private theorem addedPart11_ok : addedPart11.all Cert.ok = true := by
  decide +kernel

private def addedPart12 : List Cert := [
  ⟨23, 12, 7, (3/5 : ℚ), (2/5 : ℚ), (266041/225 : ℚ), (-916102/25 : ℚ), (-164374/25 : ℚ), [(.edgeBudget, (41686/75 : ℚ)), ((.matchingExcess 2), 14), ((.matchingExcess 3), 5), ((.matchingExcess 4), 2), ((.matchingExcess 5), (1493/4725 : ℚ)), ((.missingEdgeUnion 3), (78/5 : ℚ)), ((.missingEdgeUnion 4), 8), ((.missingEdgeUnion 5), (2041/1575 : ℚ)), ((.pairExtension 6), (1/25 : ℚ)), ((.pairExtension 7), (1/21 : ℚ)), ((.pairExtension 8), (1/70 : ℚ))]⟩,
  ⟨23, 13, 7, (3011/5119 : ℚ), (2108/5119 : ℚ), (9011274/5119 : ℚ), (-234843180/5119 : ℚ), (-38583000/5119 : ℚ), [(.edgeBudget, (3022404/5119 : ℚ)), ((.matchingExcess 2), (126462/5119 : ℚ)), ((.matchingExcess 3), (42154/5119 : ℚ)), ((.matchingExcess 4), 2), ((.matchingExcess 5), (601/5119 : ℚ)), ((.missingEdgeUnion 3), (155974/5119 : ℚ)), ((.missingEdgeUnion 4), (51492/5119 : ℚ)), ((.missingEdgeUnion 5), (1196/5119 : ℚ)), ((.pairExtension 6), (11446/76785 : ℚ)), ((.pairExtension 7), (7529/107499 : ℚ)), ((.pairExtension 8), (527/35833 : ℚ))]⟩,
  ⟨23, 13, 8, (14/43 : ℚ), (29/43 : ℚ), (507679/645 : ℚ), (-27411358/645 : ℚ), (-13470899/1935 : ℚ), [(.edgeBudget, (1060388/1935 : ℚ)), ((.matchingExcess 2), (616/43 : ℚ)), ((.matchingExcess 3), (406/43 : ℚ)), ((.matchingExcess 4), (118039/54180 : ℚ)), ((.missingEdgeUnion 3), (1428/43 : ℚ)), ((.missingEdgeUnion 4), (132529/13545 : ℚ)), ((.pairExtension 5), (7/215 : ℚ)), ((.pairExtension 6), (14/43 : ℚ)), ((.pairExtension 7), (191/903 : ℚ)), ((.pairExtension 8), (51/602 : ℚ)), ((.pairExtension 9), (29/1548 : ℚ))]⟩,
  ⟨23, 14, 7, (5/7 : ℚ), (2/7 : ℚ), (2931065/1092 : ℚ), (-611167/12 : ℚ), (-4139173/546 : ℚ), [(.edgeBudget, (88045/156 : ℚ)), ((.matchingExcess 2), 30), ((.matchingExcess 3), 10), ((.matchingExcess 4), (20521/15288 : ℚ)), ((.matchingExcess 5), (5/56 : ℚ)), ((.missingEdgeUnion 3), 44), ((.missingEdgeUnion 4), (19065/2548 : ℚ)), ((.pairExtension 6), (1/21 : ℚ)), ((.pairExtension 7), (1/21 : ℚ)), ((.pairExtension 8), (1/98 : ℚ))]⟩
]

private theorem addedPart12_ok : addedPart12.all Cert.ok = true := by
  decide +kernel

private def addedPart13 : List Cert := [
  ⟨23, 14, 8, (6/13 : ℚ), (7/13 : ℚ), (129976/117 : ℚ), (-363017/9 : ℚ), (-703957/117 : ℚ), [(.edgeBudget, (52298/117 : ℚ)), ((.matchingExcess 2), (294/13 : ℚ)), ((.matchingExcess 3), (98/13 : ℚ)), ((.matchingExcess 4), (6938/4095 : ℚ)), ((.missingEdgeUnion 3), (406/13 : ℚ)), ((.missingEdgeUnion 4), (524/63 : ℚ)), ((.pairExtension 5), (3/65 : ℚ)), ((.pairExtension 6), (76/195 : ℚ)), ((.pairExtension 7), (62/273 : ℚ)), ((.pairExtension 8), (29/364 : ℚ)), ((.pairExtension 9), (7/468 : ℚ))]⟩,
  ⟨23, 15, 7, 1, 0, (1907851/435 : ℚ), (-2407900/29 : ℚ), (-320243/29 : ℚ), [(.edgeBudget, (69982/87 : ℚ)), ((.matchingExcess 2), 42), ((.matchingExcess 3), 14), ((.matchingExcess 4), 2), ((.matchingExcess 5), (137/435 : ℚ)), ((.matchingExcess 6), (1/9 : ℚ)), ((.missingEdgeUnion 3), 70), ((.missingEdgeUnion 4), 12), ((.missingEdgeUnion 5), (661/435 : ℚ)), ((.missingEdgeUnion 7), 1)]⟩,
  ⟨23, 15, 8, (13/24 : ℚ), (11/24 : ℚ), (314635/192 : ℚ), (-1852765/48 : ℚ), (-82355/16 : ℚ), [(.edgeBudget, (17945/48 : ℚ)), ((.matchingExcess 2), (77/4 : ℚ)), ((.matchingExcess 3), (77/12 : ℚ)), ((.matchingExcess 4), (289/192 : ℚ)), ((.missingEdgeUnion 3), (371/12 : ℚ)), ((.missingEdgeUnion 4), (261/32 : ℚ)), ((.pairExtension 5), (1/16 : ℚ)), ((.pairExtension 6), (59/120 : ℚ)), ((.pairExtension 7), (43/168 : ℚ)), ((.pairExtension 8), (53/672 : ℚ))]⟩,
  ⟨23, 16, 7, 1, 0, (2263288/315 : ℚ), (-2195296/21 : ℚ), (-4118936/315 : ℚ), [(.edgeBudget, (283421/315 : ℚ)), ((.matchingExcess 2), 90), ((.matchingExcess 3), 14), ((.matchingExcess 4), (7619/6300 : ℚ)), ((.matchingExcess 5), (1/9 : ℚ)), ((.matchingExcess 6), (1/10 : ℚ)), ((.missingEdgeUnion 3), 84), ((.missingEdgeUnion 4), (12088/1575 : ℚ)), ((.missingEdgeUnion 7), 1)]⟩
]

private theorem addedPart13_ok : addedPart13.all Cert.ok = true := by
  decide +kernel

private def addedPart14 : List Cert := [
  ⟨23, 16, 8, (23/44 : ℚ), (21/44 : ℚ), (116601/44 : ℚ), (-384110/11 : ℚ), (-186815/44 : ℚ), [(.edgeBudget, (3332/11 : ℚ)), ((.matchingExcess 2), (441/22 : ℚ)), ((.matchingExcess 3), (147/22 : ℚ)), ((.matchingExcess 4), (17/44 : ℚ)), ((.subsetCount 5), (251/21 : ℚ)), ((.missingEdgeUnion 3), (434/11 : ℚ)), ((.missingEdgeUnion 4), 2), ((.pairExtension 5), (781/840 : ℚ)), ((.pairExtension 6), (7/6 : ℚ)), ((.pairExtension 7), (383/924 : ℚ))]⟩,
  ⟨23, 16, 9, (19/62 : ℚ), (43/62 : ℚ), (188651/62 : ℚ), (-1136977/31 : ℚ), (-136007/31 : ℚ), [(.edgeBudget, (19953/62 : ℚ)), ((.matchingExcess 2), (633/31 : ℚ)), ((.matchingExcess 3), (168/31 : ℚ)), ((.subsetCount 5), (2541/62 : ℚ)), ((.missingEdgeUnion 3), (1004/31 : ℚ)), ((.pairExtension 4), (11/124 : ℚ)), ((.pairExtension 6), (163/62 : ℚ)), ((.missingEdgeUnion 7), (17967/248 : ℚ)), ((.pairExtension 7), (1151/248 : ℚ))]⟩,
  ⟨23, 17, 7, 1, 0, 11393, -98736, -10509, [(.edgeBudget, 778), ((.matchingExcess 2), 42), ((.matchingExcess 3), 5), ((.matchingExcess 4), 2), ((.matchingExcess 6), (1/11 : ℚ)), ((.subsetCount 2), (1452/5 : ℚ)), ((.missingEdgeUnion 3), 35), ((.missingEdgeUnion 4), 16), ((.pairExtension 5), (1/10 : ℚ))]⟩,
  ⟨23, 17, 8, 1, 0, 4722, -53482, -5577, [(.edgeBudget, 429), ((.subsetCount 4), (3904/45 : ℚ)), ((.pairExtension 3), (14/3 : ℚ)), ((.missingEdgeUnion 4), (3679/45 : ℚ)), ((.pairExtension 5), (1/5 : ℚ)), ((.pairExtension 6), (1/15 : ℚ))]⟩
]

private theorem addedPart14_ok : addedPart14.all Cert.ok = true := by
  decide +kernel

private def addedPart15 : List Cert := [
  ⟨23, 17, 9, (215/503 : ℚ), (288/503 : ℚ), (1899560/503 : ℚ), (-18010752/503 : ℚ), (-1859667/503 : ℚ), [(.edgeBudget, (142728/503 : ℚ)), ((.matchingExcess 2), (4794/503 : ℚ)), ((.subsetCount 4), (1003538/22635 : ℚ)), ((.pairExtension 3), (1282/1509 : ℚ)), ((.missingEdgeUnion 4), (977798/22635 : ℚ)), ((.pairExtension 5), (26411/5030 : ℚ)), ((.pairExtension 6), (4774/1509 : ℚ))]⟩,
  ⟨23, 18, 7, 1, 0, 17312, -93534, -9275, [(.edgeBudget, 698), ((.matchingExcess 2), 42), ((.subsetCount 2), (4091/10 : ℚ)), ((.subsetCount 4), 2), ((.pairExtension 3), (5/3 : ℚ)), ((.pairExtension 5), (1/10 : ℚ))]⟩,
  ⟨23, 18, 8, 1, 0, 12634, -53703, -5577, [(.edgeBudget, 429), ((.subsetCount 2), (2426/5 : ℚ)), ((.subsetCount 4), 5), ((.pairExtension 3), (14/3 : ℚ)), ((.pairExtension 5), (1/5 : ℚ))]⟩,
  ⟨23, 18, 9, (503/1008 : ℚ), (505/1008 : ℚ), (5706587/1008 : ℚ), (-3297235/112 : ℚ), (-103981/36 : ℚ), [(.edgeBudget, (75329/336 : ℚ)), ((.matchingExcess 2), (173/56 : ℚ)), ((.missingEdgeUnion 3), (2270183/20160 : ℚ)), ((.pairExtension 3), (2350423/60480 : ℚ)), ((.pairExtension 4), (143/432 : ℚ)), ((.pairExtension 5), (10439/1440 : ℚ))]⟩
]

private theorem addedPart15_ok : addedPart15.all Cert.ok = true := by
  decide +kernel

private def addedPart16 : List Cert := [
  ⟨23, 19, 7, 1, 0, 26052, -79344, -7539, [(.edgeBudget, 600), ((.matchingExcess 2), 14), ((.subsetCount 2), (1465/3 : ℚ)), ((.subsetCount 3), 5), ((.pairExtension 4), (1/3 : ℚ))]⟩,
  ⟨23, 19, 8, 1, 0, 25739, -48165, -5577, [(.edgeBudget, 429), ((.subsetCount 2), (2831/6 : ℚ)), ((.subsetCount 3), 14), ((.pairExtension 4), (5/6 : ℚ))]⟩,
  ⟨23, 19, 9, 1, 0, 14106, 16796, -429, [((.subsetCount 2), (487/3 : ℚ)), ((.pairExtension 3), 14), ((.pairExtension 4), (7/3 : ℚ))]⟩,
  ⟨23, 19, 10, (64/5113 : ℚ), (5049/5113 : ℚ), (64077965/5113 : ℚ), (-416004354/5113 : ℚ), (-36352417/5113 : ℚ), [(.edgeBudget, (2928698/5113 : ℚ)), ((.matchingExcess 2), (34063/5113 : ℚ)), ((.subsetCount 2), (25399405/15339 : ℚ)), ((.pairExtension 3), (2333474/5113 : ℚ)), ((.pairExtension 4), (3545971/15339 : ℚ))]⟩
]

private theorem addedPart16_ok : addedPart16.all Cert.ok = true := by
  decide +kernel

private def addedPart17 : List Cert := [
  ⟨23, 20, 7, 1, 0, 39703, -17670, -3432, [(.edgeBudget, 297), ((.subsetCount 3), 316), ((.missingEdgeUnion 3), 311)]⟩,
  ⟨23, 20, 8, 1, 0, 48178, 23370, -1716, [(.edgeBudget, 132), ((.subsetCount 3), 188), ((.missingEdgeUnion 3), 174)]⟩,
  ⟨23, 20, 9, 1, 0, 40265, 41990, -429, [((.subsetCount 3), 174), ((.missingEdgeUnion 3), 132)]⟩,
  ⟨23, 20, 10, (541/1329 : ℚ), (788/1329 : ℚ), (22307372/1329 : ℚ), (11677514/1329 : ℚ), (-233233/443 : ℚ), [(.edgeBudget, (56023/1329 : ℚ)), ((.subsetCount 2), (23006/443 : ℚ)), ((.subsetCount 3), (1768/443 : ℚ))]⟩
]

private theorem addedPart17_ok : addedPart17.all Cert.ok = true := by
  decide +kernel

private def addedPart18 : List Cert := [
  ⟨23, 21, 7, 1, 0, 61918, 62016, -42, [((.subsetCount 2), 14)]⟩,
  ⟨23, 21, 8, 1, 0, 86904, 87210, -132, [((.subsetCount 2), 42)]⟩,
  ⟨23, 21, 9, 1, 0, 89450, 90440, -429, [((.subsetCount 2), 132)]⟩,
  ⟨23, 21, 10, 1, 0, 55497, 58786, -1430, [((.subsetCount 2), 429)]⟩
]

private theorem addedPart18_ok : addedPart18.all Cert.ok = true := by
  decide +kernel

private def addedPart19 : List Cert := [
  ⟨23, 22, 7, 1, 0, 95889, 95931, -42, []⟩,
  ⟨23, 22, 8, 1, 0, 149094, 149226, -132, []⟩,
  ⟨23, 22, 9, 1, 0, 177221, 177650, -429, []⟩,
  ⟨23, 22, 10, 1, 0, 147796, 149226, -1430, []⟩
]

private theorem addedPart19_ok : addedPart19.all Cert.ok = true := by
  decide +kernel

private def addedPart20 : List Cert := [
  ⟨23, 22, 11, 0, 1, 58786, 58786, 0, []⟩,
  ⟨24, 12, 7, (9/14 : ℚ), (5/14 : ℚ), (855437/364 : ℚ), (-6884658/91 : ℚ), (-1243995/91 : ℚ), [(.edgeBudget, (417369/364 : ℚ)), ((.matchingExcess 2), 14), ((.matchingExcess 3), 9), ((.matchingExcess 4), (45/14 : ℚ)), ((.matchingExcess 5), (7639/10920 : ℚ)), ((.matchingExcess 6), (3/28 : ℚ)), ((.missingEdgeUnion 3), 23), ((.missingEdgeUnion 4), (80/7 : ℚ)), ((.missingEdgeUnion 5), (7015/2184 : ℚ)), ((.pairExtension 7), (11/294 : ℚ)), ((.pairExtension 8), (5/392 : ℚ))]⟩,
  ⟨24, 13, 7, (7/10 : ℚ), (3/10 : ℚ), (49757/15 : ℚ), (-823719/10 : ℚ), (-135257/10 : ℚ), [(.edgeBudget, (10577/10 : ℚ)), ((.matchingExcess 2), (147/5 : ℚ)), ((.matchingExcess 3), (49/5 : ℚ)), ((.matchingExcess 4), (7/2 : ℚ)), ((.matchingExcess 5), (59/180 : ℚ)), ((.matchingExcess 6), (1/10 : ℚ)), ((.missingEdgeUnion 3), (168/5 : ℚ)), ((.missingEdgeUnion 4), (31/2 : ℚ)), ((.missingEdgeUnion 5), (47/30 : ℚ)), ((.pairExtension 7), (4/105 : ℚ)), ((.pairExtension 8), (3/280 : ℚ))]⟩,
  ⟨24, 13, 8, (4583/11576 : ℚ), (6993/11576 : ℚ), (2560293/5788 : ℚ), (-844215879/11576 : ℚ), (-138646587/11576 : ℚ), [(.edgeBudget, (2712339/2894 : ℚ)), ((.matchingExcess 2), (146853/5788 : ℚ)), ((.matchingExcess 3), (48951/5788 : ℚ)), ((.matchingExcess 4), (34965/11576 : ℚ)), ((.matchingExcess 5), (6519/11576 : ℚ)), ((.missingEdgeUnion 3), (163723/5788 : ℚ)), ((.missingEdgeUnion 4), (144917/11576 : ℚ)), ((.missingEdgeUnion 5), (15211/5788 : ℚ)), ((.pairExtension 6), (1687/8682 : ℚ)), ((.pairExtension 7), (20011/121548 : ℚ)), ((.pairExtension 8), (23389/324128 : ℚ)), ((.pairExtension 9), (777/46304 : ℚ))]⟩
]

private theorem addedPart20_ok : addedPart20.all Cert.ok = true := by
  decide +kernel

private def addedPart21 : List Cert := [
  ⟨24, 14, 7, (20/27 : ℚ), (7/27 : ℚ), (119393/27 : ℚ), (-5707078/81 : ℚ), (-94874/9 : ℚ), [(.edgeBudget, (63097/81 : ℚ)), ((.matchingExcess 2), (280/9 : ℚ)), ((.matchingExcess 3), (280/27 : ℚ)), ((.matchingExcess 4), 2), ((.matchingExcess 5), (5/54 : ℚ)), ((.matchingExcess 6), (5/54 : ℚ)), ((.missingEdgeUnion 3), (406/9 : ℚ)), ((.missingEdgeUnion 4), (305/27 : ℚ)), ((.pairExtension 7), (22/567 : ℚ)), ((.pairExtension 8), (1/108 : ℚ))]⟩,
  ⟨24, 14, 8, (7/15 : ℚ), (8/15 : ℚ), (329969/270 : ℚ), (-21614957/405 : ℚ), (-649988/81 : ℚ), [(.edgeBudget, (239012/405 : ℚ)), ((.matchingExcess 2), (112/5 : ℚ)), ((.matchingExcess 3), (112/15 : ℚ)), ((.matchingExcess 4), (25681/11340 : ℚ)), ((.matchingExcess 5), (1/15 : ℚ)), ((.missingEdgeUnion 3), (154/5 : ℚ)), ((.missingEdgeUnion 4), (126137/11340 : ℚ)), ((.pairExtension 6), (28/75 : ℚ)), ((.pairExtension 7), (2/9 : ℚ)), ((.pairExtension 8), (11/140 : ℚ)), ((.pairExtension 9), (2/135 : ℚ))]⟩,
  ⟨24, 15, 7, 1, 0, (287396/39 : ℚ), (-7478815/52 : ℚ), (-1025829/52 : ℚ), [(.edgeBudget, (71935/52 : ℚ)), ((.matchingExcess 2), 90), ((.matchingExcess 3), 14), ((.matchingExcess 4), (9713/2184 : ℚ)), ((.matchingExcess 5), (1/8 : ℚ)), ((.matchingExcess 6), (1/9 : ℚ)), ((.missingEdgeUnion 3), 70), ((.missingEdgeUnion 4), (9713/364 : ℚ)), ((.missingEdgeUnion 7), 1)]⟩,
  ⟨24, 15, 8, (13/24 : ℚ), (11/24 : ℚ), (5066371/2160 : ℚ), (-19723055/288 : ℚ), (-2711885/288 : ℚ), [(.edgeBudget, (568909/864 : ℚ)), ((.matchingExcess 2), 42), ((.matchingExcess 3), (77/12 : ℚ)), ((.matchingExcess 4), (84421/30240 : ℚ)), ((.missingEdgeUnion 3), (371/12 : ℚ)), ((.missingEdgeUnion 4), (92989/6048 : ℚ)), ((.pairExtension 5), (1/16 : ℚ)), ((.pairExtension 6), (59/120 : ℚ)), ((.pairExtension 7), (43/168 : ℚ)), ((.pairExtension 8), (53/672 : ℚ)), ((.pairExtension 9), (11/864 : ℚ))]⟩
]

private theorem addedPart21_ok : addedPart21.all Cert.ok = true := by
  decide +kernel

private def addedPart22 : List Cert := [
  ⟨24, 16, 7, 1, 0, (8443868/765 : ℚ), (-2841048/17 : ℚ), (-1750603/85 : ℚ), [(.edgeBudget, (120808/85 : ℚ)), ((.matchingExcess 2), 90), ((.matchingExcess 3), 14), ((.matchingExcess 4), (6184/1275 : ℚ)), ((.matchingExcess 5), (1/9 : ℚ)), ((.matchingExcess 6), (1/10 : ℚ)), ((.missingEdgeUnion 3), 84), ((.missingEdgeUnion 4), (43288/1275 : ℚ)), ((.missingEdgeUnion 7), 1)]⟩,
  ⟨24, 16, 8, (83/139 : ℚ), (56/139 : ℚ), (10850499/2780 : ℚ), (-82912120/973 : ℚ), (-10324553/973 : ℚ), [(.edgeBudget, (2810117/3892 : ℚ)), ((.matchingExcess 2), 42), ((.matchingExcess 3), (225179/19460 : ℚ)), ((.matchingExcess 4), (280/139 : ℚ)), ((.missingEdgeUnion 3), (236547/3892 : ℚ)), ((.missingEdgeUnion 4), (1769/139 : ℚ)), ((.pairExtension 5), (11/139 : ℚ)), ((.pairExtension 6), (259/417 : ℚ)), ((.pairExtension 7), (848/2919 : ℚ)), ((.pairExtension 8), (309/3892 : ℚ))]⟩,
  ⟨24, 16, 9, (23/71 : ℚ), (48/71 : ℚ), (180887/71 : ℚ), (-6778474/71 : ℚ), (-842011/71 : ℚ), [(.edgeBudget, (57586/71 : ℚ)), ((.matchingExcess 2), (3354/71 : ℚ)), ((.matchingExcess 3), (1022/71 : ℚ)), ((.matchingExcess 4), (77/71 : ℚ)), ((.subsetCount 5), (2541/71 : ℚ)), ((.missingEdgeUnion 3), (5426/71 : ℚ)), ((.missingEdgeUnion 4), (495/71 : ℚ)), ((.missingEdgeUnion 6), (161375/27832 : ℚ)), ((.pairExtension 6), (235723/83496 : ℚ)), ((.pairExtension 7), (561/497 : ℚ)), ((.pairExtension 8), (799/1988 : ℚ))]⟩,
  ⟨24, 17, 7, 1, 0, (3278479/209 : ℚ), (-32195144/209 : ℚ), (-3641296/209 : ℚ), [(.edgeBudget, (247597/209 : ℚ)), ((.matchingExcess 2), 90), ((.matchingExcess 3), 14), ((.matchingExcess 4), 2), ((.matchingExcess 5), (108/209 : ℚ)), ((.matchingExcess 6), (1/11 : ℚ)), ((.missingEdgeUnion 3), 98), ((.missingEdgeUnion 4), 16), ((.missingEdgeUnion 5), (871/209 : ℚ)), ((.missingEdgeUnion 7), 1)]⟩
]

private theorem addedPart22_ok : addedPart22.all Cert.ok = true := by
  decide +kernel

private def addedPart23 : List Cert := [
  ⟨24, 17, 8, (22/31 : ℚ), (9/31 : ℚ), (193823/31 : ℚ), (-2306764/31 : ℚ), (-260103/31 : ℚ), [(.edgeBudget, (17748/31 : ℚ)), ((.matchingExcess 2), 42), ((.matchingExcess 3), (126/31 : ℚ)), ((.matchingExcess 4), (45/31 : ℚ)), ((.matchingExcess 5), (18/31 : ℚ)), ((.missingEdgeUnion 3), (700/31 : ℚ)), ((.missingEdgeUnion 4), (286/31 : ℚ)), ((.missingEdgeUnion 5), (127/31 : ℚ)), ((.pairExtension 6), (22/465 : ℚ)), ((.missingEdgeUnion 7), (78433/620 : ℚ)), ((.pairExtension 7), (11539/1860 : ℚ))]⟩,
  ⟨24, 17, 9, (215/503 : ℚ), (288/503 : ℚ), (2061207/503 : ℚ), (-28277936/503 : ℚ), (-3143065/503 : ℚ), [(.edgeBudget, (218222/503 : ℚ)), ((.matchingExcess 2), (16890/503 : ℚ)), ((.matchingExcess 3), (1022/503 : ℚ)), ((.missingEdgeUnion 3), (5872/503 : ℚ)), ((.pairExtension 4), (286/1509 : ℚ)), ((.pairExtension 5), (26411/5030 : ℚ)), ((.pairExtension 6), (4774/1509 : ℚ)), ((.missingEdgeUnion 7), (1450609/5030 : ℚ)), ((.pairExtension 7), (75779/5030 : ℚ))]⟩,
  ⟨24, 18, 7, 1, 0, 21921, -209202, -21167, [(.edgeBudget, 1454), ((.matchingExcess 2), 90), ((.matchingExcess 3), 14), ((.matchingExcess 4), 2), ((.matchingExcess 5), 1), ((.missingEdgeUnion 3), (8621/40 : ℚ)), ((.pairExtension 3), (4141/120 : ℚ)), ((.missingEdgeUnion 4), 18), ((.missingEdgeUnion 5), 10), ((.pairExtension 6), (1/15 : ℚ))]⟩,
  ⟨24, 18, 8, 1, 0, 14931, -166923, -16609, [(.edgeBudget, 1169), ((.matchingExcess 2), 42), ((.pairExtension 3), (14/3 : ℚ)), ((.pairExtension 4), (5/6 : ℚ)), ((.missingEdgeUnion 5), (14753/54 : ℚ)), ((.pairExtension 5), (14861/540 : ℚ)), ((.pairExtension 6), (1/15 : ℚ))]⟩
]

private theorem addedPart23_ok : addedPart23.all Cert.ok = true := by
  decide +kernel

private def addedPart24 : List Cert := [
  ⟨24, 18, 9, (503/1008 : ℚ), (505/1008 : ℚ), (3297055/504 : ℚ), (-1057961/14 : ℚ), (-3759341/504 : ℚ), [(.edgeBudget, (22079/42 : ℚ)), ((.matchingExcess 2), (2027/84 : ℚ)), ((.matchingExcess 3), (1/36 : ℚ)), ((.pairExtension 3), (947/756 : ℚ)), ((.pairExtension 4), (143/432 : ℚ)), ((.missingEdgeUnion 5), (3237923/27216 : ℚ)), ((.pairExtension 5), (2605447/136080 : ℚ)), ((.pairExtension 6), (20471/5040 : ℚ))]⟩,
  ⟨24, 19, 7, 1, 0, 30822, -196650, -18428, [(.edgeBudget, 1286), ((.matchingExcess 2), 90), ((.matchingExcess 3), 5), ((.subsetCount 4), (1617/10 : ℚ)), ((.missingEdgeUnion 3), 45), ((.missingEdgeUnion 4), (1597/10 : ℚ)), ((.pairExtension 5), (1/10 : ℚ))]⟩,
  ⟨24, 19, 8, 1, 0, 28838, -167523, -15979, [(.edgeBudget, 1127), ((.matchingExcess 2), 42), ((.subsetCount 3), 14), ((.subsetCount 4), (4451/15 : ℚ)), ((.missingEdgeUnion 4), (4376/15 : ℚ)), ((.pairExtension 5), (1/5 : ℚ))]⟩,
  ⟨24, 19, 9, 1, 0, 13694, -56563, -6435, [(.edgeBudget, 429), ((.pairExtension 3), 14), ((.missingEdgeUnion 4), (1221/5 : ℚ)), ((.pairExtension 4), (1291/30 : ℚ)), ((.pairExtension 5), (1/2 : ℚ))]⟩
]

private theorem addedPart24_ok : addedPart24.all Cert.ok = true := by
  decide +kernel

private def addedPart25 : List Cert := [
  ⟨24, 19, 10, (159/541 : ℚ), (382/541 : ℚ), (6835006/541 : ℚ), (-54663589/541 : ℚ), (-4992551/541 : ℚ), [(.edgeBudget, (357191/541 : ℚ)), ((.matchingExcess 2), (14340/541 : ℚ)), ((.pairExtension 3), (572/1623 : ℚ)), ((.missingEdgeUnion 4), (3922313/13525 : ℚ)), ((.pairExtension 4), (9620863/81150 : ℚ)), ((.pairExtension 5), (223223/5410 : ℚ))]⟩,
  ⟨24, 20, 7, 1, 0, 43743, -156750, -13573, [(.edgeBudget, 1029), ((.matchingExcess 2), 14), ((.subsetCount 3), (1370/3 : ℚ)), ((.missingEdgeUnion 3), (1355/3 : ℚ)), ((.pairExtension 4), (1/3 : ℚ))]⟩,
  ⟨24, 20, 8, 1, 0, 50854, -141740, -13585, [(.edgeBudget, 1001), ((.subsetCount 3), (6431/12 : ℚ)), ((.missingEdgeUnion 3), (6263/12 : ℚ)), ((.pairExtension 4), (5/6 : ℚ))]⟩,
  ⟨24, 20, 9, 1, 0, 39729, -39520, -6435, [(.edgeBudget, 429), ((.subsetCount 3), (971/3 : ℚ)), ((.missingEdgeUnion 3), (845/3 : ℚ)), ((.pairExtension 4), (7/3 : ℚ))]⟩
]

private theorem addedPart25_ok : addedPart25.all Cert.ok = true := by
  decide +kernel

private def addedPart26 : List Cert := [
  ⟨24, 20, 10, (541/1329 : ℚ), (788/1329 : ℚ), (23033209/1329 : ℚ), (-83450926/1329 : ℚ), (-2515513/443 : ℚ), [(.edgeBudget, (556699/1329 : ℚ)), ((.subsetCount 3), (1054247/3987 : ℚ)), ((.missingEdgeUnion 3), (1038335/3987 : ℚ)), ((.pairExtension 4), (367588/3987 : ℚ))]⟩,
  ⟨24, 21, 7, 1, 0, 63828, -58104, -7007, [(.edgeBudget, 572), ((.subsetCount 3), 591), ((.missingEdgeUnion 3), 586)]⟩,
  ⟨24, 21, 8, 1, 0, 87499, -2880, -5577, [(.edgeBudget, 429), ((.subsetCount 3), 485), ((.missingEdgeUnion 3), 471)]⟩,
  ⟨24, 21, 9, 1, 0, 88715, 90440, -429, [((.subsetCount 3), 174), ((.missingEdgeUnion 3), 132)]⟩
]

private theorem addedPart26_ok : addedPart26.all Cert.ok = true := by
  decide +kernel

private def addedPart27 : List Cert := [
  ⟨24, 21, 10, 1, 0, 53077, 58786, -1430, [((.subsetCount 2), 473), ((.pairExtension 3), 44)]⟩,
  ⟨24, 22, 7, 1, 0, 95875, 86229, -462, [(.edgeBudget, 42), ((.subsetCount 2), 56)]⟩,
  ⟨24, 22, 8, 1, 0, 148920, 149226, -132, [((.subsetCount 2), 42)]⟩,
  ⟨24, 22, 9, 1, 0, 176660, 177650, -429, [((.subsetCount 2), 132)]⟩
]

private theorem addedPart27_ok : addedPart27.all Cert.ok = true := by
  decide +kernel

private def addedPart28 : List Cert := [
  ⟨24, 22, 10, 1, 0, 145937, 149226, -1430, [((.subsetCount 2), 429)]⟩,
  ⟨24, 22, 11, (3361/11766 : ℚ), (8405/11766 : ℚ), (345753209/5883 : ℚ), 58786, (-10639/1961 : ℚ), [((.subsetCount 2), (20995/5883 : ℚ))]⟩,
  ⟨24, 23, 7, 1, 0, 144168, 144210, -42, []⟩,
  ⟨24, 23, 8, 1, 0, 245025, 245157, -132, []⟩
]

private theorem addedPart28_ok : addedPart28.all Cert.ok = true := by
  decide +kernel

private def addedPart29 : List Cert := [
  ⟨24, 23, 9, 1, 0, 326447, 326876, -429, []⟩,
  ⟨24, 23, 10, 1, 0, 325446, 326876, -1430, []⟩,
  ⟨24, 23, 11, 1, 0, 203150, 208012, -4862, []⟩
]

private theorem addedPart29_ok : addedPart29.all Cert.ok = true := by
  decide +kernel

/-- The 119 additional certificates at orders 21--24 of Part I's certificate appendix. -/
def addedCerts : List Cert := addedPart00 ++ addedPart01 ++ addedPart02 ++ addedPart03 ++ addedPart04 ++ addedPart05 ++ addedPart06 ++ addedPart07 ++ addedPart08 ++ addedPart09 ++ addedPart10 ++ addedPart11 ++ addedPart12 ++ addedPart13 ++ addedPart14 ++ addedPart15 ++ addedPart16 ++ addedPart17 ++ addedPart18 ++ addedPart19 ++ addedPart20 ++ addedPart21 ++ addedPart22 ++ addedPart23 ++ addedPart24 ++ addedPart25 ++ addedPart26 ++ addedPart27 ++ addedPart28 ++ addedPart29

private theorem addedCerts_ok : ∀ c ∈ addedCerts, c.ok = true := by
  intro c hc
  simp only [addedCerts, List.mem_append, or_assoc] at hc
  rcases hc with h00 | h01 | h02 | h03 | h04 | h05 | h06 | h07 | h08 | h09 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29
  · exact (List.all_eq_true.mp addedPart00_ok) c h00
  · exact (List.all_eq_true.mp addedPart01_ok) c h01
  · exact (List.all_eq_true.mp addedPart02_ok) c h02
  · exact (List.all_eq_true.mp addedPart03_ok) c h03
  · exact (List.all_eq_true.mp addedPart04_ok) c h04
  · exact (List.all_eq_true.mp addedPart05_ok) c h05
  · exact (List.all_eq_true.mp addedPart06_ok) c h06
  · exact (List.all_eq_true.mp addedPart07_ok) c h07
  · exact (List.all_eq_true.mp addedPart08_ok) c h08
  · exact (List.all_eq_true.mp addedPart09_ok) c h09
  · exact (List.all_eq_true.mp addedPart10_ok) c h10
  · exact (List.all_eq_true.mp addedPart11_ok) c h11
  · exact (List.all_eq_true.mp addedPart12_ok) c h12
  · exact (List.all_eq_true.mp addedPart13_ok) c h13
  · exact (List.all_eq_true.mp addedPart14_ok) c h14
  · exact (List.all_eq_true.mp addedPart15_ok) c h15
  · exact (List.all_eq_true.mp addedPart16_ok) c h16
  · exact (List.all_eq_true.mp addedPart17_ok) c h17
  · exact (List.all_eq_true.mp addedPart18_ok) c h18
  · exact (List.all_eq_true.mp addedPart19_ok) c h19
  · exact (List.all_eq_true.mp addedPart20_ok) c h20
  · exact (List.all_eq_true.mp addedPart21_ok) c h21
  · exact (List.all_eq_true.mp addedPart22_ok) c h22
  · exact (List.all_eq_true.mp addedPart23_ok) c h23
  · exact (List.all_eq_true.mp addedPart24_ok) c h24
  · exact (List.all_eq_true.mp addedPart25_ok) c h25
  · exact (List.all_eq_true.mp addedPart26_ok) c h26
  · exact (List.all_eq_true.mp addedPart27_ok) c h27
  · exact (List.all_eq_true.mp addedPart28_ok) c h28
  · exact (List.all_eq_true.mp addedPart29_ok) c h29

/-- The original 130 certificates plus the exact 119 added records, through order 24
(Part I, Theorem `p1:thm:certificates`). -/
def certs24 : List Cert := Erdos993Lean.Fiber.certs20 ++ addedCerts

/-- Every certificate through order 24 passes the identical checker: the order-20 prefix uses
the retained order-20 kernel theorem and every added record uses a new kernel check
(Part I, Theorem `p1:thm:certificates`). -/
theorem certs_ok : ∀ c ∈ certs24, c.ok = true := by
  intro c hc
  change c ∈ Erdos993Lean.Fiber.certs20 ++ addedCerts at hc
  rcases List.mem_append.mp hc with hold | hnew
  · exact Erdos993Lean.Fiber.certs_ok c hold
  · exact addedCerts_ok c hnew

/-- The keys are exactly the parameter domain (11) through order 24, in original source order
(Part I, Theorem `p1:thm:certificates`); checked by the kernel. -/
theorem certs_cover : certs24.map Cert.key = paramDomain 24 := by
  decide +kernel

end Erdos993Lean.Fiber.Order24
