import Erdos993Lean.Analytic.V22.Analysis.RowPriceBook
import Erdos993Lean.Analytic.V22.Analysis.OuterCells
import Erdos993Lean.Analytic.V22.Analysis.OuterLowerError
import Erdos993Lean.Analytic.V22.Analysis.OuterDeficits
import Erdos993Lean.Analytic.V22.Analysis.BetaMonotonicity

/-! Source Section5 central/wing spike cell cover and native deficit family.
Every row, exact activity, actual M, retained cell, and block survives. Certified
logBounds are consumed. Parent owns Lean verification. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

noncomputable section

-- Exact definitional views remove only the generated private q wrapper.
-- All class, cell, bounds and certified logBounds fields remain native.
private def centralClassesLiteral : List V22.V22Class := [
  ⟨1, "C1", (3793 / 10000 : ℚ), (1 / 2 : ℚ), (2 / 5 : ℚ), (0 / 1 : ℚ), (3 / 5 : ℚ), (17 / 10 : ℚ), (45 / 1 : ℚ), [0, 1, 2]⟩,
  ⟨2, "C2", (1 / 4 : ℚ), (1897 / 5000 : ℚ), (2 / 5 : ℚ), (0 / 1 : ℚ), (69 / 100 : ℚ), (17 / 10 : ℚ), (50 / 1 : ℚ), [3, 4, 5]⟩,
  ⟨3, "C3", (833 / 5000 : ℚ), (2309 / 10000 : ℚ), (0 / 1 : ℚ), (1 / 2 : ℚ), (11 / 25 : ℚ), (7 / 4 : ℚ), (50 / 1 : ℚ), [40, 41, 42, 43]⟩,
  ⟨4, "C4", (2307 / 10000 : ℚ), (341 / 1250 : ℚ), (3 / 20 : ℚ), (3 / 10 : ℚ), (21 / 50 : ℚ), (9 / 5 : ℚ), (40 / 1 : ℚ), [44, 45, 46]⟩,
  ⟨5, "C5", (2727 / 10000 : ℚ), (194 / 625 : ℚ), (3 / 10 : ℚ), (0 / 1 : ℚ), (2 / 5 : ℚ), (17 / 10 : ℚ), (50 / 1 : ℚ), [47, 48, 49]⟩,
  ⟨6, "C6", (3103 / 10000 : ℚ), (861 / 2500 : ℚ), (3 / 10 : ℚ), (0 / 1 : ℚ), (9 / 25 : ℚ), (17 / 10 : ℚ), (50 / 1 : ℚ), [50, 51, 52]⟩,
  ⟨7, "C7", (1721 / 5000 : ℚ), (3847 / 10000 : ℚ), (3 / 10 : ℚ), (1 / 1 : ℚ), (33 / 100 : ℚ), (19 / 10 : ℚ), (50 / 1 : ℚ), [53]⟩,
  ⟨8, "C8", (1923 / 5000 : ℚ), (2 / 5 : ℚ), (3 / 10 : ℚ), (1 / 1 : ℚ), (3 / 10 : ℚ), (19 / 10 : ℚ), (50 / 1 : ℚ), [54]⟩
]

private theorem centralClassesLiteral_eq : V22.classes = centralClassesLiteral := by decide +kernel

private def centralSpikeCellsLiteral : List V22.V22SpikeCell := [
  ⟨0, (21 / 100 : ℚ), (1 / 4 : ℚ), (8 / 1 : ℚ), [(306 / 25 : ℚ), (1172 / 125 : ℚ), (978 / 125 : ℚ), (3137 / 500 : ℚ), (1443 / 250 : ℚ)], [(24471 / 2000 : ℚ), (46879 / 5000 : ℚ), (156471 / 20000 : ℚ), (627307 / 100000 : ℚ), (14429 / 2500 : ℚ)], false⟩,
  ⟨0, (1 / 4 : ℚ), (7 / 25 : ℚ), (8 / 1 : ℚ), [(3727 / 500 : ℚ), (2759 / 500 : ℚ), (863 / 200 : ℚ), (3459 / 1000 : ℚ), (1689 / 500 : ℚ)], [(29813 / 4000 : ℚ), (551769 / 100000 : ℚ), (431453 / 100000 : ℚ), (172929 / 50000 : ℚ), (337703 / 100000 : ℚ)], false⟩,
  ⟨0, (7 / 25 : ℚ), (3 / 10 : ℚ), (8 / 1 : ℚ), [(5149 / 1000 : ℚ), (1837 / 500 : ℚ), (2637 / 1000 : ℚ), (1157 / 500 : ℚ), (1149 / 500 : ℚ)], [(257419 / 50000 : ℚ), (367359 / 100000 : ℚ), (131829 / 50000 : ℚ), (231359 / 100000 : ℚ), (57431 / 25000 : ℚ)], false⟩,
  ⟨0, (3 / 10 : ℚ), (8 / 25 : ℚ), (8 / 1 : ℚ), [(1059 / 250 : ℚ), (2909 / 1000 : ℚ), (1001 / 500 : ℚ), (1861 / 1000 : ℚ), (1861 / 1000 : ℚ)], [(211781 / 50000 : ℚ), (72719 / 25000 : ℚ), (200191 / 100000 : ℚ), (46503 / 25000 : ℚ), (46503 / 25000 : ℚ)], false⟩,
  ⟨0, (8 / 25 : ℚ), (17 / 50 : ℚ), (8 / 1 : ℚ), [(1739 / 500 : ℚ), (2291 / 1000 : ℚ), (783 / 500 : ℚ), (1507 / 1000 : ℚ), (1507 / 1000 : ℚ)], [(86931 / 25000 : ℚ), (114529 / 50000 : ℚ), (78253 / 50000 : ℚ), (150667 / 100000 : ℚ), (150667 / 100000 : ℚ)], false⟩,
  ⟨0, (17 / 50 : ℚ), (9 / 25 : ℚ), (8 / 1 : ℚ), [(2841 / 1000 : ℚ), (943 / 500 : ℚ), (154 / 125 : ℚ), (1219 / 1000 : ℚ), (1219 / 1000 : ℚ)], [(284019 / 100000 : ℚ), (7543 / 4000 : ℚ), (3848 / 3125 : ℚ), (12187 / 10000 : ℚ), (12187 / 10000 : ℚ)], false⟩,
  ⟨0, (9 / 25 : ℚ), (19 / 50 : ℚ), (8 / 1 : ℚ), [(23 / 10 : ℚ), (1283 / 1000 : ℚ), (9827 / 10000 : ℚ), (9827 / 10000 : ℚ), (9827 / 10000 : ℚ)], [(229999 / 100000 : ℚ), (128227 / 100000 : ℚ), (30709 / 31250 : ℚ), (30709 / 31250 : ℚ), (30709 / 31250 : ℚ)], false⟩,
  ⟨0, (19 / 50 : ℚ), (2 / 5 : ℚ), (8 / 1 : ℚ), [(1839 / 1000 : ℚ), (1147 / 1250 : ℚ), (1577 / 2000 : ℚ), (1577 / 2000 : ℚ), (1577 / 2000 : ℚ)], [(22977 / 12500 : ℚ), (917507 / 1000000 : ℚ), (157687 / 200000 : ℚ), (157687 / 200000 : ℚ), (157687 / 200000 : ℚ)], false⟩,
  ⟨0, (2 / 5 : ℚ), (21 / 50 : ℚ), (8 / 1 : ℚ), [(1493 / 1000 : ℚ), (6683 / 10000 : ℚ), (6281 / 10000 : ℚ), (6281 / 10000 : ℚ), (6281 / 10000 : ℚ)], [(37323 / 25000 : ℚ), (2673 / 4000 : ℚ), (628081 / 1000000 : ℚ), (628081 / 1000000 : ℚ), (628081 / 1000000 : ℚ)], false⟩,
  ⟨0, (21 / 50 : ℚ), (11 / 25 : ℚ), (8 / 1 : ℚ), [(1229 / 1000 : ℚ), (1239 / 2500 : ℚ), (1239 / 2500 : ℚ), (1239 / 2500 : ℚ), (1239 / 2500 : ℚ)], [(30703 / 25000 : ℚ), (247751 / 500000 : ℚ), (247751 / 500000 : ℚ), (247751 / 500000 : ℚ), (247751 / 500000 : ℚ)], false⟩,
  ⟨0, (11 / 25 : ℚ), (23 / 50 : ℚ), (209 / 25 : ℚ), [(3691 / 5000 : ℚ), (3859 / 10000 : ℚ), (3859 / 10000 : ℚ), (3859 / 10000 : ℚ), (3859 / 10000 : ℚ)], [(369091 / 500000 : ℚ), (19293 / 50000 : ℚ), (19293 / 50000 : ℚ), (19293 / 50000 : ℚ), (19293 / 50000 : ℚ)], false⟩,
  ⟨0, (23 / 50 : ℚ), (12 / 25 : ℚ), (437 / 50 : ℚ), [(4389 / 10000 : ℚ), (2953 / 10000 : ℚ), (2953 / 10000 : ℚ), (2953 / 10000 : ℚ), (2953 / 10000 : ℚ)], [(219427 / 500000 : ℚ), (36911 / 125000 : ℚ), (36911 / 125000 : ℚ), (36911 / 125000 : ℚ), (36911 / 125000 : ℚ)], false⟩,
  ⟨0, (12 / 25 : ℚ), (1 / 2 : ℚ), (228 / 25 : ℚ), [(311 / 1250 : ℚ), (2207 / 10000 : ℚ), (2207 / 10000 : ℚ), (2207 / 10000 : ℚ), (2207 / 10000 : ℚ)], [(248711 / 1000000 : ℚ), (11033 / 50000 : ℚ), (11033 / 50000 : ℚ), (11033 / 50000 : ℚ), (11033 / 50000 : ℚ)], false⟩,
  ⟨0, (1 / 2 : ℚ), (13 / 25 : ℚ), (19 / 2 : ℚ), [(319 / 2000 : ℚ), (319 / 2000 : ℚ), (319 / 2000 : ℚ), (319 / 2000 : ℚ), (319 / 2000 : ℚ)], [(2491 / 15625 : ℚ), (2491 / 15625 : ℚ), (2491 / 15625 : ℚ), (2491 / 15625 : ℚ), (2491 / 15625 : ℚ)], false⟩,
  ⟨0, (13 / 25 : ℚ), (11 / 20 : ℚ), (247 / 25 : ℚ), [(607 / 5000 : ℚ), (607 / 5000 : ℚ), (607 / 5000 : ℚ), (607 / 5000 : ℚ), (607 / 5000 : ℚ)], [(121339 / 1000000 : ℚ), (121339 / 1000000 : ℚ), (121339 / 1000000 : ℚ), (121339 / 1000000 : ℚ), (121339 / 1000000 : ℚ)], false⟩,
  ⟨0, (11 / 20 : ℚ), (29 / 50 : ℚ), (209 / 20 : ℚ), [(192 / 3125 : ℚ), (192 / 3125 : ℚ), (192 / 3125 : ℚ), (192 / 3125 : ℚ), (192 / 3125 : ℚ)], [(61431 / 1000000 : ℚ), (61431 / 1000000 : ℚ), (61431 / 1000000 : ℚ), (61431 / 1000000 : ℚ), (61431 / 1000000 : ℚ)], false⟩,
  ⟨0, (29 / 50 : ℚ), (59 / 100 : ℚ), (551 / 50 : ℚ), [(6637 / 1000000 : ℚ), (6637 / 1000000 : ℚ), (6637 / 1000000 : ℚ), (6637 / 1000000 : ℚ), (6637 / 1000000 : ℚ)], [(663643 / 100000000 : ℚ), (663643 / 100000000 : ℚ), (663643 / 100000000 : ℚ), (663643 / 100000000 : ℚ), (663643 / 100000000 : ℚ)], false⟩,
  ⟨0, (59 / 100 : ℚ), (3 / 5 : ℚ), (1121 / 100 : ℚ), [(0 / 1 : ℚ), (0 / 1 : ℚ), (0 / 1 : ℚ), (0 / 1 : ℚ), (0 / 1 : ℚ)], [(0 / 1 : ℚ), (0 / 1 : ℚ), (0 / 1 : ℚ), (0 / 1 : ℚ), (0 / 1 : ℚ)], false⟩,
  ⟨1, (21 / 100 : ℚ), (17 / 50 : ℚ), (189 / 20 : ℚ), [(1437 / 10 : ℚ), (701 / 5 : ℚ), (978 / 5 : ℚ), (3107 / 10 : ℚ), (296 / 25 : ℚ)], [(71819 / 500 : ℚ), (140137 / 1000 : ℚ), (195513 / 1000 : ℚ), (310683 / 1000 : ℚ), (118329 / 10000 : ℚ)], false⟩,
  ⟨1, (17 / 50 : ℚ), (21 / 50 : ℚ), (153 / 10 : ℚ), [(431 / 10 : ℚ), (5353 / 100 : ℚ), (529 / 5 : ℚ), (477 / 25 : ℚ), (897 / 500 : ℚ)], [(86189 / 2000 : ℚ), (267613 / 5000 : ℚ), (26443 / 250 : ℚ), (190779 / 10000 : ℚ), (287 / 160 : ℚ)], false⟩,
  ⟨1, (21 / 50 : ℚ), (3 / 5 : ℚ), (189 / 10 : ℚ), [(531 / 200 : ℚ), (531 / 200 : ℚ), (531 / 200 : ℚ), (1737 / 1000 : ℚ), (343 / 200 : ℚ)], [(132739 / 50000 : ℚ), (132739 / 50000 : ℚ), (132739 / 50000 : ℚ), (173629 / 100000 : ℚ), (171481 / 100000 : ℚ)], true⟩,
  ⟨2, (21 / 100 : ℚ), (23 / 50 : ℚ), (21 / 2 : ℚ), [(5871 / 100 : ℚ), (2017 / 50 : ℚ), (839 / 25 : ℚ), (2669 / 100 : ℚ), (646 / 25 : ℚ)], [(293549 / 5000 : ℚ), (403307 / 10000 : ℚ), (335589 / 10000 : ℚ), (33359 / 1250 : ℚ), (129199 / 5000 : ℚ)], false⟩,
  ⟨2, (23 / 50 : ℚ), (3 / 5 : ℚ), (23 / 1 : ℚ), [(9679 / 10000 : ℚ), (9009 / 10000 : ℚ), (873 / 1000 : ℚ), (2161 / 2500 : ℚ), (4313 / 5000 : ℚ)], [(967807 / 1000000 : ℚ), (180163 / 200000 : ℚ), (872969 / 1000000 : ℚ), (432181 / 500000 : ℚ), (107813 / 125000 : ℚ)], true⟩,
  ⟨2, (3 / 5 : ℚ), (69 / 100 : ℚ), (30 / 1 : ℚ), [(2327 / 25000 : ℚ), (2327 / 25000 : ℚ), (2327 / 25000 : ℚ), (2327 / 25000 : ℚ), (2327 / 25000 : ℚ)], [(93073 / 1000000 : ℚ), (93073 / 1000000 : ℚ), (93073 / 1000000 : ℚ), (93073 / 1000000 : ℚ), (93073 / 1000000 : ℚ)], true⟩,
  ⟨3, (21 / 100 : ℚ), (9 / 25 : ℚ), (21 / 2 : ℚ), [(543 / 25 : ℚ), (181 / 10 : ℚ), (1581 / 100 : ℚ), (1389 / 100 : ℚ), (1357 / 100 : ℚ)], [(43427 / 2000 : ℚ), (180973 / 10000 : ℚ), (158043 / 10000 : ℚ), (69449 / 5000 : ℚ), (27137 / 2000 : ℚ)], false⟩,
  ⟨3, (9 / 25 : ℚ), (21 / 50 : ℚ), (18 / 1 : ℚ), [(1567 / 1000 : ℚ), (651 / 500 : ℚ), (63 / 50 : ℚ), (1253 / 1000 : ℚ), (1253 / 1000 : ℚ)], [(78329 / 50000 : ℚ), (65051 / 50000 : ℚ), (125983 / 100000 : ℚ), (125251 / 100000 : ℚ), (3131 / 2500 : ℚ)], false⟩,
  ⟨3, (21 / 50 : ℚ), (11 / 25 : ℚ), (21 / 1 : ℚ), [(1239 / 2500 : ℚ), (1239 / 2500 : ℚ), (1239 / 2500 : ℚ), (1239 / 2500 : ℚ), (1239 / 2500 : ℚ)], [(247751 / 500000 : ℚ), (247751 / 500000 : ℚ), (247751 / 500000 : ℚ), (247751 / 500000 : ℚ), (247751 / 500000 : ℚ)], false⟩,
  ⟨4, (21 / 100 : ℚ), (8 / 25 : ℚ), (42 / 5 : ℚ), [(517 / 25 : ℚ), (1589 / 100 : ℚ), (1329 / 100 : ℚ), (537 / 50 : ℚ), (252 / 25 : ℚ)], [(20679 / 1000 : ℚ), (39707 / 2500 : ℚ), (5313 / 400 : ℚ), (107389 / 10000 : ℚ), (2519 / 250 : ℚ)], false⟩,
  ⟨4, (8 / 25 : ℚ), (9 / 25 : ℚ), (64 / 5 : ℚ), [(397 / 125 : ℚ), (393 / 200 : ℚ), (343 / 200 : ℚ), (337 / 200 : ℚ), (1683 / 1000 : ℚ)], [(317561 / 100000 : ℚ), (98207 / 50000 : ℚ), (85733 / 50000 : ℚ), (168479 / 100000 : ℚ), (6731 / 4000 : ℚ)], false⟩,
  ⟨4, (9 / 25 : ℚ), (19 / 50 : ℚ), (72 / 5 : ℚ), [(407 / 250 : ℚ), (4921 / 5000 : ℚ), (9827 / 10000 : ℚ), (9827 / 10000 : ℚ), (9827 / 10000 : ℚ)], [(162799 / 100000 : ℚ), (984129 / 1000000 : ℚ), (30709 / 31250 : ℚ), (30709 / 31250 : ℚ), (30709 / 31250 : ℚ)], false⟩,
  ⟨4, (19 / 50 : ℚ), (2 / 5 : ℚ), (76 / 5 : ℚ), [(4763 / 10000 : ℚ), (4763 / 10000 : ℚ), (4763 / 10000 : ℚ), (4763 / 10000 : ℚ), (4763 / 10000 : ℚ)], [(476261 / 1000000 : ℚ), (476261 / 1000000 : ℚ), (476261 / 1000000 : ℚ), (476261 / 1000000 : ℚ), (476261 / 1000000 : ℚ)], true⟩,
  ⟨4, (2 / 5 : ℚ), (21 / 50 : ℚ), (16 / 1 : ℚ), [(1663 / 10000 : ℚ), (1663 / 10000 : ℚ), (1663 / 10000 : ℚ), (1663 / 10000 : ℚ), (1663 / 10000 : ℚ)], [(166267 / 1000000 : ℚ), (166267 / 1000000 : ℚ), (166267 / 1000000 : ℚ), (166267 / 1000000 : ℚ), (166267 / 1000000 : ℚ)], true⟩,
  ⟨5, (21 / 100 : ℚ), (17 / 50 : ℚ), (21 / 2 : ℚ), [(2327 / 100 : ℚ), (917 / 50 : ℚ), (378 / 25 : ℚ), (302 / 25 : ℚ), (1171 / 100 : ℚ)], [(232643 / 10000 : ℚ), (183383 / 10000 : ℚ), (75587 / 5000 : ℚ), (120751 / 10000 : ℚ), (117033 / 10000 : ℚ)], false⟩,
  ⟨5, (17 / 50 : ℚ), (19 / 50 : ℚ), (17 / 1 : ℚ), [(9787 / 10000 : ℚ), (9787 / 10000 : ℚ), (9787 / 10000 : ℚ), (9787 / 10000 : ℚ), (9787 / 10000 : ℚ)], [(19573 / 20000 : ℚ), (19573 / 20000 : ℚ), (19573 / 20000 : ℚ), (19573 / 20000 : ℚ), (19573 / 20000 : ℚ)], true⟩,
  ⟨5, (19 / 50 : ℚ), (2 / 5 : ℚ), (19 / 1 : ℚ), [(0 / 1 : ℚ), (0 / 1 : ℚ), (0 / 1 : ℚ), (0 / 1 : ℚ), (0 / 1 : ℚ)], [(0 / 1 : ℚ), (0 / 1 : ℚ), (0 / 1 : ℚ), (0 / 1 : ℚ), (0 / 1 : ℚ)], true⟩,
  ⟨6, (21 / 100 : ℚ), (3 / 10 : ℚ), (21 / 2 : ℚ), [(431 / 20 : ℚ), (1559 / 100 : ℚ), (1229 / 100 : ℚ), (8923 / 1000 : ℚ), (4279 / 500 : ℚ)], [(26937 / 1250 : ℚ), (155871 / 10000 : ℚ), (122811 / 10000 : ℚ), (446113 / 50000 : ℚ), (855727 / 100000 : ℚ)], false⟩,
  ⟨6, (3 / 10 : ℚ), (17 / 50 : ℚ), (15 / 1 : ℚ), [(241 / 125 : ℚ), (241 / 125 : ℚ), (241 / 125 : ℚ), (241 / 125 : ℚ), (241 / 125 : ℚ)], [(7711 / 4000 : ℚ), (7711 / 4000 : ℚ), (7711 / 4000 : ℚ), (7711 / 4000 : ℚ), (7711 / 4000 : ℚ)], true⟩,
  ⟨6, (17 / 50 : ℚ), (9 / 25 : ℚ), (17 / 1 : ℚ), [(177 / 500 : ℚ), (177 / 500 : ℚ), (177 / 500 : ℚ), (177 / 500 : ℚ), (177 / 500 : ℚ)], [(176977 / 500000 : ℚ), (176977 / 500000 : ℚ), (176977 / 500000 : ℚ), (176977 / 500000 : ℚ), (176977 / 500000 : ℚ)], true⟩,
  ⟨7, (21 / 100 : ℚ), (1 / 4 : ℚ), (21 / 2 : ℚ), [(579 / 25 : ℚ), (332 / 25 : ℚ), (9827 / 1000 : ℚ), (6139 / 1000 : ℚ), (719 / 125 : ℚ)], [(57897 / 2500 : ℚ), (13271 / 1000 : ℚ), (196523 / 20000 : ℚ), (19183 / 3125 : ℚ), (575111 / 100000 : ℚ)], false⟩,
  ⟨7, (1 / 4 : ℚ), (3 / 10 : ℚ), (25 / 2 : ℚ), [(4637 / 1000 : ℚ), (4637 / 1000 : ℚ), (4571 / 1000 : ℚ), (491 / 125 : ℚ), (193 / 50 : ℚ)], [(463663 / 100000 : ℚ), (463663 / 100000 : ℚ), (11427 / 2500 : ℚ), (392703 / 100000 : ℚ), (385907 / 100000 : ℚ)], true⟩,
  ⟨7, (3 / 10 : ℚ), (8 / 25 : ℚ), (15 / 1 : ℚ), [(1783 / 2000 : ℚ), (1783 / 2000 : ℚ), (1783 / 2000 : ℚ), (1783 / 2000 : ℚ), (1783 / 2000 : ℚ)], [(891459 / 1000000 : ℚ), (891459 / 1000000 : ℚ), (891459 / 1000000 : ℚ), (891459 / 1000000 : ℚ), (891459 / 1000000 : ℚ)], true⟩,
  ⟨7, (8 / 25 : ℚ), (33 / 100 : ℚ), (16 / 1 : ℚ), [(7463 / 1000000 : ℚ), (7463 / 1000000 : ℚ), (7463 / 1000000 : ℚ), (7463 / 1000000 : ℚ), (7463 / 1000000 : ℚ)], [(746231 / 100000000 : ℚ), (746231 / 100000000 : ℚ), (746231 / 100000000 : ℚ), (746231 / 100000000 : ℚ), (746231 / 100000000 : ℚ)], true⟩,
  ⟨8, (21 / 100 : ℚ), (7 / 25 : ℚ), (21 / 2 : ℚ), [(457 / 50 : ℚ), (457 / 50 : ℚ), (457 / 50 : ℚ), (7879 / 1000 : ℚ), (7289 / 1000 : ℚ)], [(228499 / 25000 : ℚ), (228499 / 25000 : ℚ), (228499 / 25000 : ℚ), (157577 / 20000 : ℚ), (364421 / 50000 : ℚ)], true⟩,
  ⟨8, (7 / 25 : ℚ), (3 / 10 : ℚ), (14 / 1 : ℚ), [(341 / 400 : ℚ), (341 / 400 : ℚ), (341 / 400 : ℚ), (341 / 400 : ℚ), (341 / 400 : ℚ)], [(85241 / 100000 : ℚ), (85241 / 100000 : ℚ), (85241 / 100000 : ℚ), (85241 / 100000 : ℚ), (85241 / 100000 : ℚ)], true⟩
]

private theorem centralSpikeCellsLiteral_eq : V22.spikeCells = centralSpikeCellsLiteral := by decide +kernel


theorem central_spike_cell_metadata {c : V22.V22SpikeCell} (hc : c ∈ V22.spikeCells)
    (hid : c.classId = 0) :
    (21 / 100 : ℝ) ≤ c.lo ∧ (c.hi : ℝ) ≤ 3 / 5 ∧
      8 ≤ (c.ma : ℝ) ∧ (c.ma : ℝ) = max 8 (19 * (c.lo : ℝ)) ∧
      c.window = false ∧ V22.spikeRm c = (1 / 4 : ℝ) := by
  rw [centralSpikeCellsLiteral_eq] at hc
  simp only [centralSpikeCellsLiteral, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num at hid
  all_goals
    norm_num [V22.spikeRm, V22.spikeClass, centralClassesLiteral_eq, centralClassesLiteral]

set_option maxHeartbeats 2000000 in
theorem central_spike_cells_cover {t : ℝ} (ht0 : (21 / 100 : ℝ) ≤ t)
    (ht1 : t ≤ 3 / 5) :
    ∃ c ∈ V22.spikeCells, c.classId = 0 ∧ V22.Checks.inCell c.lo c.hi t := by
  by_cases h0 : t ≤ (1 / 4 : ℝ)
  · refine ⟨V22.spikeCells.getD 0 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨ht0, h0⟩
  by_cases h1 : t ≤ (7 / 25 : ℝ)
  · refine ⟨V22.spikeCells.getD 1 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h0).le, h1⟩
  by_cases h2 : t ≤ (3 / 10 : ℝ)
  · refine ⟨V22.spikeCells.getD 2 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h1).le, h2⟩
  by_cases h3 : t ≤ (8 / 25 : ℝ)
  · refine ⟨V22.spikeCells.getD 3 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h2).le, h3⟩
  by_cases h4 : t ≤ (17 / 50 : ℝ)
  · refine ⟨V22.spikeCells.getD 4 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h3).le, h4⟩
  by_cases h5 : t ≤ (9 / 25 : ℝ)
  · refine ⟨V22.spikeCells.getD 5 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h4).le, h5⟩
  by_cases h6 : t ≤ (19 / 50 : ℝ)
  · refine ⟨V22.spikeCells.getD 6 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h5).le, h6⟩
  by_cases h7 : t ≤ (2 / 5 : ℝ)
  · refine ⟨V22.spikeCells.getD 7 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h6).le, h7⟩
  by_cases h8 : t ≤ (21 / 50 : ℝ)
  · refine ⟨V22.spikeCells.getD 8 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h7).le, h8⟩
  by_cases h9 : t ≤ (11 / 25 : ℝ)
  · refine ⟨V22.spikeCells.getD 9 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h8).le, h9⟩
  by_cases h10 : t ≤ (23 / 50 : ℝ)
  · refine ⟨V22.spikeCells.getD 10 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h9).le, h10⟩
  by_cases h11 : t ≤ (12 / 25 : ℝ)
  · refine ⟨V22.spikeCells.getD 11 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h10).le, h11⟩
  by_cases h12 : t ≤ (1 / 2 : ℝ)
  · refine ⟨V22.spikeCells.getD 12 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h11).le, h12⟩
  by_cases h13 : t ≤ (13 / 25 : ℝ)
  · refine ⟨V22.spikeCells.getD 13 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h12).le, h13⟩
  by_cases h14 : t ≤ (11 / 20 : ℝ)
  · refine ⟨V22.spikeCells.getD 14 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h13).le, h14⟩
  by_cases h15 : t ≤ (29 / 50 : ℝ)
  · refine ⟨V22.spikeCells.getD 15 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h14).le, h15⟩
  by_cases h16 : t ≤ (59 / 100 : ℝ)
  · refine ⟨V22.spikeCells.getD 16 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
    norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h15).le, h16⟩
  refine ⟨V22.spikeCells.getD 17 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral], ?_⟩
  norm_num [centralSpikeCellsLiteral_eq, centralSpikeCellsLiteral, V22.Checks.inCell]
  exact ⟨(lt_of_not_ge h16).le, ht1⟩

theorem central_spike_cell_below_cut {c : V22.V22SpikeCell} (hc : c ∈ V22.spikeCells)
    (hid : c.classId = 0) {tau : ℝ}
    (htau : tau = 3 / 5 ∨ tau = 29 / 50 ∨ tau = 11 / 20 ∨ tau = 13 / 25)
    (hlo : (c.lo : ℝ) < tau) : (c.hi : ℝ) ≤ tau := by
  rw [centralSpikeCellsLiteral_eq] at hc
  simp only [centralSpikeCellsLiteral, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases htau with rfl | rfl | rfl | rfl <;> norm_num at hid
  all_goals norm_num at hlo
  all_goals norm_num


def centralRowFactsQ (p : ℕ) : Prop :=
  V22.classForPiece p = none ∧
    (rowCutoffQ p = 3 / 5 ∨ rowCutoffQ p = 29 / 50 ∨ rowCutoffQ p = 11 / 20 ∨ rowCutoffQ p = 13 / 25) ∧
    3 / 8 ≤ e6QaQ p ∧ e6QbQ p ≤ 5 / 8

theorem central_row_tableQ : ∀ p < 55, 6 ≤ p → p ≤ 39 → centralRowFactsQ p := by
  unfold centralRowFactsQ
  decide +kernel

theorem central_row_metadata {p : ℕ} (hp0 : 6 ≤ p) (hp1 : p ≤ 39) :
    V22.classForPiece p = none ∧ V22.excess p = 0 ∧
    (V22.spikeCutoff p = 3 / 5 ∨ V22.spikeCutoff p = 29 / 50 ∨
      V22.spikeCutoff p = 11 / 20 ∨ V22.spikeCutoff p = 13 / 25) ∧
    3 / 8 ≤ V22.Checks.rowQa p ∧ V22.Checks.rowQb p ≤ 5 / 8 := by
  obtain ⟨hn, hcut, hqa, hqb⟩ := central_row_tableQ p (by omega) hp0 hp1
  refine ⟨hn, by simp [V22.excess, hn], ?_, ?_, ?_⟩
  · rw [row_cutoff_eq_cast]
    rcases hcut with h | h | h | h
    · left; rw [h]; norm_num
    · right; left; rw [h]; norm_num
    · right; right; left; rw [h]; norm_num
    · right; right; right; rw [h]; norm_num
  · rw [e6_rowQa_cast]
    have h := (Rat.cast_le (K := ℝ)).2 hqa
    norm_num at h
    exact h
  · rw [e6_rowQb_cast]
    have h := (Rat.cast_le (K := ℝ)).2 hqb
    norm_num at h
    exact h

theorem central_row_r_cap {p : ℕ} (hp0 : 6 ≤ p) (hp1 : p ≤ 39) {q : ℝ}
    (hqlo : V22.Checks.rowQa p ≤ q) (hqhi : q ≤ V22.Checks.rowQb p) : |2 * q - 1| ≤ 1 / 4 := by
  obtain ⟨_, _, _, hqa, hqb⟩ := central_row_metadata hp0 hp1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem central_spike_block_positive (hA3 : V22.Checks.lemma_7_4)
    (hBonus : V22.Checks.lemma_7_7) (hB2 : V22.Checks.lemma_7_13)
    {cell : V22.V22SpikeCell} (hc : cell ∈ V22.spikeCells) (hid : cell.classId = 0)
    {i M : ℕ} (hi : i < 5) {r mu : ℝ} (hM : 8 ≤ M) (hmu : 0 < mu)
    (hr0 : 0 ≤ r) (hrm : r ≤ 1 / 4)
    (ht : V22.Checks.inCell cell.lo cell.hi ((M : ℝ) / mu))
    (hblock : V22.inSpikeBlock cell i (M : ℝ))
    (hvalid : V22.Checks.spikePhiCoefficientsValid cell i ((M : ℝ) / mu)) :
    V22.deficitG ((1 + r) / 2) mu 0 0 M ≤ V22.Checks.spikePhi cell i ((M : ℝ) / mu) M := by
  obtain ⟨htlo, hthi, hma, _, _, hRm⟩ := central_spike_cell_metadata hc hid
  let M1 : ℝ := (V22.blockMultipliers.getD i 0 : ℕ) * (cell.ma : ℝ)
  have hM1 : 8 ≤ M1 := by
    have hm := outer_block_multiplier_ge_one hi
    have hmul := mul_le_mul_of_nonneg_right hm (by linarith : 0 ≤ (cell.ma : ℝ))
    dsimp [M1]
    linarith
  have hMlo : M1 ≤ (M : ℝ) := hblock.1
  have hQuarter : V22.Checks.bonusConditions (1 / 4 : ℝ) 10 := by
    convert hBonus (1 / 4, 10) (by norm_num [V22.Checks.bonusPairs]) using 1 <;> norm_num
  have hUL := lambdaBonus_source hQuarter
    (by norm_num) (by norm_num) (by norm_num) (by exact_mod_cast (show 10 ≤ M + 2 from by omega)) hr0 hrm hmu
  have hL := outer_lower_error_from_slack hB2 hM hmu hr0 hrm (by norm_num)
    (by norm_num) (by exact_mod_cast (show 10 ≤ M + 2 from by omega))
    (ht.2.trans hthi) (by norm_num) hB2.1
  have ht0 : (387 / 2500 : ℝ) ≤ (M : ℝ) / mu := by linarith [ht.1]
  have ht1 : (M : ℝ) / mu ≤ 69 / 100 := by linarith [ht.2]
  by_cases hi4 : i = 4
  · have hValid : V22.phiInfiniteBlockCoefficientsValid ((M : ℝ) / mu) M1 (1 / 4) := by
      simpa only [V22.Checks.spikePhiCoefficientsValid, if_pos hi4, hRm] using hvalid
    have hM1large : 128 ≤ M1 := by
      dsimp [M1]
      rw [hi4]
      norm_num [V22.blockMultipliers] <;> nlinarith
    have hBeta : ∀ N : ℝ, M1 + 2 ≤ N →
        V22.betaE (M1 + 2) (1 / 4) (cappedNu (1 / 4) (M1 + 2)) ≤
          V22.betaE N (1 / 4) (cappedNu (1 / 4) N) := by
      intro N hN
      have h := cappedBeta_quarter_monotone hA3
        (show M1 + 2 ∈ Ici (67 / 5) from by change 67 / 5 ≤ M1 + 2; linarith)
        (show N ∈ Ici (67 / 5) from by change 67 / 5 ≤ N; linarith) hN
      simpa only [V22.Checks.cappedBeta, cappedNu] using h
    have h := source_spike_infinite_block hM hmu hM1 hMlo hr0 hrm (by norm_num)
      ht0 ht1 hValid hBeta hUL hL
    simpa only [V22.Checks.spikePhi, if_pos hi4, hRm] using h
  · have hValid : V22.phiBlockCoefficientsValid M1 (2 * M1) (1 / 4) := by
      simpa only [V22.Checks.spikePhiCoefficientsValid, if_neg hi4, hRm] using hvalid
    have hMhi : (M : ℝ) ≤ 2 * M1 := by
      have h := hblock.2.resolve_left hi4
      simpa only [M1, mul_assoc] using h
    have h := source_spike_finite_block hM hmu hM1 hMlo hMhi hr0 hrm (by norm_num)
      ht0 ht1 hValid hUL hL
    simpa only [V22.Checks.spikePhi, if_neg hi4, hRm] using h

theorem central_spike_block_native (hA3 : V22.Checks.lemma_7_4)
    (hBonus : V22.Checks.lemma_7_7) (hB2 : V22.Checks.lemma_7_13)
    {cell : V22.V22SpikeCell} (hc : cell ∈ V22.spikeCells) (hid : cell.classId = 0)
    {i M : ℕ} (hi : i < 5) {q mu : ℝ} (hM : 8 ≤ M) (hmu : 0 < mu)
    (hr : |2 * q - 1| ≤ 1 / 4)
    (ht : V22.Checks.inCell cell.lo cell.hi ((M : ℝ) / mu))
    (hblock : V22.inSpikeBlock cell i (M : ℝ))
    (hvalid : V22.Checks.spikePhiCoefficientsValid cell i ((M : ℝ) / mu)) :
    V22.deficitG q mu 0 0 M ≤ V22.Checks.spikePhi cell i ((M : ℝ) / mu) M := by
  have hq : 0 < q ∧ q < 1 := by have h := abs_le.mp hr; constructor <;> linarith
  by_cases hhalf : 1 / 2 ≤ q
  · have h := central_spike_block_positive hA3 hBonus hB2 hc hid hi hM hmu
      (by linarith : 0 ≤ 2 * q - 1) ((le_abs_self _).trans hr) ht hblock hvalid
    simpa only [show (1 + (2 * q - 1)) / 2 = q from by ring] using h
  · have h := central_spike_block_positive hA3 hBonus hB2 hc hid hi hM hmu
      (by linarith : 0 ≤ 1 - 2 * q) (by have h := abs_le.mp hr; linarith : 1 - 2 * q ≤ 1 / 4) ht hblock hvalid
    have he : (1 + (1 - 2 * q)) / 2 = 1 - q := by ring
    rw [he, shared_deficitG_reflection hq.1 hq.2] at h
    exact h

/-- Central and wing price-book family from exact B3 certificates, all
five blocks, every native integer atom, and the inherited row identity. -/
theorem central_row_cell_deficits (hA3 : V22.Checks.lemma_7_4)
    (hBonus : V22.Checks.lemma_7_7) (hB2 : V22.Checks.lemma_7_13)
    (hB3 : V22.Checks.lemma_7_14_certified)
    {p : ℕ} (hp0 : 6 ≤ p) (hp1 : p ≤ 39) {q mu : ℝ}
    (hqlo : V22.Checks.rowQa p ≤ q) (hqhi : q ≤ V22.Checks.rowQb p)
    (hmu : V22.startingMean p ≤ mu) : rowPriceCellDeficits p q mu 0 := by
  obtain ⟨hnone, hb, hCut, _, _⟩ := central_row_metadata hp0 hp1
  obtain ⟨hstart, _⟩ := e6_startingMean_bounds (by omega : p < 55)
  have hmup : 0 < mu := by linarith
  have hr := central_row_r_cap hp0 hp1 hqlo hqhi
  intro M hM ht21 htcut
  have hCut6 : V22.spikeCutoff p ≤ 3 / 5 := by
    rcases hCut with h | h | h | h <;> rw [h] <;> norm_num
  obtain ⟨cell, hc, hid, ht⟩ := central_spike_cells_cover ht21 (htcut.le.trans hCut6)
  obtain ⟨hlo, _, hma, hmaEq, hwindow, _⟩ := central_spike_cell_metadata hc hid
  have hlo0 : 0 ≤ (cell.lo : ℝ) := by linarith
  have hBelow := central_spike_cell_below_cut hc hid hCut (ht.1.trans_lt htcut)
  have hUsed : V22.Checks.rowUsesCell p cell := by
    simpa only [V22.Checks.rowUsesCell, hnone] using ⟨hid, hBelow⟩
  have hmaM : (cell.ma : ℝ) ≤ (M : ℝ) := by
    rw [hmaEq]
    have htaMu := (le_div_iff₀ hmup).1 ht.1
    have htaStart := mul_le_mul_of_nonneg_left (show (19 : ℝ) ≤ mu from by linarith) hlo0
    exact max_le (by exact_mod_cast hM) (by nlinarith)
  obtain ⟨i, hi, hblock⟩ := outer_spike_blocks_cover (by linarith : 0 < (cell.ma : ℝ)) hmaM
  obtain ⟨hvalid, hCert⟩ := hB3.1 cell hc hwindow i hi ((M : ℝ) / mu) M ht hblock
  have hNative := central_spike_block_native hA3 hBonus hB2 hc hid hi hM hmup hr ht hblock hvalid
  refine ⟨cell, hc, hUsed, hlo0, ht, i, hi, hblock, ?_⟩
  simpa only [hb, add_zero] using hNative.trans hCert

end

end Erdos993Lean.Analytic.V22.Analysis
