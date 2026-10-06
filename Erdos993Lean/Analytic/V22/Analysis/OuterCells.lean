import Erdos993Lean.Analytic.V22.Analysis.WindowTheorems

/-! Source: Corollary 5.15, the exact class spike cells and M blocks.
Only rational data identities and coverage are established here. Parent owns
Lean verification; no displayed bound is asserted by this module. -/

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

deriving instance DecidableEq for V22.V22SpikeCell

-- Exact kernel-checked literal views remove only the generated private q wrapper.
-- All class, cell, bounds and certified logBounds fields remain native.
private def outerClassesLiteral : List V22.V22Class := [
  ⟨1, "C1", (3793 / 10000 : ℚ), (1 / 2 : ℚ), (2 / 5 : ℚ), (0 / 1 : ℚ), (3 / 5 : ℚ), (17 / 10 : ℚ), (45 / 1 : ℚ), [0, 1, 2]⟩,
  ⟨2, "C2", (1 / 4 : ℚ), (1897 / 5000 : ℚ), (2 / 5 : ℚ), (0 / 1 : ℚ), (69 / 100 : ℚ), (17 / 10 : ℚ), (50 / 1 : ℚ), [3, 4, 5]⟩,
  ⟨3, "C3", (833 / 5000 : ℚ), (2309 / 10000 : ℚ), (0 / 1 : ℚ), (1 / 2 : ℚ), (11 / 25 : ℚ), (7 / 4 : ℚ), (50 / 1 : ℚ), [40, 41, 42, 43]⟩,
  ⟨4, "C4", (2307 / 10000 : ℚ), (341 / 1250 : ℚ), (3 / 20 : ℚ), (3 / 10 : ℚ), (21 / 50 : ℚ), (9 / 5 : ℚ), (40 / 1 : ℚ), [44, 45, 46]⟩,
  ⟨5, "C5", (2727 / 10000 : ℚ), (194 / 625 : ℚ), (3 / 10 : ℚ), (0 / 1 : ℚ), (2 / 5 : ℚ), (17 / 10 : ℚ), (50 / 1 : ℚ), [47, 48, 49]⟩,
  ⟨6, "C6", (3103 / 10000 : ℚ), (861 / 2500 : ℚ), (3 / 10 : ℚ), (0 / 1 : ℚ), (9 / 25 : ℚ), (17 / 10 : ℚ), (50 / 1 : ℚ), [50, 51, 52]⟩,
  ⟨7, "C7", (1721 / 5000 : ℚ), (3847 / 10000 : ℚ), (3 / 10 : ℚ), (1 / 1 : ℚ), (33 / 100 : ℚ), (19 / 10 : ℚ), (50 / 1 : ℚ), [53]⟩,
  ⟨8, "C8", (1923 / 5000 : ℚ), (2 / 5 : ℚ), (3 / 10 : ℚ), (1 / 1 : ℚ), (3 / 10 : ℚ), (19 / 10 : ℚ), (50 / 1 : ℚ), [54]⟩
]

private theorem outerClassesLiteral_eq : V22.classes = outerClassesLiteral := by decide +kernel

private def outerSpikeCellsLiteral : List V22.V22SpikeCell := [
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

private theorem outerSpikeCellsLiteral_eq : V22.spikeCells = outerSpikeCellsLiteral := by decide +kernel

theorem outer_cell_class_fields {c : V22.V22SpikeCell} {k : V22.V22Class}
    (hk : k ∈ V22.classes) (hid : k.classId = c.classId) :
    c.classId ≠ 0 ∧ V22.spikeRm c = (k.rb : ℝ) ∧ V22.spikeMean c = (k.muD : ℝ) := by
  rw [outerClassesLiteral_eq] at hk
  simp only [outerClassesLiteral, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [V22.spikeRm, V22.spikeMean, V22.spikeClass, ← hid, outerClassesLiteral_eq, outerClassesLiteral] <;> norm_num

set_option maxHeartbeats 2000000 in
theorem outer_cell_metadata {c : V22.V22SpikeCell} (hc : c ∈ V22.spikeCells)
    {k : V22.V22Class} (hk : k ∈ V22.classes) (hid : k.classId = c.classId) :
    (21 / 100 : ℝ) ≤ c.lo ∧ (c.hi : ℝ) ≤ (k.tau : ℝ) ∧
      (c.hi : ℝ) ≤ 69 / 100 ∧ 8 ≤ (c.ma : ℝ) ∧ (c.ma : ℝ) = (k.muD : ℝ) * (c.lo : ℝ) := by
  rw [outerClassesLiteral_eq] at hk
  simp only [outerClassesLiteral, List.mem_cons, List.not_mem_nil, or_false] at hk
  rw [outerSpikeCellsLiteral_eq] at hc
  simp only [outerSpikeCellsLiteral, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hid <;> norm_num

theorem outer_spike_blocks_cover {c : V22.V22SpikeCell} {M : ℝ}
    (hma : 0 < (c.ma : ℝ)) (hM : (c.ma : ℝ) ≤ M) :
    ∃ i : ℕ, i < 5 ∧ V22.inSpikeBlock c i M := by
  by_cases h2 : M ≤ 2 * (c.ma : ℝ)
  · refine ⟨0, by norm_num, ?_⟩
    simpa [V22.inSpikeBlock, V22.blockMultipliers] using
      (show (c.ma : ℝ) ≤ M ∧ M ≤ 2 * (c.ma : ℝ) from ⟨hM, h2⟩)
  by_cases h4 : M ≤ 4 * (c.ma : ℝ)
  · refine ⟨1, by norm_num, ?_⟩
    norm_num [V22.inSpikeBlock, V22.blockMultipliers]
    exact ⟨by linarith, h4⟩
  by_cases h8 : M ≤ 8 * (c.ma : ℝ)
  · refine ⟨2, by norm_num, ?_⟩
    norm_num [V22.inSpikeBlock, V22.blockMultipliers]
    exact ⟨by linarith, h8⟩
  by_cases h16 : M ≤ 16 * (c.ma : ℝ)
  · refine ⟨3, by norm_num, ?_⟩
    norm_num [V22.inSpikeBlock, V22.blockMultipliers]
    exact ⟨by linarith, h16⟩
  · refine ⟨4, by norm_num, ?_⟩
    norm_num [V22.inSpikeBlock, V22.blockMultipliers]
    linarith

theorem outer_block_multiplier_ge_one {i : ℕ} (hi : i < 5) :
    (1 : ℝ) ≤ (V22.blockMultipliers.getD i 0 : ℕ) := by
  interval_cases i <;> norm_num [V22.blockMultipliers]


set_option maxHeartbeats 2000000 in
/-- The complete source spike cover on each outer class, with every endpoint.
No finite deficit or coefficient certificate is inferred from this cover. -/
theorem outer_spike_cells_cover {k : V22.V22Class} (hk : k ∈ V22.classes)
    {t : ℝ} (ht0 : (21 / 100 : ℝ) ≤ t) (ht1 : t ≤ (k.tau : ℝ)) :
    ∃ c ∈ V22.spikeCells, k.classId = c.classId ∧ V22.Checks.inCell c.lo c.hi t := by
  rw [outerClassesLiteral_eq] at hk
  simp only [outerClassesLiteral, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at ht1
    by_cases h0 : t ≤ (17 / 50 : ℝ)
    · refine ⟨V22.spikeCells.getD 18 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (21 / 50 : ℝ)
    · refine ⟨V22.spikeCells.getD 19 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    refine ⟨V22.spikeCells.getD 20 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
    norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h1).le, ht1⟩
  · norm_num at ht1
    by_cases h0 : t ≤ (23 / 50 : ℝ)
    · refine ⟨V22.spikeCells.getD 21 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (3 / 5 : ℝ)
    · refine ⟨V22.spikeCells.getD 22 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    refine ⟨V22.spikeCells.getD 23 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
    norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h1).le, ht1⟩
  · norm_num at ht1
    by_cases h0 : t ≤ (9 / 25 : ℝ)
    · refine ⟨V22.spikeCells.getD 24 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (21 / 50 : ℝ)
    · refine ⟨V22.spikeCells.getD 25 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    refine ⟨V22.spikeCells.getD 26 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
    norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h1).le, ht1⟩
  · norm_num at ht1
    by_cases h0 : t ≤ (8 / 25 : ℝ)
    · refine ⟨V22.spikeCells.getD 27 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (9 / 25 : ℝ)
    · refine ⟨V22.spikeCells.getD 28 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    by_cases h2 : t ≤ (19 / 50 : ℝ)
    · refine ⟨V22.spikeCells.getD 29 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h1).le, h2⟩
    by_cases h3 : t ≤ (2 / 5 : ℝ)
    · refine ⟨V22.spikeCells.getD 30 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h2).le, h3⟩
    refine ⟨V22.spikeCells.getD 31 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
    norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h3).le, ht1⟩
  · norm_num at ht1
    by_cases h0 : t ≤ (17 / 50 : ℝ)
    · refine ⟨V22.spikeCells.getD 32 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (19 / 50 : ℝ)
    · refine ⟨V22.spikeCells.getD 33 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    refine ⟨V22.spikeCells.getD 34 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
    norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h1).le, ht1⟩
  · norm_num at ht1
    by_cases h0 : t ≤ (3 / 10 : ℝ)
    · refine ⟨V22.spikeCells.getD 35 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (17 / 50 : ℝ)
    · refine ⟨V22.spikeCells.getD 36 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    refine ⟨V22.spikeCells.getD 37 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
    norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h1).le, ht1⟩
  · norm_num at ht1
    by_cases h0 : t ≤ (1 / 4 : ℝ)
    · refine ⟨V22.spikeCells.getD 38 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨ht0, h0⟩
    by_cases h1 : t ≤ (3 / 10 : ℝ)
    · refine ⟨V22.spikeCells.getD 39 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h0).le, h1⟩
    by_cases h2 : t ≤ (8 / 25 : ℝ)
    · refine ⟨V22.spikeCells.getD 40 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨(lt_of_not_ge h1).le, h2⟩
    refine ⟨V22.spikeCells.getD 41 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
    norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h2).le, ht1⟩
  · norm_num at ht1
    by_cases h0 : t ≤ (7 / 25 : ℝ)
    · refine ⟨V22.spikeCells.getD 42 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
      norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
      exact ⟨ht0, h0⟩
    refine ⟨V22.spikeCells.getD 43 ⟨0, 0, 0, 0, [], [], false⟩, by norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral], ?_⟩
    norm_num [outerSpikeCellsLiteral_eq, outerSpikeCellsLiteral, V22.Checks.inCell]
    exact ⟨(lt_of_not_ge h0).le, ht1⟩

end Erdos993Lean.Analytic.V22.Analysis
