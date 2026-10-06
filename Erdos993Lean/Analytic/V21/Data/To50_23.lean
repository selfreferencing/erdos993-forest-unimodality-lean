import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: To50_23, subinterval 23

The paper's activity rectangle is [99/100, 1], its exact mean
rectangle is [13, 50]. The 7 boxes and
1 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_23/box_000000.json`; sha256 `4a96f28eec85d343ef98f6db1f33a323aa8df44c60dbb096c36e4e60eeaaf4fd`. -/
def boxTo50_23_000 : MBox :=
  ⟨R (99) 199, R (1) 2, R (163) 4, R (50) 1, R (363) 8,
   R (143643113) 200000000000, R (-25599451) 1000000000000,
   R (5462275420796573047603936213705451223220962815441) 680564733841876926926749214863536422912000000000000,
   R (26325001) 1000000000000, R (15542483) 1000000000000, R (199323092741) 200000000000, R (1) 1,
   [R (1307801851723947) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 376⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_23/box_000001.json`; sha256 `a5825fac8634b780eddc441618adc7455c6eddfaeec7b18c4aca5f27668c1311`. -/
def boxTo50_23_001 : MBox :=
  ⟨R (99) 199, R (1) 2, R (63) 2, R (163) 4, R (289) 8,
   R (613840889) 500000000000, R (-32508547) 1000000000000,
   R (3748048321696003309490853181892030356439001328561) 340282366920938463463374607431768211456000000000000,
   R (11395421) 250000000000, R (846021) 25000000000, R (995749944733) 1000000000000, R (1) 1,
   [R (37208125066809) 250000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 304⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_23/box_000002.json`; sha256 `0c9873e608463b2d2496b639b23cf36d203cbe9edc3876bb028645e2b85dc01b`. -/
def boxTo50_23_002 : MBox :=
  ⟨R (99) 199, R (1) 2, R (215) 8, R (63) 2, R (467) 16,
   R (986746043) 500000000000, R (5000731) 125000000000,
   R (20120345970439812453184126044228353706609892796843) 1361129467683753853853498429727072845824000000000000,
   R (21872447) 125000000000, R (62240079) 1000000000000, R (1) 1, R (997140038939) 1000000000000,
   [R (735123779681) 20000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 248⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_23/box_000003.json`; sha256 `f2944c9e729906dbba70bfa0171a090cd68072c6250d8e7801c095f6f5460e37`. -/
def boxTo50_23_003 : MBox :=
  ⟨R (99) 199, R (1) 2, R (89) 4, R (215) 8, R (393) 16,
   R (3004114039) 1000000000000, R (-4421323) 40000000000,
   R (258208872290793407093007190061697702668872902699) 13611294676837538538534984297270728458240000000000,
   R (169910237) 1000000000000, R (109406603) 1000000000000, R (993053654989) 1000000000000, R (1) 1,
   [R (9805407584911) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 208⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_23/box_000004.json`; sha256 `0b6703d183c9bdd46fc3009fcf21b3fbc419d1e801e7fc1ee43d159591ba1dd1`. -/
def boxTo50_23_004 : MBox :=
  ⟨R (99) 199, R (1) 2, R (141) 8, R (89) 4, R (319) 16,
   R (2758956461) 500000000000, R (1346711) 5000000000,
   R (4661407501443611069506043664733632382867999553033) 170141183460469231731687303715884105728000000000000,
   R (28843513) 200000000000, R (104107063) 500000000000, R (1) 1, R (247386918347) 250000000000,
   [R (1879009246547) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 168⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_23/box_000005.json`; sha256 `ec9c21f3cdb7c5556630ee8e23fdde5965444beafe2cb7e46efe476a3755a608`. -/
def boxTo50_23_005 : MBox :=
  ⟨R (99) 199, R (1) 2, R (245) 16, R (141) 8, R (527) 32,
   R (7527841597) 1000000000000, R (205776527) 250000000000,
   R (2797166405176571088800648139374686271371980856187) 85070591730234615865843651857942052864000000000000,
   R (81839797) 125000000000, R (1066083) 3125000000, R (1) 1, R (971291220179) 1000000000000,
   [R (707965081453) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 144⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_one_criterion/strips_to_50_and_conversion/outputs/stage2/mgf_one/band14_to50/strip_23/box_000006.json`; sha256 `4f51cf9f00b990e52d9da55f6f2599b7477ec2b7cc132c037f140ce6d61df4a9`. -/
def boxTo50_23_006 : MBox :=
  ⟨R (99) 199, R (1) 2, R (13) 1, R (245) 16, R (453) 32,
   R (10161242471) 1000000000000, R (7847973) 1000000000000,
   R (13441874831599355972991481441282702725591808656313) 340282366920938463463374607431768211456000000000000,
   R (115936797) 100000000000, R (240141291) 500000000000, R (499320002893) 500000000000, R (1) 1,
   [R (643688565227) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 64⟩
/-- Lemma 5.4: the exact 7 boxes of To50_23. -/
def boxesTo50_23 : List MBox := [
  boxTo50_23_000,
  boxTo50_23_001,
  boxTo50_23_002,
  boxTo50_23_003,
  boxTo50_23_004,
  boxTo50_23_005,
  boxTo50_23_006
]

/-- Lemma 5.4: the exact cover chains of To50_23. -/
def slabsTo50_23 : List Atlas.Slab := [
  ⟨R (99) 199, R (1) 2, [6, 5, 4, 3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloTo50_23 : Rat := R (13) 1

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiTo50_23 : Rat := R (50) 1

end Erdos993Lean.Analytic.V21.Data
