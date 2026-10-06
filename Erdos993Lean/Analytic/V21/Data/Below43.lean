import Erdos993Lean.Analytic.V21.Pieces

/-!
# Paper v2.1 Lemma 5.4: Below43, subinterval 43

The paper's activity rectangle is [3/2, 8/5], its exact mean
rectangle is [13/2, 221/16]. The 6 boxes and
2 q-slabs are checked by the existing MGF.pieceOK.
Source receipts and the full 55-row comparison: CHECKS/V21/coverage_audit.json.
Generator: CHECKS/V21/coverage_generate.py. Each source box's rational dual,
centre, cutoff and edges are copied exactly. For combined covers the one
extension index is appended to every base q-slab; all base chains survive.
-/

namespace Erdos993Lean.Analytic.V21.Data

open Erdos993Lean.Analytic.MGF

@[noinline] private def R (n : Int) (d : Nat) : Rat := mkRat n d

/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_43/box_000000.json`; sha256 `6a3eacbb08f9e028400dd384514c3d9c3ab088dcdf540fcdd788d65af10deb72`. -/
def boxBelow43_000 : MBox :=
  ⟨R (3) 5, R (8) 13, R (39) 4, R (221) 16, R (377) 32,
   R (18619581651) 1000000000000, R (-7760434779) 200000000000,
   R (574129013839792956202415033902344458620841526527) 5316911983139663491615228241121378304000000000000,
   R (3112593331) 500000000000, R (234702381) 200000000000, R (0) 1, R (1) 1,
   [R (823840007723) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 52⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_43/box_000001.json`; sha256 `b5dfa63774c97075bc9f2363bfc3f1038122a7713ffb8ecfdca830b882668603`. -/
def boxBelow43_001 : MBox :=
  ⟨R (3) 5, R (8) 13, R (247) 32, R (39) 4, R (559) 64,
   R (38993269851) 1000000000000, R (-14232703681) 200000000000,
   R (779906007917562960946372896868161545959528739761) 5316911983139663491615228241121378304000000000000,
   R (2770088091) 500000000000, R (2063166991) 1000000000000, R (0) 1, R (1) 1,
   [R (421472950513) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 40⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_43/box_000002.json`; sha256 `a68e5db55581d3e24a7d39cdf15fb1f289035c8a5829f8d772b713e86c645b19`. -/
def boxBelow43_002 : MBox :=
  ⟨R (79) 130, R (8) 13, R (429) 64, R (247) 32, R (923) 128,
   R (44138194471) 1000000000000, R (-75378967483) 1000000000000,
   R (847367583795240921350747719626644112440495212989) 5316911983139663491615228241121378304000000000000,
   R (10646634753) 1000000000000, R (1182036279) 500000000000, R (0) 1, R (1) 1,
   [R (423156827573) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 36⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_43/box_000003.json`; sha256 `56d1a7d15a1427ae2687f16a64a3f5fb9e0fe53d15d834242f5accdf80fa45e7`. -/
def boxBelow43_003 : MBox :=
  ⟨R (79) 130, R (8) 13, R (91) 16, R (429) 64, R (793) 128,
   R (13933806121) 200000000000, R (-51643889869) 500000000000,
   R (2124415410232902598791136939048553204432985169637) 10633823966279326983230456482242756608000000000000,
   R (1252824147) 200000000000, R (845580149) 250000000000, R (0) 1, R (1) 1,
   [R (865203627173) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_43/box_000004.json`; sha256 `19bc34d9cb513cb135d1ecf0c5a8987f0c683945ad5455d8823ce9d2e682a3c5`. -/
def boxBelow43_004 : MBox :=
  ⟨R (3) 5, R (79) 130, R (429) 64, R (247) 32, R (923) 128,
   R (2974752563) 62500000000, R (-3250563249) 40000000000,
   R (338871440328697231947173569043942816300892634737) 2126764793255865396646091296448551321600000000000,
   R (3723640141) 500000000000, R (2452196447) 1000000000000, R (0) 1, R (1) 1,
   [R (427652734651) 500000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 36⟩
/-- Exact source `for_tong/TWIN_v2.1/supplement/bundle/F6_F7_hand_caps/subintervals_38_39_43_44_47_to_54_and_bands_24_26_to_29/outputs/stage2/mgf_hand/full/strip_43/box_000005.json`; sha256 `012d2252d054f14cc29065697495583d0259559ae5f2ae9517c5f58ee4767528`. -/
def boxBelow43_005 : MBox :=
  ⟨R (3) 5, R (79) 130, R (91) 16, R (429) 64, R (793) 128,
   R (33413175959) 500000000000, R (-51847763989) 500000000000,
   R (397668751179032435952759314406473024408563968411) 2126764793255865396646091296448551321600000000000,
   R (1264964909) 250000000000, R (388543237) 125000000000, R (0) 1, R (1) 1,
   [R (872534768607) 1000000000000, R (0) 1, R (0) 1, R (0) 1, R (0) 1], 32⟩
/-- Lemma 5.4: the exact 6 boxes of Below43. -/
def boxesBelow43 : List MBox := [
  boxBelow43_000,
  boxBelow43_001,
  boxBelow43_002,
  boxBelow43_003,
  boxBelow43_004,
  boxBelow43_005
]

/-- Lemma 5.4: the exact cover chains of Below43. -/
def slabsBelow43 : List Atlas.Slab := [
  ⟨R (3) 5, R (79) 130, [5, 4, 1, 0]⟩,
  ⟨R (79) 130, R (8) 13, [3, 2, 1, 0]⟩
]

/-- Lemma 5.4: the requested lower mean edge. -/
def mloBelow43 : Rat := R (13) 2

/-- Lemma 5.4: the requested upper mean edge. -/
def mhiBelow43 : Rat := R (221) 16

end Erdos993Lean.Analytic.V21.Data
