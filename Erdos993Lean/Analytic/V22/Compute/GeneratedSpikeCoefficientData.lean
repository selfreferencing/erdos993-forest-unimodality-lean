import Erdos993Lean.Analytic.V22.Compute.SpikeCoefficientChecks

set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

/-! Exact coefficient candidates. Existing status-zero partitions are reused.
No upper bound or analytic deficit transport is asserted by this data. -/

namespace Erdos993Lean.Analytic.V22.Compute.GeneratedSpikeCoefficientData

open SpikeCoefficientChecks

def fallbackBlocks : List CoefficientBlock := [
  ⟨20, 0, [
    ⟨((21 / 50 : Rat), (3 / 5 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨20, 1, [
    ⟨((21 / 50 : Rat), (3 / 5 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨20, 2, [
    ⟨((21 / 50 : Rat), (3 / 5 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨30, 0, [
    ⟨((19 / 50 : Rat), (2 / 5 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨30, 1, [
    ⟨((19 / 50 : Rat), (2 / 5 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨30, 2, [
    ⟨((19 / 50 : Rat), (2 / 5 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨30, 3, [
    ⟨((19 / 50 : Rat), (2 / 5 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨30, 4, [
    ⟨((19 / 50 : Rat), (2 / 5 : Rat)), ⟨((-1762696987093 / 2199023255552 : Rat), (-1713887986265 / 2199023255552 : Rat)), ((0 : Rat), (0 : Rat)), ((-3513821994935 / 4398046511104 : Rat), (-3415145988177 / 4398046511104 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨31, 0, [
    ⟨((2 / 5 : Rat), (21 / 50 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨31, 1, [
    ⟨((2 / 5 : Rat), (21 / 50 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨31, 2, [
    ⟨((2 / 5 : Rat), (21 / 50 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨31, 3, [
    ⟨((2 / 5 : Rat), (21 / 50 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨31, 4, [
    ⟨((2 / 5 : Rat), (21 / 50 : Rat)), ⟨((-6855551945067 / 8796093022208 : Rat), (-3326788923983 / 4398046511104 : Rat)), ((0 : Rat), (0 : Rat)), ((-3415779688825 / 4398046511104 : Rat), (-6627582023685 / 8796093022208 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨33, 0, [
    ⟨((17 / 50 : Rat), (19 / 50 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨33, 1, [
    ⟨((17 / 50 : Rat), (19 / 50 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨33, 2, [
    ⟨((17 / 50 : Rat), (19 / 50 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨33, 3, [
    ⟨((17 / 50 : Rat), (19 / 50 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨33, 4, [
    ⟨((17 / 50 : Rat), (19 / 50 : Rat)), ⟨((-7418105102863 / 8796093022208 : Rat), (-7050787948365 / 8796093022208 : Rat)), ((0 : Rat), (0 : Rat)), ((-7401177747943 / 8796093022208 : Rat), (-3515051500709 / 4398046511104 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨34, 0, [
    ⟨((19 / 50 : Rat), (2 / 5 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨34, 1, [
    ⟨((19 / 50 : Rat), (2 / 5 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨34, 2, [
    ⟨((19 / 50 : Rat), (2 / 5 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨34, 3, [
    ⟨((19 / 50 : Rat), (2 / 5 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨34, 4, [
    ⟨((19 / 50 : Rat), (2 / 5 : Rat)), ⟨((-1762696987093 / 2199023255552 : Rat), (-1713887986265 / 2199023255552 : Rat)), ((0 : Rat), (0 : Rat)), ((-7032287099523 / 8796093022208 : Rat), (-3417679396425 / 4398046511104 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨36, 0, [
    ⟨((3 / 10 : Rat), (17 / 50 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨36, 1, [
    ⟨((3 / 10 : Rat), (17 / 50 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨37, 0, [
    ⟨((17 / 50 : Rat), (9 / 25 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨37, 1, [
    ⟨((17 / 50 : Rat), (9 / 25 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨37, 2, [
    ⟨((17 / 50 : Rat), (9 / 25 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨37, 3, [
    ⟨((17 / 50 : Rat), (9 / 25 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨37, 4, [
    ⟨((17 / 50 : Rat), (9 / 25 : Rat)), ⟨((-7418105102863 / 8796093022208 : Rat), (-7238552918247 / 8796093022208 : Rat)), ((0 : Rat), (0 : Rat)), ((-7401177747943 / 8796093022208 : Rat), (-7219755154129 / 8796093022208 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨39, 0, [
    ⟨((1 / 4 : Rat), (3 / 10 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨39, 1, [
    ⟨((1 / 4 : Rat), (3 / 10 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨40, 0, [
    ⟨((3 / 10 : Rat), (8 / 25 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨40, 1, [
    ⟨((3 / 10 : Rat), (8 / 25 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨40, 2, [
    ⟨((3 / 10 : Rat), (8 / 25 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨40, 3, [
    ⟨((3 / 10 : Rat), (8 / 25 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨40, 4, [
    ⟨((3 / 10 : Rat), (8 / 25 : Rat)), ⟨((-15499277510685 / 17592186044416 : Rat), (-15177413297475 / 17592186044416 : Rat)), ((0 : Rat), (0 : Rat)), ((-15469130829765 / 17592186044416 : Rat), (-7571598504945 / 8796093022208 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨41, 0, [
    ⟨((8 / 25 : Rat), (33 / 100 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨41, 1, [
    ⟨((8 / 25 : Rat), (33 / 100 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨41, 2, [
    ⟨((8 / 25 : Rat), (33 / 100 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨41, 3, [
    ⟨((8 / 25 : Rat), (33 / 100 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨41, 4, [
    ⟨((8 / 25 : Rat), (33 / 100 : Rat)), ⟨((-1897176662185 / 2199023255552 : Rat), (-7504570271107 / 8796093022208 : Rat)), ((0 : Rat), (0 : Rat)), ((-7572672314501 / 8796093022208 : Rat), (-7487563290263 / 8796093022208 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨42, 0, [
    ⟨((21 / 100 : Rat), (7 / 25 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨42, 1, [
    ⟨((21 / 100 : Rat), (7 / 25 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨43, 0, [
    ⟨((7 / 25 : Rat), (3 / 10 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨43, 1, [
    ⟨((7 / 25 : Rat), (3 / 10 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨43, 2, [
    ⟨((7 / 25 : Rat), (3 / 10 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨43, 3, [
    ⟨((7 / 25 : Rat), (3 / 10 : Rat)), ⟨((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
  ⟨43, 4, [
    ⟨((7 / 25 : Rat), (3 / 10 : Rat)), ⟨((-3950109560925 / 4398046511104 : Rat), (-7749638755335 / 8796093022208 : Rat)), ((0 : Rat), (0 : Rat)), ((-15772340859795 / 17592186044416 : Rat), (-15466966541535 / 17592186044416 : Rat)), ((0 : Rat), (0 : Rat))⟩⟩,
  ]⟩,
]

def fromRayBlock (b : GeneratedRayData.RayBlock) : CoefficientBlock :=
  ⟨b.cellIndex, b.blockIndex, b.pieces.map (fun p => ⟨p.tspan, p.brackets⟩)⟩

def allBlocks : List CoefficientBlock :=
  (GeneratedRayData.blocks.filter (fun b => b.status == 0)).map fromRayBlock ++ fallbackBlocks

def expectedFallbackKeys : List (Nat × Nat) :=
  (GeneratedRayData.blocks.filter (fun b => b.status == 1)).map (fun b => (b.cellIndex,b.blockIndex))

def fallbackCheck : Bool :=
  decide (fallbackBlocks.length = 49 ∧
    fallbackBlocks.map (fun b => (b.cellIndex,b.blockIndex)) = expectedFallbackKeys) &&
  fallbackBlocks.all (fun b => blockOK (GeneratedRayData.cell b.cellIndex) b.blockIndex b)

def check : Bool := fallbackCheck && allOK allBlocks

def inputHashes : List (String × String) := [
  ("RationalData.lean", "218dbe2d6f1f63094edfbc40e763dc4e5fb0ba92f37c42a7a9f69005b1e9ce46"),
  ("Compute/GeneratedRayData.lean", "4ea86867320a545124ccd86d3c01d2f2e1f58fa5e03414c798e99add418f7871"),
  ("Compute/RayExprs.lean", "383b6ee13e324e6d3ee699c9458bc8e6f33e7b0dea1ac1988da96d22ad290bf2"),
  ("Compute/CoefficientExprs.lean", "59df594b0f14b3eaafe2c596a60757906321b27115ffd094e56e910ba77cf151"),
  ("Compute/SpikeCoefficientChecks.lean", "03980e089a28c54f29b5b9187cd7c8a775cc38352a776bf8ec0b6b58793e6145"),
  ("scripts/v22_candidates_ray.py", "21af402b3f26ba22cf7df50b4b3ef4324012a72b80a473708c3950031a736cc9"),
  ("scripts/v22_interval.py", "fb2d840eb5808745cec2ab574b56b2793a928f69e1d2b642469b23048b1ae400"),
  ("scripts/v22_candidates_spike_coefficients.py", "4050e660ddcc8e92685d266eb59b345cdbccb16279d5e616045a6b9a6424695e"),
  ("ray_receipt", "b9b6fb36d55ca747629e8c9382f7cd1e7d7f4004045dedd2f1d6c99c3a785991"),
]

end Erdos993Lean.Analytic.V22.Compute.GeneratedSpikeCoefficientData
