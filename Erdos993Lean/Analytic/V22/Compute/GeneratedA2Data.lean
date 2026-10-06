import Erdos993Lean.Analytic.V22.Compute.A2Checks

/-! Untrusted exact A2 partitions. Original M0=19*t(sa) is never refined.
A separate Lean evaluation and check_sound application are required. -/

namespace Erdos993Lean.Analytic.V22.Compute.GeneratedA2Data

def cell0 : List Span := [((-66 / 125 : Rat), (-373 / 1000 : Rat))]
def cell1 : List Span := [((-373 / 1000 : Rat), (-13 / 125 : Rat))]
def cell2 : List Span := [((-13 / 125 : Rat), (0 : Rat))]
def cell3 : List Span := [((0 : Rat), (31 / 200 : Rat))]
def cell4 : List Span := [((31 / 200 : Rat), (47 / 200 : Rat))]
def cell5 : List Span := [((47 / 200 : Rat), (317 / 1000 : Rat))]
def cell6 : List Span := [((317 / 1000 : Rat), (53 / 125 : Rat))]
def cell7 : List Span := [((53 / 125 : Rat), (117 / 200 : Rat))]
def cell8 : List Span := [((117 / 200 : Rat), (67 / 100 : Rat))]

def candidates (cell : Span) : List Span :=
  if cell.1 == (-66 / 125 : Rat) && cell.2 == (-373 / 1000 : Rat) then cell0 else
  if cell.1 == (-373 / 1000 : Rat) && cell.2 == (-13 / 125 : Rat) then cell1 else
  if cell.1 == (-13 / 125 : Rat) && cell.2 == (0 : Rat) then cell2 else
  if cell.1 == (0 : Rat) && cell.2 == (31 / 200 : Rat) then cell3 else
  if cell.1 == (31 / 200 : Rat) && cell.2 == (47 / 200 : Rat) then cell4 else
  if cell.1 == (47 / 200 : Rat) && cell.2 == (317 / 1000 : Rat) then cell5 else
  if cell.1 == (317 / 1000 : Rat) && cell.2 == (53 / 125 : Rat) then cell6 else
  if cell.1 == (53 / 125 : Rat) && cell.2 == (117 / 200 : Rat) then cell7 else
  if cell.1 == (117 / 200 : Rat) && cell.2 == (67 / 100 : Rat) then cell8 else
  []

def generatedCellCount : Nat := 9

def inputHashes : List (String × String) := [
  ("supplementary_code/fc_check_A.py", "5e3c41fd5f0a8a95bed79172bf88ef416659a05e83c316fad71d03db4657a29c"),
  ("scripts/v22_interval.py", "fb2d840eb5808745cec2ab574b56b2793a928f69e1d2b642469b23048b1ae400"),
  ("Compute/EarlyCoefficients.lean", "2a3ff05949c49fccb9e1c231ff22e92c6247024cb954221290c72812f59ea454"),
  ("scripts/v22_candidates_a2.py", "8827ec1bf269691fb2a895b2362e3c057c4674d821e97b0f9d72e94352b0d49e")
]

end Erdos993Lean.Analytic.V22.Compute.GeneratedA2Data
