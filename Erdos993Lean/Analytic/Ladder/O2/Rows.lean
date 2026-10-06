import Erdos993Lean.Analytic.O2.Final
import Erdos993Lean.Analytic.O2.Cert.Bridge
import Erdos993Lean.Analytic.Ladder.O2.Checks.R1B00
import Erdos993Lean.Analytic.Ladder.O2.Checks.R1B01
import Erdos993Lean.Analytic.Ladder.O2.Checks.R1B02
import Erdos993Lean.Analytic.Ladder.O2.Checks.R1B03
import Erdos993Lean.Analytic.Ladder.O2.Checks.R1B04
import Erdos993Lean.Analytic.Ladder.O2.Checks.R1B05
import Erdos993Lean.Analytic.Ladder.O2.Checks.R1B06
import Erdos993Lean.Analytic.Ladder.O2.Checks.R1B07
import Erdos993Lean.Analytic.Ladder.O2.Checks.R1B08
import Erdos993Lean.Analytic.Ladder.O2.Checks.R1B09
import Erdos993Lean.Analytic.Ladder.O2.Checks.R1B10
import Erdos993Lean.Analytic.Ladder.O2.Checks.R1B11
import Erdos993Lean.Analytic.Ladder.O2.Checks.R2B00
import Erdos993Lean.Analytic.Ladder.O2.Checks.R2B01
import Erdos993Lean.Analytic.Ladder.O2.Checks.R2B02
import Erdos993Lean.Analytic.Ladder.O2.Checks.R2B03
import Erdos993Lean.Analytic.Ladder.O2.Checks.R2B04
import Erdos993Lean.Analytic.Ladder.O2.Checks.R2B05
import Erdos993Lean.Analytic.Ladder.O2.Checks.R2B06
import Erdos993Lean.Analytic.Ladder.O2.Checks.R2B07
import Erdos993Lean.Analytic.Ladder.O2.Checks.R2B08
import Erdos993Lean.Analytic.Ladder.O2.Checks.R2B09
import Erdos993Lean.Analytic.Ladder.O2.Checks.R2B10
import Erdos993Lean.Analytic.Ladder.O2.Checks.R2B11
import Erdos993Lean.Analytic.Ladder.O2.Checks.R3B00
import Erdos993Lean.Analytic.Ladder.O2.Checks.R3B01
import Erdos993Lean.Analytic.Ladder.O2.Checks.R3B02
import Erdos993Lean.Analytic.Ladder.O2.Checks.R3B03
import Erdos993Lean.Analytic.Ladder.O2.Checks.R3B04
import Erdos993Lean.Analytic.Ladder.O2.Checks.R3B05
import Erdos993Lean.Analytic.Ladder.O2.Checks.R3B06
import Erdos993Lean.Analytic.Ladder.O2.Checks.R3B07
import Erdos993Lean.Analytic.Ladder.O2.Checks.R3B08
import Erdos993Lean.Analytic.Ladder.O2.Checks.R3B09
import Erdos993Lean.Analytic.Ladder.O2.Checks.R3B10
import Erdos993Lean.Analytic.Ladder.O2.Checks.R3B11

/-!
# O2 on the three O2R rows: `V ≤ (1 + θ)(1 − q) W` on `[33/20, 7/4]` (`θ = 19/20`), `[8/5, 33/20]` (`9/10`), `[39/50, 4/5]` (`13/20`)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A21.  Sources: lane R4X's `LEAN/r4x/REACH_BELOW_52.md` §5(a) (the three
O2 refits of the ladder), lane O2R's certificates (`LEAN/ladder/o2/`, `O2R_CERTIFICATE_INVENTORY.json`; the unmodified R2
tight engine, separately replayed by the byte-identical R2 checker), the referee's independent replay
(`LEAN/referee/ladder_replay/REVIEW_LADDER_REPLAY.md` §4: all three rows CONFIRMED on the full Lemma 1 domain, cover,
small-message tail and leaf endpoint; verdict ADOPTED), lane A16's O2 machinery (`O2/Defs.lean`: `BandData`, `OK`;
`O2/Main.lean`: `hardCoreVar_le_of_band`, `vrb_of_band`; `O2/Small.lean`: `smallMessageOK_of_guards`) and lane A18's
checker bridge (`O2/Cert/Bridge.lean`: `localPaymentOK_of_checks`, `leafOK_of_checks`; `Matches`, `BandFacts`).
Lane A16's 14-row list `O2.bands` is not edited: the rows are defined here and consumed row by row.

* `O2R1`, `O2R2`, `O2R3`: the rows as lane A16's `BandData` (the certificate tables, verbatim; `xmin = 2⁻¹⁶`).
* `o2rk_matches`, `o2rk_facts`, `guards_O2Rk`, `smallGuards_O2Rk`: the decidable table facts (kernel `decide`).
* `o2rk_checks`: the twelve root-box checks of each row (`Checks/RkB00.lean` … `RkB11.lean`, one `native_decide` each).
* `localPaymentOK_O2Rk`, `leafOK_O2Rk`, `smallMessageOK_O2Rk`, **`ok_O2Rk : O2Rk.OK`**.
* **`vrb_O2R1`, `vrb_O2R2`, `vrb_O2R3`**: O2 on the three rows for every forest and every maximum-weight independent set,
  in the form of `VarianceRatioBound`: `hardCoreVar F t ≤ (1 + θ)(1 − q) W`.

Trust: the 36 `native_decide` root-box checks; everything else `propext`, `Classical.choice`, `Quot.sound`.

Scalarity check: `θ = γ − 1` is the row's cap on the second moment of `δ` (through `V ≤ (1 + θ)(1 − q) W`), produced by
the actual payment ledger of lane A16 from the certified local payment and consumed by O4 on the sub-bands of the
`N = 45` and `N = 44` steps (`N45/Analytic.lean`, `N44/Analytic.lean`); the tables `u, v, s, τ, w, ℓ` are the multipliers
of the named transports of `PRO_R2`, consumed only by the cell checks.
-/

namespace Erdos993Lean.Analytic.Ladder.O2

open Erdos993Lean.Analytic.O2 Erdos993Lean.Analytic.O2.Cert Erdos993Lean.Analytic.O2.Cert.Compute

/-- The O2R row 1: `[33/20, 7/4]`, `γ = 39/20` (certificate `LEAN/ladder/o2/certs/tight_cert_O2R1.json.gz`, SHA-256 `830fdf8fe6eca019…`). -/
def O2R1 : BandData where
  lo := 33/20
  hi := 7/4
  gamma := 39/20
  xmin := 1/65536
  left :=
    { u := ![24452961/250000000, 83842967/250000000, 297246143/1000000000, 297080337/1000000000, 301959263/1000000000, 424410397/1000000000, 135661011/1000000000, 1273/100000000, 0]
      v := ![135102071/1000000000, 294868019/1000000000, 297204817/1000000000, 148573793/500000000, 276665867/1000000000, 143810563/500000000, 128020351/500000000, 25725731/100000000, 0]
      s := ![0, 2009825957/1000000000, 327416009/125000000, 900489591/500000000, 1246649909/1000000000, 270980153/500000000, 107414917/200000000, 71478223/125000000, 0]
      tau := ![0, 342840819/200000000, 2138694117/1000000000, 65828629/40000000, 1220092239/1000000000, 48710367/50000000, 1020039947/1000000000, 143703289/125000000, 50029363/1000000000]
      w := 154063983/200000000
      ell := 18713539/500000000 }
  right :=
    { u := ![24452961/250000000, 83842967/250000000, 297246143/1000000000, 297080337/1000000000, 301959263/1000000000, 424410397/1000000000, 135661011/1000000000, 1273/100000000, 0]
      v := ![135102071/1000000000, 294868019/1000000000, 297204817/1000000000, 148573793/500000000, 13842387/50000000, 296259021/1000000000, 128020351/500000000, 25725731/100000000, 0]
      s := ![0, 2009825957/1000000000, 327416009/125000000, 900489591/500000000, 1246649909/1000000000, 270980153/500000000, 107414917/200000000, 71478223/125000000, 0]
      tau := ![0, 342840819/200000000, 2138694117/1000000000, 65828629/40000000, 1220092239/1000000000, 48710367/50000000, 1020039947/1000000000, 143703289/125000000, 50029363/1000000000]
      w := 94666671/125000000
      ell := 18713539/500000000 }

/-- The O2R row 2: `[8/5, 33/20]`, `γ = 19/10` (certificate `LEAN/ladder/o2/certs/tight_cert_O2R2.json.gz`, SHA-256 `7fef9c6e6e678790…`). -/
def O2R2 : BandData where
  lo := 8/5
  hi := 33/20
  gamma := 19/10
  xmin := 1/65536
  left :=
    { u := ![9853833/100000000, 303338481/1000000000, 272127673/1000000000, 1666181/6250000, 55881861/200000000, 424719051/1000000000, 4622981/40000000, 1273/100000000, 0]
      v := ![2143073/15625000, 269609627/1000000000, 269839439/1000000000, 134364973/500000000, 263839081/1000000000, 33171847/125000000, 116740869/500000000, 3364657/12500000, 0]
      s := ![0, 1056275489/500000000, 2611949371/1000000000, 456504783/250000000, 115123143/100000000, 71068021/125000000, 110990597/200000000, 30417151/62500000, 0]
      tau := ![0, 110388183/62500000, 518778369/250000000, 1604342973/1000000000, 38385561/31250000, 1000965181/1000000000, 257279861/250000000, 1161745387/1000000000, 736489/15625000]
      w := 742836989/1000000000
      ell := 44260949/1000000000 }
  right :=
    { u := ![9853833/100000000, 303338481/1000000000, 272127673/1000000000, 1666181/6250000, 55881861/200000000, 424719051/1000000000, 4622981/40000000, 1273/100000000, 0]
      v := ![2143073/15625000, 269609627/1000000000, 269839439/1000000000, 134364973/500000000, 131971193/500000000, 269847413/1000000000, 116740869/500000000, 3364657/12500000, 0]
      s := ![0, 1056275489/500000000, 2611949371/1000000000, 456504783/250000000, 115123143/100000000, 71068021/125000000, 110990597/200000000, 30417151/62500000, 0]
      tau := ![0, 110388183/62500000, 518778369/250000000, 1604342973/1000000000, 38385561/31250000, 1000965181/1000000000, 257279861/250000000, 1161745387/1000000000, 736489/15625000]
      w := 184088039/250000000
      ell := 44260949/1000000000 }

/-- The O2R row 3: `[39/50, 4/5]`, `γ = 33/20` (certificate `LEAN/ladder/o2/certs/tight_cert_O2R3.json.gz`, SHA-256 `61225afaf1d5ec8d…`). -/
def O2R3 : BandData where
  lo := 39/50
  hi := 4/5
  gamma := 33/20
  xmin := 1/65536
  left :=
    { u := ![22923879/500000000, 191543991/1000000000, 18094419/100000000, 95916587/500000000, 3573521/20000000, 96042069/500000000, 137587371/1000000000, 0, 0]
      v := ![15313119/250000000, 177821643/1000000000, 177089089/1000000000, 172951687/1000000000, 34847273/200000000, 46071439/200000000, 230357153/1000000000, 133470793/1000000000, 0]
      s := ![0, 403631541/500000000, 1223181747/1000000000, 908524363/1000000000, 560713321/1000000000, 0, 0, 896800427/1000000000, 0]
      tau := ![2128305999/1000000000, 1210909317/1000000000, 719271403/500000000, 1201385597/1000000000, 1018057421/1000000000, 110651417/125000000, 885198057/1000000000, 1112433871/1000000000, -25061653/200000000]
      w := 1007127117/1000000000
      ell := 8720171/1000000000 }
  right :=
    { u := ![22923879/500000000, 191543991/1000000000, 18094419/100000000, 95916587/500000000, 3573521/20000000, 96042069/500000000, 137587371/1000000000, 0, 0]
      v := ![15313119/250000000, 177821643/1000000000, 177089089/1000000000, 172951687/1000000000, 34847273/200000000, 46071439/200000000, 230357153/1000000000, 133470793/1000000000, 0]
      s := ![0, 403631541/500000000, 1223181747/1000000000, 908524363/1000000000, 560713321/1000000000, 0, 0, 896800427/1000000000, 0]
      tau := ![2128305999/1000000000, 1210909317/1000000000, 719271403/500000000, 1201385597/1000000000, 1018057421/1000000000, 110651417/125000000, 885198057/1000000000, 1112433871/1000000000, -25061653/200000000]
      w := 1007127117/1000000000
      ell := 9887099/1000000000 }

/-! ### The row O2R1 -/

/-- The checker's tables of `O2R1` are the row's. -/
theorem o2r1_matches : Matches o2r1SD O2R1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `O2R1`. -/
theorem o2r1_facts : BandFacts o2r1SD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `O2R1` starts at `x = 2⁻¹⁶`. -/
theorem o2r1_xmin : O2R1.xmin = 1 / 65536 := by decide +kernel

/-- The sign guards of `O2R1`. -/
theorem guards_O2R1 : O2R1.Guards := by decide +kernel

/-- The small-message guards of `O2R1`. -/
theorem smallGuards_O2R1 : O2R1.SmallGuards := by decide +kernel

/-- The twelve root boxes of `O2R1` pass (`native_decide`, `Checks/R1B00.lean` … `R1B11.lean`). -/
theorem o2r1_checks : ∀ i < 12, checkRoot o2r1SD i (o2r1Toks.getD i "") = true := by
  intro i hi
  interval_cases i
  exacts [o2r1_b00, o2r1_b01, o2r1_b02, o2r1_b03, o2r1_b04, o2r1_b05, o2r1_b06, o2r1_b07, o2r1_b08, o2r1_b09, o2r1_b10, o2r1_b11]

/-- **The certified local payment of `O2R1`.** -/
theorem localPaymentOK_O2R1 : O2R1.LocalPaymentOK :=
  localPaymentOK_of_checks o2r1_matches o2r1_facts o2r1_xmin o2r1_checks

/-- **The leaf endpoint of `O2R1`.** -/
theorem leafOK_O2R1 : O2R1.LeafOK := leafOK_of_checks o2r1_matches o2r1_facts o2r1_checks

/-- **The small-message boundary of `O2R1`.** -/
theorem smallMessageOK_O2R1 : O2R1.SmallMessageOK :=
  BandData.smallMessageOK_of_guards guards_O2R1 smallGuards_O2R1

/-- **Everything the O2 framework needs of `O2R1`.** -/
theorem ok_O2R1 : O2R1.OK := ⟨guards_O2R1, localPaymentOK_O2R1, leafOK_O2R1, smallMessageOK_O2R1⟩

/-- **O2 on `[33/20, 7/4]` at `θ = 19/20`**: `V ≤ (1 + 19/20)(1 − q) W` for every forest, every activity of the row and every
maximum-weight independent set. -/
theorem vrb_O2R1 (F : FiniteForest) {t : ℝ} (h1 : ((33/20 : ℚ) : ℝ) ≤ t) (h2 : t ≤ ((7/4 : ℚ) : ℝ))
    {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) :
    hardCoreVar F t ≤ (1 + ((19/20 : ℚ) : ℝ)) * (1 - actQ t) * weightW F t B :=
  vrb_of_band ok_O2R1 ⟨h1, h2⟩ (by norm_num [O2R1]) hB

/-! ### The row O2R2 -/

/-- The checker's tables of `O2R2` are the row's. -/
theorem o2r2_matches : Matches o2r2SD O2R2 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `O2R2`. -/
theorem o2r2_facts : BandFacts o2r2SD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `O2R2` starts at `x = 2⁻¹⁶`. -/
theorem o2r2_xmin : O2R2.xmin = 1 / 65536 := by decide +kernel

/-- The sign guards of `O2R2`. -/
theorem guards_O2R2 : O2R2.Guards := by decide +kernel

/-- The small-message guards of `O2R2`. -/
theorem smallGuards_O2R2 : O2R2.SmallGuards := by decide +kernel

/-- The twelve root boxes of `O2R2` pass (`native_decide`, `Checks/R2B00.lean` … `R2B11.lean`). -/
theorem o2r2_checks : ∀ i < 12, checkRoot o2r2SD i (o2r2Toks.getD i "") = true := by
  intro i hi
  interval_cases i
  exacts [o2r2_b00, o2r2_b01, o2r2_b02, o2r2_b03, o2r2_b04, o2r2_b05, o2r2_b06, o2r2_b07, o2r2_b08, o2r2_b09, o2r2_b10, o2r2_b11]

/-- **The certified local payment of `O2R2`.** -/
theorem localPaymentOK_O2R2 : O2R2.LocalPaymentOK :=
  localPaymentOK_of_checks o2r2_matches o2r2_facts o2r2_xmin o2r2_checks

/-- **The leaf endpoint of `O2R2`.** -/
theorem leafOK_O2R2 : O2R2.LeafOK := leafOK_of_checks o2r2_matches o2r2_facts o2r2_checks

/-- **The small-message boundary of `O2R2`.** -/
theorem smallMessageOK_O2R2 : O2R2.SmallMessageOK :=
  BandData.smallMessageOK_of_guards guards_O2R2 smallGuards_O2R2

/-- **Everything the O2 framework needs of `O2R2`.** -/
theorem ok_O2R2 : O2R2.OK := ⟨guards_O2R2, localPaymentOK_O2R2, leafOK_O2R2, smallMessageOK_O2R2⟩

/-- **O2 on `[8/5, 33/20]` at `θ = 9/10`**: `V ≤ (1 + 9/10)(1 − q) W` for every forest, every activity of the row and every
maximum-weight independent set. -/
theorem vrb_O2R2 (F : FiniteForest) {t : ℝ} (h1 : ((8/5 : ℚ) : ℝ) ≤ t) (h2 : t ≤ ((33/20 : ℚ) : ℝ))
    {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) :
    hardCoreVar F t ≤ (1 + ((9/10 : ℚ) : ℝ)) * (1 - actQ t) * weightW F t B :=
  vrb_of_band ok_O2R2 ⟨h1, h2⟩ (by norm_num [O2R2]) hB

/-! ### The row O2R3 -/

/-- The checker's tables of `O2R3` are the row's. -/
theorem o2r3_matches : Matches o2r3SD O2R3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The range and sign facts of `O2R3`. -/
theorem o2r3_facts : BandFacts o2r3SD := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The certified cover of `O2R3` starts at `x = 2⁻¹⁶`. -/
theorem o2r3_xmin : O2R3.xmin = 1 / 65536 := by decide +kernel

/-- The sign guards of `O2R3`. -/
theorem guards_O2R3 : O2R3.Guards := by decide +kernel

/-- The small-message guards of `O2R3`. -/
theorem smallGuards_O2R3 : O2R3.SmallGuards := by decide +kernel

/-- The twelve root boxes of `O2R3` pass (`native_decide`, `Checks/R3B00.lean` … `R3B11.lean`). -/
theorem o2r3_checks : ∀ i < 12, checkRoot o2r3SD i (o2r3Toks.getD i "") = true := by
  intro i hi
  interval_cases i
  exacts [o2r3_b00, o2r3_b01, o2r3_b02, o2r3_b03, o2r3_b04, o2r3_b05, o2r3_b06, o2r3_b07, o2r3_b08, o2r3_b09, o2r3_b10, o2r3_b11]

/-- **The certified local payment of `O2R3`.** -/
theorem localPaymentOK_O2R3 : O2R3.LocalPaymentOK :=
  localPaymentOK_of_checks o2r3_matches o2r3_facts o2r3_xmin o2r3_checks

/-- **The leaf endpoint of `O2R3`.** -/
theorem leafOK_O2R3 : O2R3.LeafOK := leafOK_of_checks o2r3_matches o2r3_facts o2r3_checks

/-- **The small-message boundary of `O2R3`.** -/
theorem smallMessageOK_O2R3 : O2R3.SmallMessageOK :=
  BandData.smallMessageOK_of_guards guards_O2R3 smallGuards_O2R3

/-- **Everything the O2 framework needs of `O2R3`.** -/
theorem ok_O2R3 : O2R3.OK := ⟨guards_O2R3, localPaymentOK_O2R3, leafOK_O2R3, smallMessageOK_O2R3⟩

/-- **O2 on `[39/50, 4/5]` at `θ = 13/20`**: `V ≤ (1 + 13/20)(1 − q) W` for every forest, every activity of the row and every
maximum-weight independent set. -/
theorem vrb_O2R3 (F : FiniteForest) {t : ℝ} (h1 : ((39/50 : ℚ) : ℝ) ≤ t) (h2 : t ≤ ((4/5 : ℚ) : ℝ))
    {B : Finset (Fin F.n)} (hB : IsMaxWeight F t B) :
    hardCoreVar F t ≤ (1 + ((13/20 : ℚ) : ℝ)) * (1 - actQ t) * weightW F t B :=
  vrb_of_band ok_O2R3 ⟨h1, h2⟩ (by norm_num [O2R3]) hB

end Erdos993Lean.Analytic.Ladder.O2
