import Erdos993Lean.Analytic.HandVariance.Derivatives
import Erdos993Lean.Analytic.HandVariance.Feasibility

/-!
# Activity derivatives for Appendix N.4

Source: TWIN v1.8 Appendix N.4, `tgt:lem:dmu` and `mc:lem:base`.
All derivatives retain the segment parameters and use μ=log activity.
-/

namespace Erdos993Lean.Analytic.HandVariance
open Real Reserve

/-- Source: `tgt:lem:dmu`, derivative of the leaf occupation. -/
theorem hasDerivAt_actQ_mu (mu : ℝ) :
    HasDerivAt (fun x => actQ (exp x)) (actQ (exp mu)*(1-actQ (exp mu))) mu := by
  have hd : 1+exp mu ≠ 0 := by positivity
  have h := (Real.hasDerivAt_exp mu).div
    ((hasDerivAt_const mu (1:ℝ)).add (Real.hasDerivAt_exp mu)) hd
  convert h using 1
  dsimp [actQ]
  field_simp [hd]
  ring

/-- Source: `tgt:lem:dmu`, α̇. -/
noncomputable def alphaDot (c : Band) (lam : ℝ) : ℝ :=
  c.aCoef*actQ lam*(1-actQ lam)

/-- Source: `tgt:lem:dmu`, γ̇. -/
noncomputable def gammaDot (c : Band) (lam : ℝ) : ℝ :=
  lam*(3+2*lam)/c.gDen

/-- Source: `tgt:lem:dmu`, Ȧ. -/
noncomputable def capADot (c : Band) (lam : ℝ) : ℝ :=
  (c.D-1)*actQ lam*(1-actQ lam)

/-- Source: `tgt:lem:dmu`, derivative of the actual α multiplier. -/
theorem hasDerivAt_alpha_mu (c : Band) (mu : ℝ) :
    HasDerivAt (fun x => alpha c (exp x)) (alphaDot c (exp mu)) mu := by
  convert (hasDerivAt_actQ_mu mu).const_mul (c.aCoef:ℝ) using 1
  dsimp [alphaDot]
  ring

/-- Source: `tgt:lem:dmu`, derivative of the actual γ multiplier. -/
theorem hasDerivAt_gamma_mu (c : Band) (mu : ℝ) :
    HasDerivAt (fun x => gamma c (exp x)) (gammaDot c (exp mu)) mu := by
  have h := ((Real.hasDerivAt_exp mu).mul
    ((Real.hasDerivAt_exp mu).const_add 3)).div_const (c.gDen:ℝ)
  convert h using 1
  dsimp [gammaDot]
  ring

/-- Source: `tgt:lem:dmu`, derivative of the actual A multiplier. -/
theorem hasDerivAt_capA_mu (c : Band) (mu : ℝ) :
    HasDerivAt (fun x => capA c (exp x)) (capADot c (exp mu)) mu := by
  convert ((hasDerivAt_actQ_mu mu).const_mul ((c.D:ℝ)-1)).const_add 1 using 1
  dsimp [capADot]
  ring

/-- Source: `tgt:lem:tr`, activity derivative of the parent exponential. -/
theorem hasDerivAt_parentE_mu (Y mu : ℝ) :
    HasDerivAt (fun x => parentE (exp x) Y) (-parentE (exp mu) Y) mu := by
  have h := (hasDerivAt_const mu (exp Y)).div (Real.hasDerivAt_exp mu) (exp_ne_zero mu)
  convert h using 1
  dsimp [parentE]
  field_simp
  ring

/-- Source: `tgt:lem:tr`, activity derivative of k, with its actual mass. -/
theorem hasDerivAt_parentK_mu (Y mu : ℝ) :
    HasDerivAt (fun x => parentK (exp x) Y)
      (-parentK (exp mu) Y*parentTheta (exp mu) Y) mu := by
  have hphi : lmass (exp mu) Y ≠ 0 := (Reserve.lmass_pos (exp_pos _) Y).ne'
  have h := (hasDerivAt_msg_mu Y mu).div (hasDerivAt_lmass_mu Y mu) hphi
  convert h using 1
  dsimp [parentK, parentTheta]
  field_simp
  ring

/-- Source: `tgt:lem:dmu`, ĥ dot. -/
noncomputable def hDot (c : Band) (lam Y : ℝ) : ℝ :=
  -msg lam Y*(1-msg lam Y)-gamma c lam*parentK lam Y*parentTheta lam Y+
    gammaDot c lam*parentK lam Y

/-- Source: `tgt:lem:dmu`, N dot. -/
noncomputable def nDot (c : Band) (lam Y : ℝ) : ℝ :=
  capADot c lam-hDot c lam Y-alphaDot c lam/parentK lam Y-
    alpha c lam*parentTheta lam Y/parentK lam Y

/-- Source: `tgt:lem:dmu`, L̄ dot. -/
noncomputable def lDot (c : Band) (lam Y : ℝ) : ℝ :=
  gammaDot c lam*parentE lam Y-gamma c lam*parentE lam Y-hDot c lam Y*Y

/-- Source: `tgt:lem:dmu`, Z̄ dot. -/
noncomputable def zDot (c : Band) (lam Y J : ℝ) : ℝ :=
  gammaDot c lam+J*lDot c lam Y

/-- Source: `tgt:lem:dmu`, exact derivative of ĥ. -/
theorem hasDerivAt_hHat_mu (c : Band) (Y mu : ℝ) :
    HasDerivAt (fun x => hHat c (exp x) Y) (hDot c (exp mu) Y) mu := by
  have h := ((hasDerivAt_const mu (1:ℝ)).sub (hasDerivAt_msg_mu Y mu)).add
    ((hasDerivAt_gamma_mu c mu).mul (hasDerivAt_parentK_mu Y mu))
  convert h using 1
  dsimp [hDot]
  ring

/-- Source: `tgt:lem:dmu`, exact derivative of N. -/
theorem hasDerivAt_nTerm_mu (c : Band) (Y mu : ℝ) :
    HasDerivAt (fun x => nTerm c (exp x) Y) (nDot c (exp mu) Y) mu := by
  have hk : parentK (exp mu) Y ≠ 0 := (parentK_pos (exp_pos _) _).ne'
  have h := ((hasDerivAt_capA_mu c mu).sub (hasDerivAt_hHat_mu c Y mu)).sub
    ((hasDerivAt_alpha_mu c mu).div (hasDerivAt_parentK_mu Y mu) hk)
  convert h using 1
  dsimp [nDot]
  field_simp
  ring

/-- Source: `tgt:lem:dmu`, exact derivative of L̄. -/
theorem hasDerivAt_lBar_mu (c : Band) (Y mu : ℝ) :
    HasDerivAt (fun x => lBar c (exp x) Y) (lDot c (exp mu) Y) mu := by
  have h := ((hasDerivAt_gamma_mu c mu).mul (hasDerivAt_parentE_mu Y mu)).sub
    ((hasDerivAt_hHat_mu c Y mu).mul_const Y)
  convert h using 1
  dsimp [lDot]
  ring

/-- Source: `tgt:lem:dmu`, exact derivative of Z̄ at fixed J. -/
theorem hasDerivAt_zBar_mu (c : Band) (Y J mu : ℝ) :
    HasDerivAt (fun x => zBar c (exp x) Y J) (zDot c (exp mu) Y J) mu :=
  (hasDerivAt_gamma_mu c mu).add ((hasDerivAt_lBar_mu c Y mu).const_mul J)

/-- Source: `tgt:lem:dmu`, the vertex function's signed activity derivative. -/
noncomputable def vertexADot (c : Band) (lam Y r J : ℝ) : ℝ :=
  (alphaDot c lam-alpha c lam)*parentE lam Y+nDot c lam Y/Y+alphaDot c lam*r-
    J*(2*hHat c lam Y*hDot c lam Y*zBar c lam Y J -
      (hHat c lam Y)^2*zDot c lam Y J)/(zBar c lam Y J)^2

/-- Source: `tgt:lem:dmu`, derivative used in transport of each vertex check. -/
theorem hasDerivAt_vertexA_mu (c : Band) (Y r J mu : ℝ)
    (hZ : zBar c (exp mu) Y J ≠ 0) :
    HasDerivAt (fun x => vertexA c (exp x) Y r J) (vertexADot c (exp mu) Y r J) mu := by
  have h := ((((hasDerivAt_alpha_mu c mu).mul (hasDerivAt_parentE_mu Y mu)).add
    ((hasDerivAt_nTerm_mu c Y mu).div_const Y)).add
    ((hasDerivAt_alpha_mu c mu).mul_const r)).sub
    ((((hasDerivAt_hHat_mu c Y mu).pow 2).const_mul J).div
      (hasDerivAt_zBar_mu c Y J mu) hZ)
  convert h using 1
  dsimp [vertexADot]
  ring

/-- Source: `tgt:lem:dmu`, activity derivative of the gamma-denominator function. -/
noncomputable def vertexAgammaDot (c : Band) (lam Y r J : ℝ) : ℝ :=
  (alphaDot c lam-alpha c lam)*parentE lam Y+nDot c lam Y/Y+alphaDot c lam*r-
    J*(2*hHat c lam Y*hDot c lam Y/gamma c lam -
      (hHat c lam Y)^2*gammaDot c lam/(gamma c lam)^2)

/-- Source: `tgt:lem:dmu`, derivative used in the majorant transport check. -/
theorem hasDerivAt_vertexAgamma_mu (c : Band) (Y r J mu : ℝ)
    (hgamma : gamma c (exp mu) ≠ 0) :
    HasDerivAt (fun x => vertexAgamma c (exp x) Y r J) (vertexAgammaDot c (exp mu) Y r J) mu := by
  have h := ((((hasDerivAt_alpha_mu c mu).mul (hasDerivAt_parentE_mu Y mu)).add
    ((hasDerivAt_nTerm_mu c Y mu).div_const Y)).add
    ((hasDerivAt_alpha_mu c mu).mul_const r)).sub
    ((((hasDerivAt_hHat_mu c Y mu).pow 2).const_mul J).div
      (hasDerivAt_gamma_mu c mu) hgamma)
  convert h using 1
  dsimp [vertexAgammaDot]
  field_simp
  ring

/-- Source: `mc:lem:base`, selected-leaf slack on the exact multiplier curve. -/
noncomputable def baseSlack (c : Band) (lam : ℝ) : ℝ :=
  c.D*(actQ lam)^2-alpha c lam*log (1+lam)-gamma c lam*(actQ lam)^2/log (1+lam)

/-- Source: `mc:lem:base`, explicit activity derivative of the leaf slack. -/
noncomputable def baseSlackDot (c : Band) (lam : ℝ) : ℝ :=
  2*c.D*actQ lam*(actQ lam*(1-actQ lam))-alphaDot c lam*log (1+lam)-
  alpha c lam*actQ lam-gammaDot c lam*(actQ lam)^2/log (1+lam)-
  2*gamma c lam*actQ lam*(actQ lam*(1-actQ lam))/log (1+lam)+
  gamma c lam*(actQ lam)^3/(log (1+lam))^2

/-- Source: `mc:lem:base`, log-activity derivative consumed by the 13 base checks. -/
theorem hasDerivAt_baseSlack_mu (c : Band) (mu : ℝ) :
    HasDerivAt (fun x => baseSlack c (exp x)) (baseSlackDot c (exp mu)) mu := by
  have hphi : HasDerivAt (fun x => log (1+exp x)) (actQ (exp mu)) mu := by
    simpa only [lmass_zero, msg_zero] using hasDerivAt_lmass_mu 0 mu
  have hz : log (1+exp mu) ≠ 0 := (log_pos (by linarith [exp_pos mu])).ne'
  have hq := hasDerivAt_actQ_mu mu
  have h := (((hq.pow 2).const_mul (c.D:ℝ)).sub
    ((hasDerivAt_alpha_mu c mu).mul hphi)).sub
    (((hasDerivAt_gamma_mu c mu).mul (hq.pow 2)).div hphi hz)
  convert h using 1
  dsimp [baseSlackDot]
  field_simp
  ring

end Erdos993Lean.Analytic.HandVariance
