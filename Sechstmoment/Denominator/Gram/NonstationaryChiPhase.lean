import Sechstmoment.Denominator.Gram.ChiFrequencyCore
import Sechstmoment.Denominator.Gram.NonstationaryIntegration

namespace Sechstmoment
open Complex Real Set MeasureTheory
open scoped ContDiff Topology
noncomputable section
set_option maxHeartbeats 1000000

def d06NonstationaryChiPhase (T ℓ : ℝ) (x : ℝ) : ℂ :=
  (criticalChi (T * x))⁻¹ * Complex.exp (((T * ℓ * x : ℝ) : ℂ) * I)

theorem d06CriticalChi_contDiffAt (t : ℝ) : ContDiffAt ℝ ∞ criticalChi t := by
  have ha : AnalyticAt ℂ zetaChi (criticalLinePoint t) :=
    zetaChi_analyticOnNhd_strip _ (by norm_num [criticalLinePoint_re])
  have hp : ContDiffAt ℝ ∞ criticalLinePoint t := by
    unfold criticalLinePoint
    exact contDiffAt_const.add (Complex.ofRealCLM.contDiff.contDiffAt.mul contDiffAt_const)
  exact (ha.contDiffAt.restrict_scalars ℝ).comp t hp

theorem d06NonstationaryChiPhase_contDiffAt (T ℓ x : ℝ) :
    ContDiffAt ℝ ∞ (d06NonstationaryChiPhase T ℓ) x := by
  unfold d06NonstationaryChiPhase
  apply ContDiffAt.mul
  · exact ((d06CriticalChi_contDiffAt (T * x)).inv (criticalChi_ne_zero _)).comp x
      (by fun_prop)
  · have hl : ContDiffAt ℝ ∞ (fun y : ℝ => T * ℓ * y) x :=
      contDiffAt_const.mul contDiffAt_id
    exact Complex.contDiff_exp.contDiffAt.comp x
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp x hl).mul contDiffAt_const)

theorem d06NonstationaryChiPhase_norm (T ℓ x : ℝ) :
    ‖d06NonstationaryChiPhase T ℓ x‖ = 1 := by
  simp [d06NonstationaryChiPhase, norm_inv, criticalChi_norm,
    Complex.norm_exp, Complex.mul_re]

theorem d06NonstationaryChiPhase_hasDerivAt (T ℓ x : ℝ) :
    HasDerivAt (d06NonstationaryChiPhase T ℓ)
      ((T : ℂ) * (I * ((ℓ + d06ChiFrequency (T * x) : ℝ) : ℂ)) *
        d06NonstationaryChiPhase T ℓ x) x := by
  have hm : HasDerivAt (fun y : ℝ => T * y) T x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul T)
  have hmp : HasDerivAt (fun y : ℝ => T * ℓ * y) (T * ℓ) x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul (T * ℓ))
  have hc := (d06CriticalChiInv_hasDerivAt (T * x)).scomp x hm
  have hp := hmp.ofReal_comp.mul_const I
  have he := hc.mul hp.cexp
  convert he using 1
  · ext y
    simp [d06NonstationaryChiPhase]
  · simp only [d06NonstationaryChiPhase, Function.comp_def, Complex.real_smul]
    push_cast
    ring

end
end Sechstmoment
