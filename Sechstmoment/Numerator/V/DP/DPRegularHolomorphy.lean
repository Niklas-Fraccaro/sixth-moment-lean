import Sechstmoment.Numerator.Polar.General.Holomorphy
import Sechstmoment.Numerator.V.DP.DPRegularBoundary

/-! # Actual DP regular kernel is holomorphic on the coincident-shift polydisc -/
namespace Sechstmoment.Source
open Complex Set
noncomputable section

theorem polarSourceKnots_differentiable : Differentiable ℂ polarSourceKnots := by
  unfold polarSourceKnots
  apply differentiable_pi.mpr
  intro j
  fin_cases j
  · change Differentiable ℂ (fun σ : MomentShifts => -σ 0)
    fun_prop
  · change Differentiable ℂ (fun σ : MomentShifts => -σ 1)
    fun_prop
  · change Differentiable ℂ (fun σ : MomentShifts => σ 2)
    fun_prop
  · change Differentiable ℂ (fun σ : MomentShifts => σ 3)
    fun_prop

theorem dpCauchyPolydisc_knots_in_domain (σ : MomentShifts)
    (hσ : σ ∈ rectangularClosedPolydisc dpCauchyRadii) :
    polarSourceKnots σ ∈ polarCircleDomain 16 16 := by
  intro j
  have hn : ‖polarSourceKnots σ j‖=‖σ j‖ := by
    fin_cases j <;> simp [polarSourceKnots]
  have hr : dpCauchyRadii j ≤ (8 : ℝ) := by
    fin_cases j <;> norm_num [dpCauchyRadii]
  have h : ‖polarSourceKnots σ j‖ < (16 : ℝ) := by
    rw [hn]
    linarith [hσ j]
  exact ⟨h,h⟩

theorem dpRegularKernel_differentiableOn {η : ℝ} (hη : 0 ≤ η) (P : Polynomial ℝ) :
    DifferentiableOn ℂ (dpRegularKernel η P) (rectangularClosedPolydisc dpCauchyRadii) :=
  (polarGeneralGeneratorContour_differentiableOn η P 16 16 hη).comp
    polarSourceKnots_differentiable.differentiableOn dpCauchyPolydisc_knots_in_domain

theorem dpRegularLeadingDensity_differentiableOn {η : ℝ} (hη : 0 ≤ η)
    (T : ℝ) (P : Polynomial ℝ) :
    DifferentiableOn ℂ (dpRegularLeadingDensity T η P)
      (rectangularClosedPolydisc dpCauchyRadii) :=
  (dpRegularKernel_differentiableOn hη P).const_mul
    ((arithmeticFactor : ℂ)*(Real.log T : ℂ)^9)

end
end Sechstmoment.Source
