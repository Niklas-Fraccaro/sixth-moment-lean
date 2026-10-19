import Sechstmoment.Numerator.V.DP.CenteringRemainder
import Sechstmoment.Numerator.V.DP.DPCoincidentTransfer

/-! The actual all-positive DP moment against its genuine regular circle kernel. -/
namespace Sechstmoment.Source
open Complex MeasureTheory Set Polynomial Filter
open scoped Topology
noncomputable section

def dpAllPositiveRegularKernel (η : ℝ) (P : ℝ[X]) (σ : MomentShifts) : ℂ :=
  Complex.exp (σ 2+σ 3)*dpRegularKernel η P σ

def dpAllPositiveRegularLeadingDensity (T η : ℝ) (P : ℝ[X])
    (σ : MomentShifts) : ℂ :=
  (arithmeticFactor : ℂ)*(Real.log T : ℂ)^9*dpAllPositiveRegularKernel η P σ

theorem dpAllPositiveRegularLeadingDensity_eq_on_boundary {η : ℝ} (hη : 0 < η)
    (T : ℝ) (P : ℝ[X]) (σ : MomentShifts)
    (hσ : σ ∈ rectangularDistinguishedBoundary dpCauchyRadii) :
    dpAllPositiveRegularLeadingDensity T η P σ =
      Complex.exp (σ 2+σ 3)*dpLeadingDensity T η P σ := by
  unfold dpAllPositiveRegularLeadingDensity dpAllPositiveRegularKernel
  rw [dpRegularKernel_eq_residues_on_boundary hη P σ hσ]
  unfold dpLeadingDensity
  ring

theorem dpAllPositiveMoment_regular_boundary_bound (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ ∈ rectangularDistinguishedBoundary dpCauchyRadii,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ‖dpAllPositiveMoment T η P σ Φ-
        (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpAllPositiveRegularLeadingDensity T η P σ‖ ≤
          C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,hbound⟩ := dpAllPositiveMoment_uniform_smoothing hsource η hη hηu P
    (rectangularDistinguishedBoundary dpCauchyRadii) dpCauchyBoundary_isCompact
    dpCauchyBoundary_separated B hB
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with T hbound σ hσ Φ hΦ hseminorm
  have he : (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*
      dpAllPositiveRegularLeadingDensity T η P σ =
      Complex.exp (σ 2+σ 3)*(T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpLeadingDensity T η P σ := by
    rw [dpAllPositiveRegularLeadingDensity_eq_on_boundary hη T P σ hσ]
    ring
  rw [he]
  exact hbound σ hσ Φ hΦ hseminorm

theorem dpAllPositiveRegularKernel_differentiableOn {η : ℝ} (hη : 0 ≤ η)
    (P : ℝ[X]) :
    DifferentiableOn ℂ (dpAllPositiveRegularKernel η P)
      (rectangularClosedPolydisc dpCauchyRadii) := by
  have he : Differentiable ℂ (fun σ : MomentShifts => Complex.exp (σ 2+σ 3)) := by
    fun_prop
  exact he.differentiableOn.mul (dpRegularKernel_differentiableOn hη P)

theorem dpAllPositiveRegularLeadingDensity_differentiableOn {η : ℝ} (hη : 0 ≤ η)
    (T : ℝ) (P : ℝ[X]) :
    DifferentiableOn ℂ (dpAllPositiveRegularLeadingDensity T η P)
      (rectangularClosedPolydisc dpCauchyRadii) :=
  (dpAllPositiveRegularKernel_differentiableOn hη P).const_mul
    ((arithmeticFactor : ℂ)*(Real.log T : ℂ)^9)

theorem smoothDyadicWeight_seminorm_one_bound (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∃ B : ℝ, 0 ≤ B ∧ WeightSeminormBound 1 B Φ := by
  have hs : HasCompactSupport Φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport Φ) hΦ.2
  obtain ⟨A,hA⟩ := hs.exists_bound_of_continuous hΦ.1.continuous
  obtain ⟨D,hD,hderiv⟩ := smoothDyadicWeight_deriv_bound Φ hΦ
  refine ⟨max (max A D) 0, le_max_right _ _,?_⟩
  intro j hj x
  interval_cases j
  · rw [iteratedDeriv_zero]
    exact (hA x).trans ((le_max_left A D).trans (le_max_left (max A D) 0))
  · rw [iteratedDeriv_one,Real.norm_eq_abs]
    exact (hderiv x).trans ((le_max_right A D).trans (le_max_left (max A D) 0))

end
end Sechstmoment.Source
