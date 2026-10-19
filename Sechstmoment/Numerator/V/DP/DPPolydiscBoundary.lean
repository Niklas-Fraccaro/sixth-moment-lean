import Sechstmoment.Analysis.Complex.Polydisc
import Sechstmoment.Numerator.V.DP.DPSmoothUniform

/-! # A genuine compact separated boundary enclosing coincident DP shifts -/
namespace Sechstmoment.Source
open Complex Set Metric
open scoped Topology
noncomputable section

def dpCauchyRadii : Fin 4 → ℝ := ![1,2,4,8]

theorem dpCauchyRadii_positive : ∀ j, 0 < dpCauchyRadii j := by
  intro j
  fin_cases j <;> norm_num [dpCauchyRadii]

theorem dpCauchyRadii_injective : Function.Injective dpCauchyRadii := by
  intro j k h
  fin_cases j <;> fin_cases k <;> simp_all [dpCauchyRadii]

theorem dpCauchyBoundary_separated (σ : MomentShifts)
    (hσ : σ ∈ rectangularDistinguishedBoundary dpCauchyRadii) : DPSeparated σ := by
  intro j k h
  apply dpCauchyRadii_injective
  have hn := congrArg norm h
  have he (i : Fin 4) : ‖(![-σ 0,-σ 1,σ 2,σ 3] : Fin 4 → ℂ) i‖=‖σ i‖ := by
    fin_cases i <;> simp
  change ‖(![-σ 0,-σ 1,σ 2,σ 3] : Fin 4 → ℂ) j‖ =
    ‖(![-σ 0,-σ 1,σ 2,σ 3] : Fin 4 → ℂ) k‖ at hn
  rw [he,he,hσ j,hσ k] at hn
  exact hn

theorem dpCauchyBoundary_isCompact :
    IsCompact (rectangularDistinguishedBoundary dpCauchyRadii) := by
  have hc : IsClosed (rectangularDistinguishedBoundary dpCauchyRadii) := by
    change IsClosed {σ : MomentShifts | ∀ j, ‖σ j‖=dpCauchyRadii j}
    have he : {σ : MomentShifts | ∀ j, ‖σ j‖=dpCauchyRadii j} =
        ⋂ j : Fin 4, {σ : MomentShifts | ‖σ j‖=dpCauchyRadii j} := by
      ext σ
      simp
    rw [he]
    exact isClosed_iInter fun j => isClosed_eq (by fun_prop) continuous_const
  apply (isCompact_closedBall (0 : MomentShifts) 8).of_isClosed_subset hc
  intro σ hσ
  rw [mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)).mpr
  intro j
  rw [hσ j]
  fin_cases j <;> norm_num [dpCauchyRadii]

theorem dpCauchyPolydisc_contains_zero :
    (0 : MomentShifts) ∈ rectangularClosedPolydisc dpCauchyRadii := by
  intro j
  simpa using (dpCauchyRadii_positive j).le

theorem dpActualMoment_boundary_uniform_smoothing (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : Polynomial ℝ)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ σ ∈ rectangularDistinguishedBoundary dpCauchyRadii,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → (∀ x, |deriv Φ x| ≤ B) →
      ‖chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ-
        (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpLeadingDensity T η P σ‖ ≤
          C*T*(Real.log T)^8 :=
  dpActualMoment_uniform_smoothing hsource η hη hηu P
    (rectangularDistinguishedBoundary dpCauchyRadii) dpCauchyBoundary_isCompact
    dpCauchyBoundary_separated B hB

end
end Sechstmoment.Source
