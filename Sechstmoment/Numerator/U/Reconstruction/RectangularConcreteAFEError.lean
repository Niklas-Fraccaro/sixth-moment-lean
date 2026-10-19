import Sechstmoment.Numerator.U.Reconstruction.ConcreteAFE
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEError

/-! The actual Gaussian pole killer's fixed-source AFE remainder stays
uniformly negligible after both unequal amplifiers and the moment integral.
Only the cited fixed-G approximate functional equation is a source input. -/

namespace Sechstmoment
open Complex Source MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology

/-- The literal dyadic weight has a uniform, nonnegative norm bound. -/
theorem rectangular_supported_weight_bounded (Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) : ∃ P : ℝ, 0 ≤ P ∧ ∀ x, ‖Φ x‖ ≤ P := by
  have hc : HasCompactSupport Φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport Φ) hΦ.2
  obtain ⟨P, hP⟩ := hc.exists_bound_of_continuous hΦ.1.continuous
  exact ⟨max P 0, le_max_right _ _, fun x => (hP x).trans (le_max_left _ _)⟩

/-- This is the actual integrated AFE discrepancy, with the actual moving
Gaussian polynomial auxiliary. The source estimate is derived from fixed
Gaussian basis inputs before applying the unequal amplifier bound. -/
theorem rectangular_concrete_AFE_integrated_uniform_bound
    (hsource : BBLRv1FixedApproximateFEInput)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      ‖rectangularAFEIntegratedError T (rawMomentShifts T σ)
        (polarPoleKiller T σ) f g Φ‖ ≤ C*T^(1+a+b-(A : ℝ)) := by
  obtain ⟨F, hF, hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨Gc, hGc, hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨P, hP, hΦb⟩ := rectangular_supported_weight_bounded Φ hΦ
  obtain ⟨C, hC, hs⟩ := polarPoleKiller_AFE_uniform_remainder hsource K hK δ hδ hρ A
  refine ⟨P*F*Gc*C, by positivity, ?_⟩
  filter_upwards [hs, eventually_gt_atTop (1 : ℝ)] with T hs hT
  intro σ hσ
  exact rectangular_AFE_integrated_error_bound hT hF hGc hP hC a b f g Φ
    (rawMomentShifts T σ) (polarPoleKiller T σ)
    (rectangular_supported_profile_zero_above f hf)
    (rectangular_supported_profile_zero_above g hg) hfb hgb hΦ hΦb (hs σ hσ)

/-- Every rectangular pair of supported profiles has a uniform `o(T)`
literal AFE error. No rectangular divisor estimate is used here. -/
theorem rectangular_concrete_AFE_integrated_uniform_negligible
    (hsource : BBLRv1FixedApproximateFEInput)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      ‖rectangularAFEIntegratedError T (rawMomentShifts T σ)
        (polarPoleKiller T σ) f g Φ‖ ≤ ε*T := by
  obtain ⟨A, hA⟩ := exists_nat_gt (a+b)
  obtain ⟨C, hC, hb⟩ := rectangular_concrete_AFE_integrated_uniform_bound
    hsource K hK δ hδ hρ a b f g Φ hf hg hΦ A
  have hp : (fun T : ℝ => C*T^(1+a+b-(A : ℝ))) =o[atTop] (fun T : ℝ => T) :=
    (rpow_isLittleO_id_of_lt_one (by linarith : 1+a+b-(A : ℝ) < 1)).const_mul_left C
  intro ε hε
  filter_upwards [hb, hp.def hε, eventually_gt_atTop (0 : ℝ)] with T hb hp hT
  intro σ hσ
  apply (hb σ hσ).trans
  simpa only [Real.norm_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hT.le _)),
    Real.norm_of_nonneg hT.le] using hp

end Sechstmoment
