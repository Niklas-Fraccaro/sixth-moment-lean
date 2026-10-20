import SixthMoment.Denominator.Unbalanced.ActualMomentRegularity
import SixthMoment.Denominator.Unbalanced.Expansion.Regularity
import SixthMoment.Denominator.Unbalanced.MomentComparison

namespace SixthMoment
open Complex Real Filter Set MeasureTheory
open scoped Topology BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem d04UnbalancedMomentError_eventually_eq_difference
    (R : ℝ) (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (hρs : ∀ i, tsupport (ρ i) ⊆ Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : Fin 2 → ℂ, (∀ i, ‖σ i‖ ≤ R) →
      d04UnbalancedMomentError T σ ρ Φ =
        d04UnbalancedShiftedMoment T σ ρ Φ-d04OneSidedShiftedMoment T σ ρ Φ := by
  filter_upwards [d04UnbalancedShiftedIntegrand_eventually_integrable_on_shiftBox
    R ρ a hρs Φ hΦ hΦs,
    d04OneSidedShiftedIntegrand_eventually_integrable_on_shiftBox R ρ a hρs Φ hΦ hΦs]
    with T hActual hModel
  intro σ hσ
  unfold d04UnbalancedMomentError d04UnbalancedShiftedMoment d04OneSidedShiftedMoment
  rw [← integral_sub (hActual σ hσ) (hModel σ hσ)]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold d04ActualUnbalancedPair
  ring

theorem d04UnbalancedShiftedMoment_normalized_tendsto
    (a : Fin 4 → ℝ) (ha : ∀ i, 0 < a i) (haS : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i, Continuous (ρ i))
    (hρs : ∀ i, tsupport (ρ i) ⊆ Icc 0 (a i))
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (σ : Fin 2 → ℂ) :
    Tendsto (fun T : ℝ => d04UnbalancedShiftedMoment T σ ρ Φ/
      (T*(Real.log T)^9 : ℂ)) atTop
      (𝓝 ((arithmeticFactor : ℂ)*(∫ y : ℝ, Φ y : ℂ)*d04UnbalancedShiftedEdgeIntegral ρ σ)) := by
  let R : ℝ := ‖σ 0‖+‖σ 1‖
  have hσ : ∀ i, ‖σ i‖≤R := by
    intro i
    fin_cases i <;> dsimp [R] <;> linarith [norm_nonneg (σ 0),norm_nonneg (σ 1)]
  have hlim := (d04UnbalancedMomentError_normalized_tendsto
    a ha haS ρ hρ hρs Φ hΦ.continuous hΦs σ).add
    (d04OneSidedShiftedMoment_normalized_tendsto a ha haS ρ hρ hρs hΦ hΦs σ)
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [d04UnbalancedMomentError_eventually_eq_difference R ρ a hρs Φ hΦ hΦs]
    with T hT
  rw [hT σ hσ]
  ring

theorem d04UnbalancedShiftedMoment_normalized_eventually_uniformly_bounded
    (a : Fin 4 → ℝ) (ha : ∀ i, 0 < a i) (haS : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i, Continuous (ρ i))
    (hρs : ∀ i, tsupport (ρ i) ⊆ Icc 0 (a i))
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : Fin 2 → ℂ, (∀ i, ‖σ i‖ ≤ R) →
        ‖d04UnbalancedShiftedMoment T σ ρ Φ/(T*(Real.log T)^9 : ℂ)‖ ≤ C := by
  obtain ⟨B,hB,hmodel⟩ := d04OneSidedShiftedMoment_normalized_eventually_uniformly_bounded
    a ha haS ρ hρ hρs hΦ hΦs hR
  refine ⟨B+1,by positivity,?_⟩
  filter_upwards [hmodel,d04UnbalancedMomentError_normalized_uniform_small
    a ha haS ρ hρ hρs Φ hΦ.continuous hΦs hR (by norm_num : (0:ℝ)<1),
    d04UnbalancedMomentError_eventually_eq_difference R ρ a hρs Φ hΦ hΦs]
    with T hmodelT herrorT heqT
  intro σ hσ
  have heq : d04UnbalancedShiftedMoment T σ ρ Φ/(T*(Real.log T)^9 : ℂ) =
      d04UnbalancedMomentError T σ ρ Φ/(T*(Real.log T)^9 : ℂ)+
        d04OneSidedShiftedMoment T σ ρ Φ/(T*(Real.log T)^9 : ℂ) := by
    rw [heqT σ hσ]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add (herrorT σ hσ).le (hmodelT σ hσ)).trans_eq (by ring))

end
end SixthMoment
