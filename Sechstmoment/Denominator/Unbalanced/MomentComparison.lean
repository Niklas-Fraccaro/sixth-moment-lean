import Sechstmoment.Denominator.Balanced.NormalizedHeightBudget
import Sechstmoment.Denominator.Unbalanced.ActualPairReplacement
import Sechstmoment.Denominator.Unbalanced.Expansion.Approximation
import Sechstmoment.Denominator.Unbalanced.MomentErrorBudget

namespace Sechstmoment
open Complex Real Filter Set MeasureTheory
open scoped Topology BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def d04UnbalancedMomentError (T : ℝ) (σ : Fin 2 → ℂ)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T) : ℂ)*d04UnbalancedAmplifier T t ρ*
    (d04ActualUnbalancedPair T t σ-
      d04CenteringPurePower T t (σ 0)*d04OneSidedCenteredPair T t σ)

theorem d04ActualPair_oneSided_uniform_error {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1/4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
      ∀ σ : Fin 2 → ℂ, (∀ i, ‖σ i‖ ≤ R) →
        ‖d04ActualUnbalancedPair T t σ-
          d04CenteringPurePower T t (σ 0)*d04OneSidedCenteredPair T t σ‖ ≤
          C*T^(-1/2+2*ε) := by
  obtain ⟨K,hK,hraw⟩ := d04OneSidedExpansion_uniform_eventually_bound hR hε hε1
  exact d04ActualPair_oneSided_uniform_error_of_raw hR hε hε1 hK hraw

theorem d04UnbalancedMomentError_uniform_power_bound {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1/4)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i, Continuous (ρ i)) (hρs : ∀ i, tsupport (ρ i) ⊆ Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : Fin 2 → ℂ, (∀ i, ‖σ i‖ ≤ R) →
        ‖d04UnbalancedMomentError T σ ρ Φ‖ ≤ C*T^(1/2+2*ε+(∑ i,a i)/2) := by
  obtain ⟨K,hK,hpoint⟩ := d04ActualPair_oneSided_uniform_error hR hε hε1
  have hm : ∀ i : Fin 4, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |ρ i x| ≤ M :=
    fun i => d02Continuous_supported_norm_bound (hρ i) (hρs i)
  choose M hM hρM using hm
  obtain ⟨P,hP,hΦP⟩ := d02Continuous_supported_norm_bound hΦ hΦs
  have hcap : ∀ i x, a i < x → ρ i x=0 := by
    intro i x hx
    by_contra hn
    exact (not_le_of_gt hx) (hρs i (subset_tsupport (ρ i) hn)).2
  have hcut : ∀ x, x ∉ Icc (1:ℝ) 2 → Φ x=0 := by
    intro x hx
    by_contra hn
    exact hx (hΦs (subset_tsupport Φ hn))
  refine ⟨P*(∏ i,2*M i)*K, mul_nonneg
    (mul_nonneg hP (Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (hM i))) hK, ?_⟩
  filter_upwards [hpoint,eventually_gt_atTop (1:ℝ)] with T hpointT hT
  intro σ hσ
  have hb := d04UnbalancedMoment_uniform_window_error_bound
    (d:=-1/2+2*ε) hT hP a M hM ρ hρM hcap Φ hΦP hcut
    (fun t => d04ActualUnbalancedPair T t σ-
      d04CenteringPurePower T t (σ 0)*d04OneSidedCenteredPair T t σ)
    (fun t ht => hpointT t ht σ hσ)
  simpa only [d04UnbalancedMomentError,
    show (-1/2+2*ε)+1+(∑ i,a i)/2=1/2+2*ε+(∑ i,a i)/2 by ring] using hb

theorem d04UnbalancedMomentError_normalized_uniform_small
    (a : Fin 4 → ℝ) (ha : ∀ i, 0 < a i) (haS : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i, Continuous (ρ i))
    (hρs : ∀ i, tsupport (ρ i) ⊆ Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : Fin 2 → ℂ, (∀ i, ‖σ i‖ ≤ R) →
      ‖d04UnbalancedMomentError T σ ρ Φ/(T*(Real.log T)^9 : ℂ)‖ < η := by
  let ε : ℝ := (1-(∑ i,a i))/8
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hS0 : 0 ≤ ∑ i,a i := Finset.sum_nonneg (fun i _ => (ha i).le)
  have hε1 : ε ≤ 1/4 := by dsimp [ε]; linarith
  obtain ⟨C,_hC,hbound⟩ := d04UnbalancedMomentError_uniform_power_bound
    hR hε hε1 a ρ hρ hρs Φ hΦ hΦs
  exact d02PowerHeight_normalized_uniform_small
    (fun T σ => d04UnbalancedMomentError T σ ρ Φ) (fun σ => ∀ i, ‖σ i‖≤R)
    (by dsimp [ε]; linarith : 1/2+2*ε+(∑ i,a i)/2<1) hbound hη

theorem d04UnbalancedMomentError_normalized_tendsto
    (a : Fin 4 → ℝ) (ha : ∀ i, 0 < a i) (haS : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i, Continuous (ρ i))
    (hρs : ∀ i, tsupport (ρ i) ⊆ Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (σ : Fin 2 → ℂ) :
    Tendsto (fun T : ℝ => d04UnbalancedMomentError T σ ρ Φ/
      (T*(Real.log T)^9 : ℂ)) atTop (𝓝 0) := by
  let R : ℝ := ‖σ 0‖+‖σ 1‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hσ : ∀ i, ‖σ i‖≤R := by
    intro i
    fin_cases i <;> dsimp [R] <;> linarith [norm_nonneg (σ 0),norm_nonneg (σ 1)]
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [d04UnbalancedMomentError_normalized_uniform_small
    a ha haS ρ hρ hρs Φ hΦ hΦs hR hη] with T hT
  simpa only [dist_eq_norm,sub_zero] using hT σ hσ

end
end Sechstmoment
