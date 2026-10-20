import Sechstmoment.Denominator.Unbalanced.ActualMomentComparison
import Sechstmoment.Denominator.Unbalanced.CauchyKernel
import Sechstmoment.Denominator.Unbalanced.Statement

namespace Sechstmoment
open Complex Real Filter Set MeasureTheory Polynomial
open scoped Topology BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem d04UnbalancedMinusAsymptotic_closed : D04UnbalancedMinusAsymptotic := by
  intro a ha haS ρ hρ hρs Φ hΦ hΦs p q hp hq
  obtain ⟨C,_hC,hb⟩ := d04UnbalancedShiftedMoment_normalized_eventually_uniformly_bounded
    a ha haS ρ hρ hρs hΦ hΦs (R:=1) (by norm_num)
  let g : ℂ → ℂ → ℂ := fun z w => (arithmeticFactor : ℂ)*
    (∫ y : ℝ, Φ y : ℂ)*d04UnbalancedShiftedEdgeIntegral ρ ![z,w]
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ z ∈ Metric.sphere (0:ℂ) 1,
      ∀ w ∈ Metric.sphere (0:ℂ) 1,
      ‖d04UnbalancedShiftedMoment T ![z,w] ρ Φ/(T*(Real.log T)^9 : ℂ)‖ ≤ C := by
    filter_upwards [hb] with T hT
    intro z hz w hw
    apply hT ![z,w]
    intro i
    fin_cases i
    · exact (mem_sphere_zero_iff_norm.mp hz).le
    · exact (mem_sphere_zero_iff_norm.mp hw).le
  have hlim : ∀ z ∈ Metric.sphere (0:ℂ) 1, ∀ w ∈ Metric.sphere (0:ℂ) 1,
      Tendsto (fun T : ℝ => d04UnbalancedShiftedMoment T ![z,w] ρ Φ/
        (T*(Real.log T)^9 : ℂ)) atTop (𝓝 (g z w)) := by
    intro z _hz w _hw
    exact d04UnbalancedShiftedMoment_normalized_tendsto a ha haS ρ hρ hρs hΦ hΦs ![z,w]
  have ht := d04UnbalancedPolynomialMoment_tendsto_of_pointwise_shifted
    p q ρ a hρs Φ hΦ hΦs g C hbound hlim
  have hkernel : d02PolynomialCircle p (fun z => d02PolynomialCircle q (g z)) =
      ((arithmeticFactor*(∫ y : ℝ,Φ y)*
        d04UnbalancedProfileKernel (fun i => p.coeff i.val) (fun i => q.coeff i.val) ρ : ℝ) : ℂ) := by
    dsimp only [g]
    simp_rw [d02PolynomialCircle_const_mul]
    rw [d04UnbalancedCauchy_profileKernel p q hp hq ρ a hρ
      (fun i x hx => hρs i (subset_tsupport (ρ i) hx))]
    have hreal : (∫ y : ℝ, (Φ y : ℂ)) = ((∫ y : ℝ, Φ y : ℝ) : ℂ) := integral_ofReal
    rw [hreal]
    push_cast
    ring
  rw [hkernel] at ht
  exact ht

theorem d04UnbalancedPlusAsymptotic_closed : D04UnbalancedPlusAsymptotic :=
  d04UnbalancedPlusAsymptotic_of_minus d04UnbalancedMinusAsymptotic_closed

theorem d04UnbalancedDenominatorAsymptotic_closed : D04UnbalancedDenominatorAsymptotic :=
  ⟨d04UnbalancedMinusAsymptotic_closed,d04UnbalancedPlusAsymptotic_closed⟩

end
end Sechstmoment
