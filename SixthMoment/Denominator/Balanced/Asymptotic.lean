import SixthMoment.Denominator.Balanced.ShiftedHeightAsymptotic

namespace SixthMoment
open Complex Real Polynomial MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
noncomputable section

theorem d02BalancedDenominatorAsymptotic_closed : D02BalancedDenominatorAsymptotic := by
  intro a ha hS ρ hρ hρs Φ hΦ hΦs p q hp hq
  obtain ⟨C,_hC,hbound⟩ := d02BalancedShiftedMoment_eventually_uniform_circle_bound
    a ha hS ρ hρ hρs Φ hΦ hΦs
  let K : ℂ := ((arithmeticFactor*(∫ x : ℝ,Φ x):ℝ):ℂ)
  have hlim : ∀ z∈Metric.sphere (0:ℂ) 1,∀ w∈Metric.sphere (0:ℂ) 1,
      Tendsto (fun T : ℝ => d02BalancedShiftedMoment T ![z,w] ρ Φ/(T*(Real.log T)^9:ℂ))
        atTop (𝓝 (K*d02BalancedShiftedEdgeIntegral ρ ![z,w])) := by
    intro z hz w hw
    exact d02BalancedShiftedMoment_normalized_tendsto a ha hS ρ hρ hρs Φ hΦ hΦs hz hw
  have h := d02BalancedPolynomialMoment_tendsto_of_pointwise_shifted
    p q ρ a hρs Φ hΦ hΦs
    (fun z w => K*d02BalancedShiftedEdgeIntegral ρ ![z,w]) C hbound hlim
  have he : d02PolynomialCircle p (fun z => d02PolynomialCircle q
      (fun w => K*d02BalancedShiftedEdgeIntegral ρ ![z,w]))=
      ((arithmeticFactor*(∫ x : ℝ,Φ x)*
        d02BalancedProfileKernel (fun i => p.coeff i.val) (fun i => q.coeff i.val) ρ:ℝ):ℂ) := by
    simp_rw [d02PolynomialCircle_const_mul]
    rw [d02BalancedCauchy_profileKernel p q hp hq ρ a hS hρ]
    · dsimp only [K]
      push_cast
      ring
    · intro i x hx
      exact hρs i (subset_tsupport (ρ i) hx)
  rw [he] at h
  exact h

end
end SixthMoment
