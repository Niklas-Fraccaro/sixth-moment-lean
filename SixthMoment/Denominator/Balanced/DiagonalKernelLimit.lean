import SixthMoment.Denominator.Balanced.FourProfileCutoff
import SixthMoment.Denominator.Balanced.ProfileDisintegration


namespace SixthMoment
open MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def d02BalancedLogPolynomialWeight (p q : Fin 5 → ℝ) (y : D01LogSpace) : ℂ :=
  ((evalDegreeFour p (1/2-y.1 0)*evalDegreeFour q (1/2-y.2 0) +
    evalDegreeFour p (y.2 0-1/2)*evalDegreeFour q (y.1 0-1/2) : ℝ) : ℂ)

theorem d02BalancedLogPolynomialWeight_continuous (p q : Fin 5 → ℝ) :
    Continuous (d02BalancedLogPolynomialWeight p q) := by
  unfold d02BalancedLogPolynomialWeight evalDegreeFour
  fun_prop

theorem d02BalancedSharpIntegral_eq_edgeIntegral (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) :
    (∫ x : D01EdgeSpace, d02BalancedLogPolynomialWeight p q (d01RowColumnSums x) *
      d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t : ℂ)))
        (d01RowColumnSums x) ∂volume.restrict d01NonnegativeOrthant) =
      ((∫ x : D01EdgeSpace, d02BalancedEdgeIntegrand p q ρ x : ℝ) : ℂ) := by
  rw [← integral_indicator d01NonnegativeOrthant_measurable]
  refine (integral_congr_ae ?_).trans
    (integral_ofReal (μ := volume) (𝕜 := ℂ) (f := d02BalancedEdgeIntegrand p q ρ))
  filter_upwards [] with x
  by_cases hx : x∈d01NonnegativeOrthant
  · by_cases hcut : d02ZetaLogSum (d01RowColumnSums x)≤1
    · simp only [d02ZetaLogSum] at hcut
      simp [Set.indicator_apply,d02SharpLogTest,d02SharpLogRegion,d02LogCutCoordinate,
        d02ZetaLogSum,d02BalancedEdgeIntegrand,d02BalancedEdgeCut,
        d02BalancedLogPolynomialWeight,d02BalancedEdgePolynomial,
        d02BalancedEdgeProfile,d02BalancedProfileCoordinates,d02FourProfileProduct,
        Fin.prod_univ_succ,hx,hcut]
      ring
    · simp only [d02ZetaLogSum] at hcut
      simp [Set.indicator_apply,d02SharpLogTest,d02SharpLogRegion,d02LogCutCoordinate,
        d02ZetaLogSum,d02BalancedEdgeIntegrand,d02BalancedEdgeCut,hx,hcut]
  · simp [d02BalancedEdgeIntegrand,d02BalancedEdgeCut,hx]

theorem d02BalancedSharpIntegral_eq_profileKernel (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hA : (∑ i, A i)<1) (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    (∫ x : D01EdgeSpace, d02BalancedLogPolynomialWeight p q (d01RowColumnSums x) *
      d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t : ℂ)))
        (d01RowColumnSums x) ∂volume.restrict d01NonnegativeOrthant) =
      (d02BalancedProfileKernel p q ρ : ℂ) := by
  rw [d02BalancedSharpIntegral_eq_edgeIntegral,
    d02BalancedEdgeIntegral_eq_profileKernel p q ρ A hA hρc hρcap]

theorem d02BalancedDiagonal_profileKernel_limit (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hA : (∑ i, A i)<1) (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    Tendsto (fun L : ℝ => ∫ y,
      d02BalancedLogPolynomialWeight p q y *
        d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t : ℂ))) y
          ∂d01DiagonalMeasure L) atTop
      (𝓝 ((arithmeticFactor*d02BalancedProfileKernel p q ρ : ℝ) : ℂ)) := by
  have hcap : ∀ i t, (ρ i t : ℂ)≠0 → t∈Icc 0 (A i) := by
    intro i t hn
    apply hρcap i t
    intro hz
    exact hn (by rw [hz]; simp)
  have h := d02DiagonalMeasure_four_profile_sharp_log_limit
    (fun i t => (ρ i t : ℂ)) A (d02BalancedLogPolynomialWeight p q)
    (fun i => Complex.continuous_ofReal.comp (hρc i)) hcap
    (d02BalancedLogPolynomialWeight_continuous p q)
  rw [d02BalancedSharpIntegral_eq_profileKernel p q ρ A hA hρc hρcap] at h
  simpa only [Complex.ofReal_mul] using h

theorem d02BalancedDiagonal_profileKernel_height_limit (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hA : (∑ i, A i)<1) (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    Tendsto (fun T : ℝ => ∫ y,
      d02BalancedLogPolynomialWeight p q y *
        d02SharpLogTest (d02FourProfileProduct (fun i t => (ρ i t : ℂ))) y
          ∂d01DiagonalMeasure (Real.log T)) atTop
      (𝓝 ((arithmeticFactor*d02BalancedProfileKernel p q ρ : ℝ) : ℂ)) :=
  (d02BalancedDiagonal_profileKernel_limit p q ρ A hA hρc hρcap).comp
    Real.tendsto_log_atTop

end
end SixthMoment
