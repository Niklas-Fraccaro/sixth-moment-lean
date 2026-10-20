import SixthMoment.Numerator.U.ConjugateOrientationTransfer
import SixthMoment.Numerator.U.HolomorphicTransfer
import SixthMoment.Numerator.U.MainTerm.MomentRegularLimit
import SixthMoment.Numerator.U.MainTerm.RegularProfileConjugateSwap


namespace SixthMoment
open Complex Real Set Filter Source Metric Polynomial
open scoped Topology ComplexConjugate
noncomputable section

set_option maxHeartbeats 2000000

private theorem smoothInteriorProfile_zero_above {a : ℝ} {f : ℝ → ℝ}
    (hf : SmoothInteriorProfile a f) : ∀ x, a<x → f x=0 := by
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  linarith [(hf.2.2 ht).2]

private theorem uBBLRShifts_mem_swapped_polydisc {z : ℂ}
    (hz : z ∈ closedBall (0:ℂ) (1/2)) :
    uBBLRShifts z ∈ rectangularClosedPolydisc
      (twistedConjugateSwapRadii dpCauchyRadii) := by
  have hn : ‖z‖ ≤ 1/2 := by simpa only [mem_closedBall, dist_zero_right] using hz
  intro j
  fin_cases j <;> simp [uBBLRShifts, twistedConjugateSwapRadii, dpCauchyRadii]
  linarith

theorem uPolynomialNormalizedMixedGenerator_uniform_regular
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    TendstoUniformlyOn (fun T => uPolynomialNormalizedMixedGenerator T f g Φ)
      (actualCenteredNumeratorProfileGenerator a b (fun x => (f x:ℂ))
        (fun x => (g x:ℂ)) Φ) atTop (closedBall (0:ℂ) (1/2)) := by
  have hsource := normalizedTwistedFourthMoment_uniform_regular_on_polydisc
    hAFE hSource ha hab hlen f g Φ hf hg hΦ
  have hswap := normalized_twistedFourthMoment_uniform_polydisc_conjugate_swap
    dpCauchyRadii f g Φ
    (actualRegularProfileGenerator a b (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ)
    (by
      change TendstoUniformlyOn
        (fun T σ => twistedFourthMoment T (rawMomentShifts T σ) f g Φ /
          ((T:ℂ)*(Real.log T:ℂ)^9)) _ atTop _ at hsource
      exact hsource)
  have htarget (z : ℂ) : actualCenteredNumeratorProfileGenerator a b
      (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ z =
      Complex.exp (z/2)*conj (actualRegularProfileGenerator a b
        (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ
        (twistedConjugateSwapShifts (uBBLRShifts z))) := by
    calc
      _ = Complex.exp (z/2)*actualRegularProfileGenerator b a
          (fun x => (g x:ℂ)) (fun x => (f x:ℂ)) Φ (uBBLRShifts z) := by
        simpa only [uBBLRShifts] using
          actualCenteredNumeratorProfileGenerator_eq_regular_u_slice a b
            (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ
            (Complex.continuous_ofReal.comp hf.1.continuous)
            (Complex.continuous_ofReal.comp hg.1.continuous) z
      _ = _ := by
        rw [actualRegularProfileGenerator_conj_swap a b f g Φ
          hf.1.continuous hg.1.continuous (uBBLRShifts z)]
  rw [Metric.tendstoUniformlyOn_iff] at hswap ⊢
  intro ε hε
  have hpos : 0<Real.exp 1 := Real.exp_pos 1
  filter_upwards [hswap (ε/Real.exp 1) (div_pos hε hpos)] with T hT z hz
  have hh := hT (uBBLRShifts z) (uBBLRShifts_mem_swapped_polydisc hz)
  have hn : ‖z‖ ≤ 1/2 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hq : ‖z/(2:ℂ)‖ ≤ 1 := by
    rw [norm_div]
    norm_num
    linarith
  have hexp : ‖Complex.exp (z/2)‖ ≤ Real.exp 1 :=
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hq)
  rw [htarget, uPolynomialNormalizedMixedGenerator_eq_centered_twistedFourthMoment,
    dist_eq_norm]
  calc
    _ = ‖Complex.exp (z/2) *
        (conj (actualRegularProfileGenerator a b (fun x => (f x:ℂ))
          (fun x => (g x:ℂ)) Φ (twistedConjugateSwapShifts (uBBLRShifts z))) -
          twistedFourthMoment T (rawMomentShifts T (uBBLRShifts z)) g f Φ /
            ((T:ℂ)*(Real.log T:ℂ)^9))‖ := by congr 1; ring
    _ = ‖Complex.exp (z/2)‖ *
        ‖conj (actualRegularProfileGenerator a b (fun x => (f x:ℂ))
          (fun x => (g x:ℂ)) Φ (twistedConjugateSwapShifts (uBBLRShifts z))) -
          twistedFourthMoment T (rawMomentShifts T (uBBLRShifts z)) g f Φ /
            ((T:ℂ)*(Real.log T:ℂ)^9)‖ := norm_mul _ _
    _ ≤ Real.exp 1 *
        ‖conj (actualRegularProfileGenerator a b (fun x => (f x:ℂ))
          (fun x => (g x:ℂ)) Φ (twistedConjugateSwapShifts (uBBLRShifts z))) -
          twistedFourthMoment T (rawMomentShifts T (uBBLRShifts z)) g f Φ /
            ((T:ℂ)*(Real.log T:ℂ)^9)‖ :=
      mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
    _ < Real.exp 1*(ε/Real.exp 1) := by
      exact mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hh) hpos
    _ = ε := by field_simp

theorem uPolynomialNormalizedMixedGenerator_derivatives_regular_through_four
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ n ≤ 4, Tendsto (fun T => iteratedDeriv n
      (uPolynomialNormalizedMixedGenerator T f g Φ) 0) atTop
      (𝓝 (iteratedDeriv n (actualCenteredNumeratorProfileGenerator a b
        (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ) 0)) :=
  uPolynomialNormalizedMixedGenerator_derivatives_zero_through_four (1/2) (by norm_num)
    f g Φ _
    (uPolynomialNormalizedMixedGenerator_eventually_differentiableOn_disk
      (1/2) (by norm_num) a b f g Φ (smoothInteriorProfile_zero_above hf)
      (smoothInteriorProfile_zero_above hg) hΦ)
    (uPolynomialNormalizedMixedGenerator_uniform_regular hAFE hSource ha hab hlen f g Φ hf hg hΦ)

theorem uPolynomialNormalizedMixedGenerator_finiteDifferentialOperator_four_regular_limit
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (q : Fin 5 → ℂ) :
    Tendsto (fun T => finiteDifferentialOperator 4 q
      (uPolynomialNormalizedMixedGenerator T f g Φ) 0) atTop
      (𝓝 (finiteDifferentialOperator 4 q (actualCenteredNumeratorProfileGenerator a b
        (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ) 0)) :=
  holomorphic_uniform_disk_finiteDifferentialOperator_limit (1/2) (by norm_num)
    (fun T => uPolynomialNormalizedMixedGenerator T f g Φ) _
    (uPolynomialNormalizedMixedGenerator_eventually_differentiableOn_disk
      (1/2) (by norm_num) a b f g Φ (smoothInteriorProfile_zero_above hf)
      (smoothInteriorProfile_zero_above hg) hΦ)
    (uPolynomialNormalizedMixedGenerator_uniform_regular hAFE hSource ha hab hlen f g Φ hf hg hΦ)
    4 q

theorem uPolynomialRawMixedMoment_normalized_regular_limit
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput)
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (p : ℝ[X]) (hp : p.natDegree≤4) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T => uPolynomialRawMixedMoment T p f g Φ /
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 (finiteDifferentialOperator 4 (fun j => (p.coeff j.val:ℂ))
        (actualCenteredNumeratorProfileGenerator a b (fun x => (f x:ℂ))
          (fun x => (g x:ℂ)) Φ) 0)) :=
  uPolynomialRawMixedMoment_normalized_limit_of_uniform_disk_limit (1/2) (by norm_num)
    (by norm_num) a b p hp f g Φ (smoothInteriorProfile_zero_above hf)
    (smoothInteriorProfile_zero_above hg) hΦ _
    (uPolynomialNormalizedMixedGenerator_uniform_regular hAFE hSource ha hab hlen f g Φ hf hg hΦ)

end
end SixthMoment
