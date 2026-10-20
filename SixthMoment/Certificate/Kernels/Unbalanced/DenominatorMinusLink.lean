import SixthMoment.Certificate.Kernels.Unbalanced.EvaluatorBridge
import SixthMoment.Certificate.Kernels.Unbalanced.KernelPolynomial
import SixthMoment.Certificate.Kernels.Unbalanced.MomentBridge


namespace SixthMoment
open scoped BigOperators

private theorem minus_polynomial_mask_sum (coeff : Fin 5 → ℝ)
    (value : Fin 5 → Fin 8 → ℝ) (sign h : Fin 8 → ℝ) :
    (∑ m : Fin 5, coeff m * ∑ mask : Fin 8, sign mask *
      (if h mask ≤ 0 then 0 else value m mask)) =
    ∑ mask : Fin 8, sign mask *
      (if h mask ≤ 0 then 0 else ∑ m : Fin 5, coeff m * value m mask) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mask _
  by_cases hh : h mask ≤ 0
  · simp [hh]
  · simp only [hh, ite_false]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring

theorem denominatorMinusKernel_eq_maskEvaluator (p q : Fin 5 → ℝ)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (d : ℝ) :
    denominatorMinusKernel p q a b c d =
      realMinusMaskEvaluator p q (minusKernelT0 a b c d) a b c (minusKernelH a b c d) := by
  unfold realMinusMaskEvaluator
  by_cases hH : minusKernelH a b c d ≤ 0
  · rw [ite_eq_left hH]
    exact denominatorMinusKernel_zero_of_nonpos p q a b c d (by
      unfold minusKernelH at hH
      linarith)
  · rw [ite_eq_right hH, denominatorMinusKernel_polynomial]
    simp_rw [boundedSimplexSlice_minusBoxEvenMoment_integral ha hb hc]
    rw [minus_polynomial_mask_sum]
    simp only [mul_div_assoc]

theorem denominatorMinusKernel_eq_integer (A B C D : ℕ) (p q : List ℤ) :
    denominatorMinusKernel (fun k => (Finite.coef p k.val : ℝ))
      (fun k => (Finite.coef q k.val : ℝ))
      (realEndpoint A) (realEndpoint B) (realEndpoint C) (realEndpoint D) =
      (Finite.dminus A B C D p q : ℝ) /
        ((Finite.dminusDenominator : ℝ) * (Finite.scale : ℝ)^13) := by
  rw [denominatorMinusKernel_eq_maskEvaluator _ _
    (realEndpoint_nonneg A) (realEndpoint_nonneg B) (realEndpoint_nonneg C)]
  simpa only [minusKernelT0, minusKernelH] using
    (dminus_normalized_eq_realMinusMaskEvaluator A B C D p q).symm

end SixthMoment
