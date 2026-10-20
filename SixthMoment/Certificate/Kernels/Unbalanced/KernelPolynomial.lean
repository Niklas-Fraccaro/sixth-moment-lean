import SixthMoment.Certificate.Kernels.Unbalanced.BoxPolynomial
import SixthMoment.Certificate.Kernels.Unbalanced.Kernel

namespace SixthMoment

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 500000

attribute [local irreducible] minusBoxEvenMoment

theorem boundedSimplexSlice_closed (a b c H : ℝ) :
    IsClosed (boundedSimplexSlice a b c H) := by
  unfold boundedSimplexSlice
  simp only [Set.ofPred_and]
  exact (simplexSlice_closed H).inter
    ((isClosed_le (by fun_prop) continuous_const).inter
      ((isClosed_le (by fun_prop) continuous_const).inter
        (isClosed_le (by fun_prop) continuous_const)))

theorem boundedSimplexSlice_indicator_integrable (a b c H : ℝ)
    (f : (Fin 2 → ℝ) → ℝ) (hf : Continuous f) :
    Integrable ((boundedSimplexSlice a b c H).indicator f) := by
  have hbase : IntegrableOn f (simplexSlice H) volume :=
    hf.continuousOn.integrableOn_compact (simplexSlice_compact H)
  exact (hbase.mono_set (fun _ hr => hr.1)).integrable_indicator
    (boundedSimplexSlice_closed a b c H).measurableSet

theorem minusKernelBox_eq_minusBoxIntegral (p q : Fin 5 → ℝ) (shift r s t : ℝ) :
    minusKernelBox p q shift r s t = minusBoxIntegral p q shift r s t := rfl

theorem minusKernelEvenMoment_slice_continuous (m : ℕ) (H : ℝ) :
    Continuous (fun r : Fin 2 → ℝ => minusBoxEvenMoment m (r 0) (r 1) (H - r 0 - r 1)) := by
  have hg : Continuous (fun r : Fin 2 → ℝ => (r 0, r 1, H - r 0 - r 1)) := by fun_prop
  exact (continuous_minusBoxEvenMoment m).comp hg

theorem denominatorMinusResidualKernel_polynomial (p q : Fin 5 → ℝ) (a b c d : ℝ) :
    denominatorMinusResidualKernel p q a b c d =
      ∑ m : Fin 5, minusBoxCoefficient p q (minusKernelT0 a b c d) (minusEvenIndex m) *
        ∫ r, (boundedSimplexSlice a b c (minusKernelH a b c d)).indicator
          (fun r => minusBoxEvenMoment m.val (r 0) (r 1)
            (minusKernelH a b c d - r 0 - r 1)) r := by
  classical
  let H := minusKernelH a b c d
  let shift := minusKernelT0 a b c d
  unfold denominatorMinusResidualKernel
  simp_rw [minusKernelBox_eq_minusBoxIntegral, minusBoxIntegral_polynomial]
  change (∫ r, (boundedSimplexSlice a b c H).indicator
      (fun r => ∑ m : Fin 5, minusBoxCoefficient p q shift (minusEvenIndex m) *
        minusBoxEvenMoment m.val (r 0) (r 1) (H - r 0 - r 1)) r) = _
  have he (r : Fin 2 → ℝ) : (boundedSimplexSlice a b c H).indicator
      (fun r => ∑ m : Fin 5, minusBoxCoefficient p q shift (minusEvenIndex m) *
        minusBoxEvenMoment m.val (r 0) (r 1) (H - r 0 - r 1)) r =
      ∑ m : Fin 5, minusBoxCoefficient p q shift (minusEvenIndex m) *
        (boundedSimplexSlice a b c H).indicator
          (fun r => minusBoxEvenMoment m.val (r 0) (r 1) (H - r 0 - r 1)) r := by
    by_cases hr : r ∈ boundedSimplexSlice a b c H <;> simp [hr]
  simp_rw [he]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
    rfl
  · intro m _
    exact (boundedSimplexSlice_indicator_integrable a b c H _
      (minusKernelEvenMoment_slice_continuous m.val H)).const_mul _

theorem denominatorMinusKernel_polynomial (p q : Fin 5 → ℝ) (a b c d : ℝ) :
    denominatorMinusKernel p q a b c d =
      ∑ m : Fin 5, minusBoxCoefficient p q (minusKernelT0 a b c d) (minusEvenIndex m) *
        ∫ r, (boundedSimplexSlice a b c (minusKernelH a b c d)).indicator
          (fun r => minusBoxEvenMoment m.val (r 0) (r 1)
            (minusKernelH a b c d - r 0 - r 1)) r := by
  rw [denominatorMinusKernel_eq_residual]
  exact denominatorMinusResidualKernel_polynomial p q a b c d

end SixthMoment
