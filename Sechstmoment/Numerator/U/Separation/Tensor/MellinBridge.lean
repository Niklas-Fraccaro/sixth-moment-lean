import Sechstmoment.Numerator.U.Separation.Frequency.ActualNearKernel
import Sechstmoment.Numerator.U.Separation.Tensor.Arguments

/-! Literal AFE Mellin weights match the physical six-coordinate tensor factor.
Nonzero native arithmetic factors force the entire physical dyadic support. -/
namespace Sechstmoment
open Complex Real Source MeasureTheory Set
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

private theorem quad_argument_succ (q : QuadraticScales) (n : Fin 7 → ℕ) (i : Fin 4) :
    phaseQuadVariable n i / phaseQuadScale q i = rectangularWeightArguments q n i.succ := by
  fin_cases i <;> rfl

theorem a03_actual_base_mellin_power_factorization (q : QuadraticScales)
    (α : MomentShifts) (z : ℂ) (n : Fin 7 → ℕ) :
    phaseBaseSmoothFactor q α z n =
      (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments q n j) : ℂ)) *
        ∏ i : Fin 4, (rectangularWeightArguments q n i.succ : ℂ) ^ (-(1 / 2 + α i + z)) := by
  unfold phaseBaseSmoothFactor
  simp_rw [rectangularActualMellinBlockWeight, rectangularMellinBlockWeight, quad_argument_succ]
  rw [Finset.prod_mul_distrib,
    Fin.prod_univ_succ (fun j : Fin 5 => (rectangularSmoothBlockWeight (rectangularWeightArguments q n j) : ℂ))]
  exact (mul_assoc _ _ _).symm

theorem a03_actual_base_mellin_tensor_identity (q : QuadraticScales)
    (α : MomentShifts) (z : ℂ) (n : Fin 7 → ℕ)
    (hx : ∀ j, 0 < a03SixSourceArguments q n j) :
    phaseBaseSmoothFactor q α z n =
      (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments q n j) : ℂ)) *
        a03TensorMellinFactor α z (a03SixTensorLogPoint (a03SixSourceArguments q n)) := by
  rw [a03TensorMellinFactor_logPoint α z _ hx, a03_actual_base_mellin_power_factorization]
  rfl

theorem a03_actual_base_nonzero_smooth_product (q : QuadraticScales)
    (α : MomentShifts) (z : ℂ) (n : Fin 7 → ℕ)
    (hn : phaseBaseSmoothFactor q α z n ≠ 0) :
    (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments q n j) : ℂ)) ≠ 0 := by
  rw [a03_actual_base_mellin_power_factorization] at hn
  exact (mul_ne_zero_iff.mp hn).1

theorem a03_actual_arithmetic_nonzero_six_support (T A B H : ℝ) (f g : ℝ → ℝ)
    (α : MomentShifts) (u v : ℕ) (k n : Fin 4 → ℕ) (h : ℕ) (z : ℂ)
    (hF : a03ActualArithmeticBlockFactor T A B H f g α u v k n h z ≠ 0) :
    ∀ j, a03SixSourceArguments (phaseActualScales A B H k)
      (rectangularAFESourceTuple (u + 1) (v + 1) n h) j ∈ Icc 1 2 := by
  have hβ : phaseActualAmplifierCoefficient T g B (v + 1) ≠ 0 := by
    intro hz
    apply hF
    simp only [a03ActualArithmeticBlockFactor, hz, mul_zero, zero_mul]
  have hbase : phaseBaseSmoothFactor (phaseActualScales A B H k) α z
      (rectangularAFESourceTuple (u + 1) (v + 1) n h) ≠ 0 := by
    intro hz
    apply hF
    simp only [a03ActualArithmeticBlockFactor, hz, mul_zero]
  have hω : rectangularSmoothBlockWeight (((v + 1 : ℕ) : ℝ) / B) ≠ 0 := by
    intro hz
    apply hβ
    simp only [phaseActualAmplifierCoefficient, hz, Complex.ofReal_zero, zero_mul]
  exact a03SixSourceArguments_smooth_support _ _ hω
    (a03_actual_base_nonzero_smooth_product _ α z _ hbase)

theorem a03_actual_arithmetic_nonzero_six_positive (T A B H : ℝ) (f g : ℝ → ℝ)
    (α : MomentShifts) (u v : ℕ) (k n : Fin 4 → ℕ) (h : ℕ) (z : ℂ)
    (hF : a03ActualArithmeticBlockFactor T A B H f g α u v k n h z ≠ 0) :
    ∀ j, 0 < a03SixSourceArguments (phaseActualScales A B H k)
      (rectangularAFESourceTuple (u + 1) (v + 1) n h) j := by
  intro j
  exact zero_lt_one.trans_le (a03_actual_arithmetic_nonzero_six_support T A B H f g α u v k n h z hF j).1

end
end Sechstmoment
