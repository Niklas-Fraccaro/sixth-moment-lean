import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Sechstmoment.Certificate.Kernels.Balanced.Pieces
import Sechstmoment.Certificate.Kernels.Unbalanced.BoxPolynomial


namespace Sechstmoment
open MeasureTheory Set
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 500000

theorem innerCoefficient_continuous (p q : Fin 5 → ℝ) (k : Fin 9) :
    Continuous (fun delta : ℝ => innerCoefficient p q delta k) := by
  unfold innerCoefficient productCoefficient
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  split_ifs
  · exact (shiftedCoefficient_continuous p (-1) i).mul
      ((shiftedCoefficient_continuous q (-1) j).comp continuous_neg)
  · exact continuous_const

theorem denominatorRealInner_joint_continuous (p q : Fin 5 → ℝ) :
    Continuous (fun z : ℝ × ℝ => denominatorRealInner p q z.1 z.2) := by
  unfold denominatorRealInner
  simp_rw [denominator_inner_integral]
  have hc (k : Fin 9) : Continuous (fun z : ℝ × ℝ => innerCoefficient p q z.1 k) :=
    (innerCoefficient_continuous p q k).comp continuous_fst
  fun_prop

theorem realW6Formula_joint_continuous :
    Continuous (fun z : (Fin 4 → ℝ) × ℝ =>
      realW6Formula z.2 (z.1 0) (z.1 1) (z.1 2) (z.1 3)) := by
  unfold realW6Formula
  fun_prop

def denominatorZeroKernelExtension (p q : Fin 5 → ℝ) (z : Fin 4 → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..min (z 0 + z 1) (z 2 + z 3),
    realW6Formula t (z 0) (z 1) (z 2) (z 3) / 6 *
      denominatorRealInner p q ((z 0 + z 1 - z 2 - z 3) / 2)
        ((1 - z 0 - z 1 - z 2 - z 3 + 2 * t) / 2)

theorem denominatorZeroKernelExtension_continuous (p q : Fin 5 → ℝ) :
    Continuous (denominatorZeroKernelExtension p q) := by
  unfold denominatorZeroKernelExtension
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · change Continuous (fun z : (Fin 4 → ℝ) × ℝ =>
      realW6Formula z.2 (z.1 0) (z.1 1) (z.1 2) (z.1 3) / 6 *
        denominatorRealInner p q ((z.1 0 + z.1 1 - z.1 2 - z.1 3) / 2)
          ((1 - z.1 0 - z.1 1 - z.1 2 - z.1 3 + 2 * z.2) / 2))
    have hm : Continuous (fun z : (Fin 4 → ℝ) × ℝ =>
        (((z.1 0 + z.1 1 - z.1 2 - z.1 3) / 2),
          ((1 - z.1 0 - z.1 1 - z.1 2 - z.1 3 + 2 * z.2) / 2))) := by fun_prop
    exact (realW6Formula_joint_continuous.div_const 6).mul
      ((denominatorRealInner_joint_continuous p q).comp hm)
  · fun_prop

theorem denominatorZeroKernelExtension_eq (p q : Fin 5 → ℝ) (z : Fin 4 → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    denominatorZeroKernelExtension p q z =
      denominatorZeroKernel p q (z 0) (z 1) (z 2) (z 3) := by
  rw [denominatorZeroKernel_one_dimensional p q (hz 0) (hz 1) (hz 2) (hz 3)]
  unfold denominatorZeroKernelExtension
  apply intervalIntegral.integral_congr
  intro t ht
  have hE : 0 ≤ min (z 0 + z 1) (z 2 + z 3) :=
    le_min (add_nonneg (hz 0) (hz 1)) (add_nonneg (hz 2) (hz 3))
  rw [uIcc_of_le hE] at ht
  dsimp only
  rw [realW6_eq_formula (hz 0) (hz 1) (hz 2) (hz 3) ht.1 ht.2]

theorem denominatorZeroKernel_continuousOn_nonneg (p q : Fin 5 → ℝ) :
    ContinuousOn (fun z : Fin 4 → ℝ =>
      denominatorZeroKernel p q (z 0) (z 1) (z 2) (z 3))
      {z | ∀ i, 0 ≤ z i} := by
  apply (denominatorZeroKernelExtension_continuous p q).continuousOn.congr
  intro z hz
  exact (denominatorZeroKernelExtension_eq p q z hz).symm

end
end Sechstmoment
