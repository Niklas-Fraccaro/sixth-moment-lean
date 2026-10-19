import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.ExponentialBounds
import Sechstmoment.Numerator.U.Separation.Tensor.SixFourier

/-! A fixed compact smooth cutoff in the six logarithmic normalized variables.
It is identically one on the actual dyadic box and is independent of T,
frequency, shifts, block scales and the sign of the gap. -/
namespace Sechstmoment
open Complex Real Set MeasureTheory Metric
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

def a03TensorLogBump : ContDiffBump (1/2 : ℝ) :=
  ⟨1/2, 3/5, by norm_num, by norm_num⟩

def a03TensorLogCutoff (y : A03SixTensorSpace) : ℂ :=
  ∏ j : Fin 6, (a03TensorLogBump (y j) : ℂ)

def a03TensorLogCutoffBox : Set A03SixTensorSpace :=
  {y | ∀ j, y j ∈ Icc (-1/10 : ℝ) (11/10)}

theorem a03TensorLogCutoff_contDiff : ContDiff ℝ (⊤ : ℕ∞) a03TensorLogCutoff := by
  unfold a03TensorLogCutoff
  apply contDiff_prod
  intro j _
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun y : A03SixTensorSpace => y j) :=
    (EuclideanSpace.proj j : A03SixTensorSpace →L[ℝ] ℝ).contDiff
  exact Complex.ofRealCLM.contDiff.comp (a03TensorLogBump.contDiff.comp hp)

theorem a03TensorLogCutoff_one {y : A03SixTensorSpace}
    (hy : ∀ j, y j ∈ Icc (0 : ℝ) (Real.log 2)) :
    a03TensorLogCutoff y = 1 := by
  unfold a03TensorLogCutoff
  apply Finset.prod_eq_one
  intro j _
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hb : y j ∈ closedBall (1/2 : ℝ) a03TensorLogBump.rIn := by
    simp only [mem_closedBall, Real.dist_eq, a03TensorLogBump]
    apply abs_le.mpr
    constructor <;> linarith [(hy j).1, (hy j).2]
  rw [a03TensorLogBump.one_of_mem_closedBall hb]
  norm_num

theorem a03TensorLogCutoff_logPoint_one {x : Fin 6 → ℝ}
    (hx : ∀ j, x j ∈ Icc (1 : ℝ) 2) :
    a03TensorLogCutoff (a03SixTensorLogPoint x) = 1 := by
  apply a03TensorLogCutoff_one
  intro j
  exact ⟨Real.log_nonneg (hx j).1,
    Real.log_le_log (zero_lt_one.trans_le (hx j).1) (hx j).2⟩

theorem a03TensorLogCutoff_norm_le_one (y : A03SixTensorSpace) :
    ‖a03TensorLogCutoff y‖ ≤ 1 := by
  unfold a03TensorLogCutoff
  rw [norm_prod]
  calc
    _ ≤ ∏ _j : Fin 6, (1 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg a03TensorLogBump.nonneg]
      exact a03TensorLogBump.le_one
    _ = 1 := Finset.prod_const_one

theorem a03TensorLogCutoffBox_isClosed : IsClosed a03TensorLogCutoffBox := by
  have he : a03TensorLogCutoffBox =
      ⋂ j : Fin 6, (fun y : A03SixTensorSpace => y j) ⁻¹' Icc (-1/10 : ℝ) (11/10) := by
    ext y
    simp [a03TensorLogCutoffBox]
  rw [he]
  apply isClosed_iInter
  intro j
  exact isClosed_Icc.preimage (EuclideanSpace.proj j).continuous

theorem a03TensorLogCutoff_tsupport :
    tsupport a03TensorLogCutoff ⊆ a03TensorLogCutoffBox := by
  apply closure_minimal _ a03TensorLogCutoffBox_isClosed
  intro y hy j
  have hj : (a03TensorLogBump (y j) : ℂ) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hy) j (Finset.mem_univ j)
  have hr : a03TensorLogBump (y j) ≠ 0 := Complex.ofReal_ne_zero.mp hj
  have hm : y j ∈ closedBall (1/2 : ℝ) a03TensorLogBump.rOut := by
    rw [← a03TensorLogBump.tsupport_eq]
    exact subset_tsupport _ hr
  simp only [mem_closedBall, Real.dist_eq, a03TensorLogBump] at hm
  obtain ⟨hl, hu⟩ := abs_le.mp hm
  constructor <;> linarith

theorem a03TensorLogCutoffBox_norm_bound {y : A03SixTensorSpace}
    (hy : y ∈ a03TensorLogCutoffBox) : ‖y‖ ≤ 3 := by
  have hsum : ∑ j : Fin 6, (y j)^2 ≤ ∑ _j : Fin 6, (11/10 : ℝ)^2 := by
    apply Finset.sum_le_sum
    intro j _
    have hj := hy j
    have h1 : 0 ≤ 11/10 - y j := by linarith [hj.2]
    have h2 : 0 ≤ 11/10 + y j := by linarith [hj.1]
    nlinarith [mul_nonneg h1 h2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hnorm := EuclideanSpace.real_norm_sq_eq y
  nlinarith [norm_nonneg y]

theorem a03TensorLogCutoffBox_gap_linear_bound {y : A03SixTensorSpace}
    (hy : y ∈ a03TensorLogCutoffBox) :
    -(34/10 : ℝ) ≤ y 1 - y 0 - y 4 - y 5 ∧
      y 1 - y 0 - y 4 - y 5 ≤ (14/10 : ℝ) := by
  constructor <;> linarith [(hy 0).1, (hy 0).2, (hy 1).1, (hy 1).2,
    (hy 4).1, (hy 4).2, (hy 5).1, (hy 5).2]

theorem a03TensorLogCutoffBox_gap_exp_bound {y : A03SixTensorSpace}
    (hy : y ∈ a03TensorLogCutoffBox) :
    Real.exp (y 1 - y 0 - y 4 - y 5) ≤ 20 := by
  have he : Real.exp 2 ≤ 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  exact ((Real.exp_le_exp.mpr (by linarith [
    (a03TensorLogCutoffBox_gap_linear_bound hy).2])).trans he).trans (by norm_num)

theorem a03TensorLogCutoff_hasCompactSupport : HasCompactSupport a03TensorLogCutoff := by
  apply (isCompact_closedBall (0 : A03SixTensorSpace) 3).of_isClosed_subset (isClosed_tsupport a03TensorLogCutoff)
  intro y hy
  simpa only [mem_closedBall, dist_zero_right] using
    a03TensorLogCutoffBox_norm_bound (a03TensorLogCutoff_tsupport hy)

theorem a03TensorLogCutoff_derivative_bounds :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ n y,
      ‖iteratedFDeriv ℝ n a03TensorLogCutoff y‖ ≤ B n := by
  let f := a03TensorLogCutoff_hasCompactSupport.toSchwartzMap a03TensorLogCutoff_contDiff
  refine ⟨fun n => SchwartzMap.seminorm ℂ 0 n f, fun n => apply_nonneg (SchwartzMap.seminorm ℂ 0 n) f,
    ?_⟩
  intro n y
  exact f.norm_iteratedFDeriv_le_seminorm ℂ n y

end
end Sechstmoment
