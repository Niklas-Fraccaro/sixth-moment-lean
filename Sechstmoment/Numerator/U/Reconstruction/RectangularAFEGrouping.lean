import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Sechstmoment.Zeta.AFE.Four.Integrability


namespace Sechstmoment

open Complex Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical

noncomputable section

theorem rectangular_BBLR_weight_vertical_integrable (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) :
    Integrable (fun v : ℝ => ‖G (1+(v : ℂ)*I)‖) := by
  obtain ⟨C, hC, hb⟩ := hG.2.2.2 1 zero_lt_one 2
  have hc : Continuous G := continuousOn_univ.mp hG.1.continuousOn
  have hm : AEStronglyMeasurable (fun v : ℝ => ‖G (1+(v : ℂ)*I)‖) := by
    exact ((hc.comp (by fun_prop)).norm).aestronglyMeasurable
  apply (integrable_inv_one_add_sq.const_mul C).mono' hm
  filter_upwards [] with v
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have hz := hb (1+(v : ℂ)*I) (by norm_num)
  have hz' : ‖G (1+(v : ℂ)*I)‖*(1+|v|)^2 ≤ C := by
    simpa using hz
  have hden : 0 < 1+v^2 := by positivity
  rw [show C*(1+v^2)⁻¹ = C/(1+v^2) by ring]
  apply (le_div_iff₀ hden).mpr
  calc
    _ ≤ ‖G (1+(v : ℂ)*I)‖*(1+|v|)^2 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      nlinarith [abs_nonneg v, sq_abs v]
    _ ≤ C := hz'

def rectangularAFEDyadicCode (n : Fin 4 → ℕ) : Fin 4 → ℕ :=
  fun j => Nat.log 2 (n j+1)

def rectangularAFEDyadicBox (k : Fin 4 → ℕ) : Finset (Fin 4 → ℕ) :=
  Fintype.piFinset fun j => Finset.Ico (2^(k j)-1) (2^(k j+1)-1)

theorem rectangular_AFE_dyadic_mem (n k : Fin 4 → ℕ) :
    n ∈ rectangularAFEDyadicBox k ↔ rectangularAFEDyadicCode n = k := by
  rw [rectangularAFEDyadicBox, Fintype.mem_piFinset]
  constructor
  · intro hn
    funext j
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp (hn j)
    have hp : 0 < (2:ℕ)^(k j) := by positivity
    have hp' : 0 < (2:ℕ)^(k j+1) := by positivity
    have h₁ : k j ≤ Nat.log 2 (n j+1) :=
      (Nat.le_log_iff_pow_le (by norm_num) (Nat.succ_ne_zero _)).mpr (by omega)
    have h₂ : Nat.log 2 (n j+1) < k j+1 :=
      (Nat.log_lt_iff_lt_pow (by norm_num) (Nat.succ_ne_zero _)).mpr (by omega)
    dsimp [rectangularAFEDyadicCode]
    omega
  · intro hn j
    have he : Nat.log 2 (n j+1) = k j := congrFun hn j
    have h₁ : 2^(k j) ≤ n j+1 :=
      (Nat.le_log_iff_pow_le (by norm_num) (Nat.succ_ne_zero _)).mp he.ge
    have h₂ : n j+1 < 2^(k j+1) :=
      (Nat.log_lt_iff_lt_pow (by norm_num) (Nat.succ_ne_zero _)).mp (he.trans_lt (Nat.lt_succ_self _))
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem rectangular_AFE_dyadic_fiber (f : (Fin 4 → ℕ) → ℂ) (k : Fin 4 → ℕ) :
    (∑' n : rectangularAFEDyadicCode ⁻¹' {k}, f n) =
      ∑ n ∈ rectangularAFEDyadicBox k, f n := by
  have hset : rectangularAFEDyadicCode ⁻¹' {k} = (rectangularAFEDyadicBox k : Set (Fin 4 → ℕ)) := by
    ext n
    simp only [mem_preimage, mem_singleton_iff, Finset.mem_coe, rectangular_AFE_dyadic_mem]
  rw [tsum_congr_set_coe f hset]
  exact Finset.tsum_subtype _ _

theorem rectangular_AFE_dyadic_grouping (f : (Fin 4 → ℕ) → ℂ) (hf : Summable f) :
    (∑' n, f n) = ∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k, f n := by
  have h := hf.hasSum.tsum_fiberwise rectangularAFEDyadicCode
  simp_rw [rectangular_AFE_dyadic_fiber] at h
  exact h.tsum_eq.symm

theorem rectangular_actual_AFE_summable (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re) :
    Summable (bblrAFESummand G α t) := by
  exact bblrAFESummand_summable G (continuousOn_univ.mp hG.1.continuousOn)
    (rectangular_BBLR_weight_vertical_integrable G α hG) α t hα

theorem rectangular_actual_AFE_dyadic (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re) :
    bblrAFESum G α t = ∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k,
      bblrAFESummand G α t n := by
  exact rectangular_AFE_dyadic_grouping _ (rectangular_actual_AFE_summable G α hG t hα)

def rectangularPositiveQuadGap (a b : ℕ) (n : Fin 4 → ℕ) : Prop :=
  b*(n 2+1)*(n 3+1) < a*(n 0+1)*(n 1+1)

def rectangularNegativeQuadGap (a b : ℕ) (n : Fin 4 → ℕ) : Prop :=
  a*(n 0+1)*(n 1+1) < b*(n 2+1)*(n 3+1)

def rectangularAFEDiagonal (G : ℂ → ℂ) (α : MomentShifts) (a b : ℕ) (t : ℝ) : ℂ :=
  ∑' n, if diagonalQuadRelation a b n then bblrAFESummand G α t n else 0

def rectangularAFEPositive (G : ℂ → ℂ) (α : MomentShifts) (a b : ℕ) (t : ℝ) : ℂ :=
  ∑' n, if rectangularPositiveQuadGap a b n then bblrAFESummand G α t n else 0

def rectangularAFENegative (G : ℂ → ℂ) (α : MomentShifts) (a b : ℕ) (t : ℝ) : ℂ :=
  ∑' n, if rectangularNegativeQuadGap a b n then bblrAFESummand G α t n else 0

private theorem rectangular_filtered_summable (f : (Fin 4 → ℕ) → ℂ)
    (hf : Summable f) (P : (Fin 4 → ℕ) → Prop) :
    Summable (fun n => if P n then f n else 0) := by
  apply hf.norm.of_norm_bounded
  intro n
  by_cases hn : P n
  · simp [hn]
  · simp [hn]

theorem rectangular_actual_AFE_diagonal_offDiagonal (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (a b : ℕ) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re) :
    bblrAFESum G α t = rectangularAFEDiagonal G α a b t+
      rectangularAFEPositive G α a b t+rectangularAFENegative G α a b t := by
  have hs := rectangular_actual_AFE_summable G α hG t hα
  have hd := rectangular_filtered_summable _ hs (diagonalQuadRelation a b)
  have hp := rectangular_filtered_summable _ hs (rectangularPositiveQuadGap a b)
  have hn := rectangular_filtered_summable _ hs (rectangularNegativeQuadGap a b)
  unfold bblrAFESum rectangularAFEDiagonal rectangularAFEPositive rectangularAFENegative
  rw [← hd.tsum_add hp, ← (hd.add hp).tsum_add hn]
  apply tsum_congr
  intro n
  rcases lt_trichotomy (a*(n 0+1)*(n 1+1)) (b*(n 2+1)*(n 3+1)) with h | h | h
  · simp [diagonalQuadRelation, rectangularPositiveQuadGap, rectangularNegativeQuadGap,
      h, h.ne, not_lt_of_gt h]
  · simp [diagonalQuadRelation, rectangularPositiveQuadGap, rectangularNegativeQuadGap, h]
  · simp [diagonalQuadRelation, rectangularPositiveQuadGap, rectangularNegativeQuadGap,
      h, h.ne', not_lt_of_gt h]

theorem rectangular_actual_AFE_signed_dyadic (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (a b : ℕ) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re)
    (positive : Bool) :
    (if positive then rectangularAFEPositive G α a b t else rectangularAFENegative G α a b t) =
      ∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k,
        if (if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n)
          then bblrAFESummand G α t n else 0 := by
  have hs := rectangular_actual_AFE_summable G α hG t hα
  cases positive
  · exact rectangular_AFE_dyadic_grouping _
      (rectangular_filtered_summable _ hs (rectangularNegativeQuadGap a b))
  · exact rectangular_AFE_dyadic_grouping _
      (rectangular_filtered_summable _ hs (rectangularPositiveQuadGap a b))

theorem rectangular_actual_dual_AFE_dyadic (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (t : ℝ) (hα : ∀ j, |(α j).re| < 1/2) :
    bblrAFESum G (bblrSixShifts α 1) t =
      ∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k,
        bblrAFESummand G (bblrSixShifts α 1) t n := by
  apply rectangular_actual_AFE_dyadic G (bblrSixShifts α 1) hG t
  intro j
  fin_cases j <;> simp [bblrSixShifts]
  all_goals linarith [(abs_lt.mp (hα 0)).2, (abs_lt.mp (hα 1)).2,
    (abs_lt.mp (hα 2)).2, (abs_lt.mp (hα 3)).2]

end
end Sechstmoment
