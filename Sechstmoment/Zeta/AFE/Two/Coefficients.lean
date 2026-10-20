import Lean.Elab.Tactic.NormCast
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Sechstmoment
open Real Set
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem d02_reciprocal_sqrt_step (n : ℕ) :
    1 / Real.sqrt (n + 1 : ℝ) ≤
      2 * (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ)) := by
  have ha : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hsA := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hsB := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  apply (div_le_iff₀ ha).2
  nlinarith [sq_nonneg (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ))]

theorem d02_reciprocal_sqrt_sum_le (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / Real.sqrt (n + 1 : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs := d02_reciprocal_sqrt_step N
    push_cast
    linarith

def d02PositiveBox {k : ℕ} (N : Fin k → ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun j => Finset.range (N j))

def d02ReciprocalSqrtWeight {k : ℕ} (q : Fin k → ℕ) : ℝ :=
  ∏ j : Fin k, 1 / Real.sqrt (q j + 1 : ℝ)

theorem d02_reciprocal_sqrt_box_mass_le {k : ℕ} (N : Fin k → ℕ) :
    (∑ q ∈ d02PositiveBox N, d02ReciprocalSqrtWeight q) ≤
      ∏ j : Fin k, 2 * Real.sqrt (N j : ℝ) := by
  unfold d02PositiveBox d02ReciprocalSqrtWeight
  rw [← Finset.prod_univ_sum (fun j : Fin k => Finset.range (N j))
    (fun (_ : Fin k) n => 1 / Real.sqrt (n + 1 : ℝ))]
  exact Finset.prod_le_prod₀
    (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
    (fun j _ => d02_reciprocal_sqrt_sum_le (N j))

theorem d02_reciprocal_sqrt_height_box_mass_le {k : ℕ} {T : ℝ} (hT : 0 < T)
    (a : Fin k → ℝ) :
    (∑ q ∈ d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊), d02ReciprocalSqrtWeight q) ≤
      2 ^ k * T ^ ((∑ j, a j) / 2) := by
  apply (d02_reciprocal_sqrt_box_mass_le _).trans
  have hcap (j : Fin k) : Real.sqrt (⌊T ^ (a j)⌋₊ : ℝ) ≤ T ^ (a j / 2) := by
    calc
      _ ≤ Real.sqrt (T ^ (a j)) :=
        Real.sqrt_le_sqrt (Nat.floor_le (Real.rpow_nonneg hT.le _))
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT.le]
        congr 1
        ring
  calc
    _ ≤ ∏ j : Fin k, 2 * T ^ (a j / 2) := by
      exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
        (fun j _ => mul_le_mul_of_nonneg_left (hcap j) (by norm_num))
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.rpow_sum_of_pos hT]
      congr 2
      rw [Finset.sum_div]

theorem d02_restricted_height_coefficient_mass_le {k : ℕ} {T F : ℝ}
    (hT : 0 < T) (hF : 0 ≤ F) (a : Fin k → ℝ)
    (s : Finset (Fin k → ℕ)) (c : (Fin k → ℕ) → ℂ)
    (hs : s ⊆ d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊))
    (hc : ∀ q ∈ s, ‖c q‖ ≤ F * d02ReciprocalSqrtWeight q) :
    (∑ q ∈ s, ‖c q‖) ≤ F * 2 ^ k * T ^ ((∑ j, a j) / 2) := by
  calc
    _ ≤ ∑ q ∈ s, F * d02ReciprocalSqrtWeight q := Finset.sum_le_sum hc
    _ = F * ∑ q ∈ s, d02ReciprocalSqrtWeight q := (Finset.mul_sum ..).symm
    _ ≤ F * ∑ q ∈ d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊), d02ReciprocalSqrtWeight q := by
      apply mul_le_mul_of_nonneg_left _ hF
      exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun q _ _ => by
        unfold d02ReciprocalSqrtWeight
        positivity)
    _ ≤ F * (2 ^ k * T ^ ((∑ j, a j) / 2)) :=
      mul_le_mul_of_nonneg_left (d02_reciprocal_sqrt_height_box_mass_le hT a) hF
    _ = _ := by ring

def d02ShiftedSqrtCoefficient {k : ℕ} (T : ℝ) (σ : Fin k → ℂ)
    (q : Fin k → ℕ) : ℂ :=
  ∏ j : Fin k, (q j + 1 : ℂ) ^ (-(1 / 2 : ℂ) - σ j / (Real.log T : ℂ))

theorem d02_shifted_sqrt_coefficient_norm_le {k : ℕ} {T R : ℝ}
    (hT : 0 < T) (hlog : 1 ≤ Real.log T) (hR : 0 ≤ R)
    (a : Fin k → ℝ) (σ : Fin k → ℂ) (hσ : ∀ j, ‖σ j‖ ≤ R)
    (q : Fin k → ℕ) (hq : q ∈ d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊)) :
    ‖d02ShiftedSqrtCoefficient T σ q‖ ≤
      Real.exp (R * ∑ j, a j) * d02ReciprocalSqrtWeight q := by
  have hL : 0 < Real.log T := zero_lt_one.trans_le hlog
  have hpoint (j : Fin k) :
      ‖(q j + 1 : ℂ) ^ (-(1 / 2 : ℂ) - σ j / (Real.log T : ℂ))‖ ≤
        Real.exp (R * a j) * (1 / Real.sqrt (q j + 1 : ℝ)) := by
    have hnp : 0 < (q j + 1 : ℝ) := by positivity
    have hn1 : (1 : ℝ) ≤ q j + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (q j)]
    have hqj : q j + 1 ≤ ⌊T ^ (a j)⌋₊ :=
      Nat.succ_le_of_lt (Finset.mem_range.1 (Fintype.mem_piFinset.1 hq j))
    have hqjR : (q j + 1 : ℝ) ≤ (⌊T ^ (a j)⌋₊ : ℝ) := by exact_mod_cast hqj
    have hcap : (q j + 1 : ℝ) ≤ T ^ (a j) :=
      hqjR.trans (Nat.floor_le (Real.rpow_nonneg hT.le _))
    have hlogcap : Real.log (q j + 1 : ℝ) ≤ a j * Real.log T := by
      have hh := Real.log_le_log hnp hcap
      rw [Real.log_rpow hT] at hh
      simpa only [mul_comm] using hh
    have hr : -(σ j).re ≤ R := by
      have hh := (Complex.abs_re_le_norm (σ j)).trans (hσ j)
      exact (neg_le_abs _).trans hh
    have he : (-(1 / 2 : ℂ) - σ j / (Real.log T : ℂ)).re ≤ R / Real.log T - 1 / 2 := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.div_ofReal_re]
      norm_num
      have hh := div_le_div_of_nonneg_right hr hL.le
      rw [neg_div] at hh
      linarith
    have hshift : (q j + 1 : ℝ) ^ (R / Real.log T) ≤ Real.exp (R * a j) := by
      rw [Real.rpow_def_of_pos hnp]
      apply Real.exp_le_exp.2
      have hh := mul_le_mul_of_nonneg_right hlogcap (div_nonneg hR hL.le)
      apply hh.trans_eq
      field_simp
    rw [show (q j + 1 : ℂ) = ((q j + 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hnp]
    calc
      _ ≤ (q j + 1 : ℝ) ^ (R / Real.log T - 1 / 2) :=
        Real.rpow_le_rpow_of_exponent_le hn1 he
      _ = (q j + 1 : ℝ) ^ (R / Real.log T) / Real.sqrt (q j + 1 : ℝ) := by
        rw [Real.rpow_sub hnp, ← Real.sqrt_eq_rpow]
      _ ≤ Real.exp (R * a j) / Real.sqrt (q j + 1 : ℝ) :=
        div_le_div_of_nonneg_right hshift (Real.sqrt_nonneg _)
      _ = _ := by ring
  unfold d02ShiftedSqrtCoefficient d02ReciprocalSqrtWeight
  rw [norm_prod]
  calc
    _ ≤ ∏ j : Fin k, Real.exp (R * a j) * (1 / Real.sqrt (q j + 1 : ℝ)) :=
      Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hpoint j)
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

theorem d02_shifted_height_coefficient_mass_le {k : ℕ} {T R F : ℝ}
    (hT : 0 < T) (hlog : 1 ≤ Real.log T) (hR : 0 ≤ R) (hF : 0 ≤ F)
    (a : Fin k → ℝ) (σ : Fin k → ℂ) (hσ : ∀ j, ‖σ j‖ ≤ R)
    (s : Finset (Fin k → ℕ)) (w : (Fin k → ℕ) → ℂ)
    (hs : s ⊆ d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊))
    (hw : ∀ q ∈ s, ‖w q‖ ≤ F) :
    (∑ q ∈ s, ‖w q * d02ShiftedSqrtCoefficient T σ q‖) ≤
      (F * Real.exp (R * ∑ j, a j)) * 2 ^ k * T ^ ((∑ j, a j) / 2) := by
  apply d02_restricted_height_coefficient_mass_le hT
    (mul_nonneg hF (Real.exp_pos _).le) a s _ hs
  intro q hq
  rw [norm_mul]
  calc
    _ ≤ F * (Real.exp (R * ∑ j, a j) * d02ReciprocalSqrtWeight q) :=
      mul_le_mul (hw q hq) (d02_shifted_sqrt_coefficient_norm_le hT hlog hR a σ hσ q (hs hq))
        (norm_nonneg _) hF
    _ = _ := by ring

end
end Sechstmoment
