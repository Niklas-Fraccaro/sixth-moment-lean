import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace SixthMoment
open Real Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

private theorem d02_nat_log_ratio_ordered {A B : ℕ} (hB : 0 < B) (hBA : B < A) :
    1 / (2 * Real.sqrt ((A : ℝ) * (B : ℝ))) ≤
      Real.log ((A : ℝ) / (B : ℝ)) := by
  have hA : 0 < (A : ℝ) := by exact_mod_cast (hB.trans hBA)
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  have hgap : (B : ℝ) + 1 ≤ (A : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hBA
  have hroot : 0 < Real.sqrt ((A : ℝ) * (B : ℝ)) :=
    Real.sqrt_pos.2 (mul_pos hA hBr)
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hA hBr)
  have hfirst : 1 / (A : ℝ) ≤ Real.log ((A : ℝ) / (B : ℝ)) := by
    apply le_trans _ hlog
    rw [inv_div]
    apply (div_le_iff₀ hA).2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hA.ne']
    linarith
  by_cases hcomp : (A : ℝ) ≤ 2 * (B : ℝ)
  · have hcap : (A : ℝ) ≤ 2 * Real.sqrt ((A : ℝ) * (B : ℝ)) := by
      have hs := Real.sq_sqrt (mul_pos hA hBr).le
      have hh := mul_le_mul_of_nonneg_left hcomp hA.le
      nlinarith [Real.sqrt_nonneg ((A : ℝ) * (B : ℝ))]
    exact (one_div_le_one_div_of_le hA hcap).trans hfirst
  · have hr : (2 : ℝ) ≤ (A : ℝ) / (B : ℝ) :=
      (le_div_iff₀ hBr).2 (le_of_lt (lt_of_not_ge hcomp))
    have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      exact hh
    have hprod : 1 ≤ (A : ℝ) * (B : ℝ) := by
      have ha1 : (1 : ℝ) ≤ A := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (hB.trans hBA))
      have hb1 : (1 : ℝ) ≤ B := by exact_mod_cast Nat.succ_le_iff.mpr hB
      nlinarith
    have hs : (1 : ℝ) ≤ Real.sqrt ((A : ℝ) * (B : ℝ)) := Real.one_le_sqrt.2 hprod
    have hhalf : 1 / (2 * Real.sqrt ((A : ℝ) * (B : ℝ))) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    exact hhalf.trans (hlogtwo.trans (Real.log_le_log (by norm_num) hr))

theorem d02_nat_log_ratio_separation {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hne : A ≠ B) :
    1 / (2 * Real.sqrt ((A : ℝ) * (B : ℝ))) ≤
      |Real.log ((A : ℝ) / (B : ℝ))| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hb := d02_nat_log_ratio_ordered hA h
    have ha : 0 < (A : ℝ) := by exact_mod_cast hA
    have hb' : 0 < (B : ℝ) := by exact_mod_cast hB
    have he : Real.log ((B : ℝ) / (A : ℝ)) = -Real.log ((A : ℝ) / (B : ℝ)) := by
      rw [Real.log_div hb'.ne' ha.ne', Real.log_div ha.ne' hb'.ne']
      ring
    have ha' := le_abs_self (Real.log ((B : ℝ) / (A : ℝ)))
    rw [he] at hb
    rw [he, abs_neg] at ha'
    simpa only [mul_comm] using hb.trans ha'
  · exact (d02_nat_log_ratio_ordered hB h).trans (le_abs_self _)

theorem d02_product_cutoff_frequency {T p : ℝ} (hT : 0 < T)
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hne : A ≠ B)
    (hprod : (A : ℝ) * (B : ℝ) ≤ T ^ p) :
    (1 / 2 : ℝ) * T ^ (1 - p / 2) ≤
      |T * Real.log ((A : ℝ) / (B : ℝ))| := by
  have ha : 0 < (A : ℝ) := by exact_mod_cast hA
  have hb : 0 < (B : ℝ) := by exact_mod_cast hB
  have hroot : 0 < Real.sqrt ((A : ℝ) * (B : ℝ)) := Real.sqrt_pos.2 (mul_pos ha hb)
  have hcap : Real.sqrt ((A : ℝ) * (B : ℝ)) ≤ T ^ (p / 2) := by
    calc
      _ ≤ Real.sqrt (T ^ p) := Real.sqrt_le_sqrt hprod
      _ = T ^ (p / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT.le]
        congr 1
        ring
  have hbound := d02_nat_log_ratio_separation hA hB hne
  have hlower : 1 / (2 * T ^ (p / 2)) ≤
      1 / (2 * Real.sqrt ((A : ℝ) * (B : ℝ))) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hcap (by norm_num))
  have hh := mul_le_mul_of_nonneg_left (hlower.trans hbound) hT.le
  rw [abs_mul, abs_of_pos hT]
  apply le_trans _ hh
  rw [Real.rpow_sub hT, Real.rpow_one]
  have hn : T ^ (p / 2) ≠ 0 := (Real.rpow_pos_of_pos hT _).ne'
  field_simp; ring_nf; norm_num

theorem d02_balanced_offDiagonal_frequency {T S δ : ℝ} (hT : 0 < T)
    {H K m n : ℕ} (hH : 0 < H) (hK : 0 < K) (hm : 0 < m) (hn : 0 < n)
    (hne : H * m ≠ K * n)
    (hHK : (H : ℝ) * (K : ℝ) ≤ T ^ S)
    (hmn : (m : ℝ) * (n : ℝ) ≤ T ^ (1 + δ)) :
    (1 / 2 : ℝ) * T ^ ((1 - S - δ) / 2) ≤
      |T * Real.log (((H * m : ℕ) : ℝ) / ((K * n : ℕ) : ℝ))| := by
  have hp : (((H * m : ℕ) : ℝ) * ((K * n : ℕ) : ℝ)) ≤ T ^ (1 + S + δ) := by
    push_cast
    calc
      _ = ((H : ℝ) * (K : ℝ)) * ((m : ℝ) * (n : ℝ)) := by ring
      _ ≤ T ^ S * T ^ (1 + δ) := mul_le_mul hHK hmn (by positivity) (Real.rpow_nonneg hT.le _)
      _ = T ^ (1 + S + δ) := by
        rw [← Real.rpow_add hT]
        congr 1
        ring
  have he : 1 - (1 + S + δ) / 2 = (1 - S - δ) / 2 := by ring
  simpa only [he] using
    d02_product_cutoff_frequency hT (Nat.mul_pos hH hm) (Nat.mul_pos hK hn) hne hp

theorem d02_balanced_frequency_exponent_pos {S δ : ℝ} (hδ : δ < 1 - S) :
    0 < (1 - S - δ) / 2 := by linarith

end
end SixthMoment
