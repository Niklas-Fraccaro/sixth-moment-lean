import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SixthMoment

open MeasureTheory

theorem positivePart_integral_nonpos {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0)
    (n : ℕ) (hn : 0 < n) : (∫ x in a..b, (max x 0)^n) = 0 := by
  calc
    (∫ x in a..b, (max x 0)^n) = ∫ _ in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change (max x 0)^n = 0
      simp only [Set.uIcc_of_le hab, Set.mem_Icc] at hx
      rw [max_eq_right (hx.2.trans hb), zero_pow (by omega)]
    _ = 0 := by simp

theorem positivePart_integral_nonneg {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    (n : ℕ) : (∫ x in a..b, (max x 0)^n) =
      (b^(n+1)-a^(n+1))/(n+1) := by
  calc
    (∫ x in a..b, (max x 0)^n) = ∫ x in a..b, x^n := by
      apply intervalIntegral.integral_congr
      intro x hx
      change (max x 0)^n = x^n
      simp only [Set.uIcc_of_le hab, Set.mem_Icc] at hx
      rw [max_eq_left (ha.trans hx.1)]
    _ = _ := integral_pow n

theorem positivePart_integral {a b : ℝ} (hab : a ≤ b) (n : ℕ) (hn : 0 < n) :
    (∫ x in a..b, (max x 0)^n) =
      ((max b 0)^(n+1)-(max a 0)^(n+1))/(n+1) := by
  by_cases hb : b ≤ 0
  · rw [positivePart_integral_nonpos hab hb n hn,
      max_eq_right hb, max_eq_right (hab.trans hb)]
    simp
  by_cases ha : 0 ≤ a
  · rw [positivePart_integral_nonneg hab ha n, max_eq_left ha,
      max_eq_left (ha.trans hab)]
  have ha' : a ≤ 0 := by linarith
  have hb' : 0 ≤ b := by linarith
  have hc : Continuous (fun x : ℝ => (max x 0)^n) :=
    (continuous_id.max continuous_const).pow n
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a 0) (hc.intervalIntegrable 0 b)]
  rw [positivePart_integral_nonpos ha' le_rfl n hn,
    positivePart_integral_nonneg hb' le_rfl n,
    max_eq_right ha', max_eq_left hb']
  simp

theorem positivePart_shifted_integral {a b : ℝ} (hab : a ≤ b) (c : ℝ)
    (n : ℕ) (hn : 0 < n) :
    (∫ x in a..b, (max (x-c) 0)^n) =
      ((max (b-c) 0)^(n+1)-(max (a-c) 0)^(n+1))/(n+1) := by
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => (max x 0)^n) c]
  apply positivePart_integral (by linarith) n hn

theorem positivePart_reflected_integral {a b : ℝ} (hab : a ≤ b) (c : ℝ)
    (n : ℕ) (hn : 0 < n) :
    (∫ x in a..b, (max (c-x) 0)^n) =
      ((max (c-a) 0)^(n+1)-(max (c-b) 0)^(n+1))/(n+1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => (max x 0)^n) c]
  apply positivePart_integral (by linarith) n hn

end SixthMoment
