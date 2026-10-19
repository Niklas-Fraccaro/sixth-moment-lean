import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Tactic.LinearCombination
import Sechstmoment.Certificate.Kernels.Balanced.Density
import Sechstmoment.Certificate.Kernels.Balanced.IntegerEvaluator

namespace Sechstmoment

noncomputable def realW6 (t a b c d : ℝ) : ℝ :=
  let lo := max 0 (t-b)
  let hi := min a t
  let ll := max 0 (t-d)
  let hh := min c t
  if hi ≤ lo ∨ hh ≤ ll then 0 else
    3*(hi^2-lo^2)*(hh-ll) +
      (max (hi-hh) 0)^3 - (max (hi+hh-t) 0)^3 -
      (max (lo-hh) 0)^3 + (max (lo+hh-t) 0)^3 -
      (max (hi-ll) 0)^3 + (max (hi+ll-t) 0)^3 +
      (max (lo-ll) 0)^3 - (max (lo+ll-t) 0)^3

theorem w6_integer_cast (t a b c d : Int) :
    (Finite.w6 t a b c d : ℝ) = realW6 t a b c d := by
  have hc : (min a t ≤ max 0 (t-b) ∨ min c t ≤ max 0 (t-d)) ↔
      (min (a : ℝ) t ≤ max 0 ((t : ℝ)-b) ∨
        min (c : ℝ) t ≤ max 0 ((t : ℝ)-d)) := by norm_cast
  dsimp only [Finite.w6, realW6]
  by_cases h : min a t ≤ max 0 (t-b) ∨ min c t ≤ max 0 (t-d)
  · simp only [ite_eq_left h, ite_eq_left (hc.mp h), Int.cast_zero]
  · simp only [ite_eq_right h, ite_eq_right ((not_congr hc).mp h)]
    (push_cast; rfl)

theorem realW6_homogeneous (t a b c d M : ℝ) (hM : 0 < M) :
    realW6 (t/M) (a/M) (b/M) (c/M) (d/M) = realW6 t a b c d/M^3 := by
  have hp (x : ℝ) : max (x/M) 0 = max x 0/M := by
    simpa only [zero_div] using max_div_div_right hM.le x 0
  have hl : max 0 (t/M-b/M) = max 0 (t-b)/M := by
    rw [← sub_div]
    simpa only [zero_div] using max_div_div_right hM.le 0 (t-b)
  have hr : min (a/M) (t/M) = min a t/M := min_div_div_right hM.le a t
  have hm : max 0 (t/M-d/M) = max 0 (t-d)/M := by
    rw [← sub_div]
    simpa only [zero_div] using max_div_div_right hM.le 0 (t-d)
  have hs : min (c/M) (t/M) = min c t/M := min_div_div_right hM.le c t
  unfold realW6
  rw [hl, hr, hm, hs]
  simp only [div_le_div_iff_of_pos_right hM]
  split_ifs
  · simp
  · simp only [← add_div, ← sub_div, hp]
    field_simp

theorem realW6_integral {a b c d t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ht : 0 ≤ t) (hmax : t ≤ min (a+b) (c+d)) :
    realW6 t a b c d =
      6*(∫ r in max 0 (t-b)..min a t,
        ∫ s in max 0 (t-d)..min c t, min r s-max (s-(t-r)) 0) := by
  have hab : t ≤ a+b := le_trans hmax (min_le_left _ _)
  have hcd : t ≤ c+d := le_trans hmax (min_le_right _ _)
  have hlu : max 0 (t-b) ≤ min a t := by
    simp only [max_le_iff, le_min_iff]
    (repeat' constructor) <;> linarith
  have hmv : max 0 (t-d) ≤ min c t := by
    simp only [max_le_iff, le_min_iff]
    (repeat' constructor) <;> linarith
  by_cases he : min a t ≤ max 0 (t-b) ∨ min c t ≤ max 0 (t-d)
  · unfold realW6
    rw [ite_eq_left he]
    rcases he with hr | hs
    · have hh := le_antisymm hr hlu
      simp [hh]
    · have hh := le_antisymm hs hmv
      simp [hh]
  · have hi := denominator_density_cubic hlu hmv t
    have heq (r s : ℝ) : r-(t-s) = r+s-t := by ring
    simp_rw [heq] at hi
    unfold realW6
    rw [ite_eq_right he]
    simp_rw [heq]
    linear_combination -hi

end Sechstmoment
