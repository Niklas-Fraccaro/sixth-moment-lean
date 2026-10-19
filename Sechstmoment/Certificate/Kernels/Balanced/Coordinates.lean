import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Sechstmoment

/-- The coordinate domain in the four-edge denominator polytope.
This proves the constraints used to obtain the density W; the measure
change and the evaluation of that density remain separate obligations. -/
theorem denominator_coordinates_iff (a b c d t r s x : ℝ) :
    (0 ≤ x ∧ 0 ≤ r-x ∧ 0 ≤ s-x ∧ 0 ≤ t-r-s+x ∧
      r ≤ a ∧ t-r ≤ b ∧ s ≤ c ∧ t-s ≤ d) ↔
    (0 ≤ t ∧ t ≤ min (a+b) (c+d) ∧
      max 0 (t-b) ≤ r ∧ r ≤ min a t ∧
      max 0 (t-d) ≤ s ∧ s ≤ min c t ∧
      max 0 (r+s-t) ≤ x ∧ x ≤ min r s) := by
  simp only [le_min_iff, max_le_iff]
  constructor
  · rintro ⟨h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩
    (repeat' constructor) <;> linarith
  · rintro ⟨h₀,⟨h₁,h₂⟩,⟨h₃,h₄⟩,⟨h₅,h₆⟩,⟨h₇,h₈⟩,⟨h₉,h₁₀⟩,⟨h₁₁,h₁₂⟩,⟨h₁₃,h₁₄⟩⟩
    (repeat' constructor) <;> linarith

theorem denominator_coordinate_inverse (t r s x : ℝ) :
    x + (r-x) + (s-x) + (t-r-s+x) = t ∧
    x + (r-x) = r ∧ x + (s-x) = s := by
  constructor
  · ring
  constructor <;> ring

theorem denominator_free_interval_nonnegative {t r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrt : r ≤ t) (hst : s ≤ t) :
    max 0 (r+s-t) ≤ min r s := by
  simp only [max_le_iff, le_min_iff]
  (repeat' constructor) <;> linarith

end Sechstmoment
