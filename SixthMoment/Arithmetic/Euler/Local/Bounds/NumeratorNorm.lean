import SixthMoment.Arithmetic.Euler.Local.Prime.PrincipalTailIdentity


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem numerator_norm_le (a b c d t : ℂ) (h : ℕ) :
    ‖numerator a b c d h t‖≤‖q0 a b c d h‖+‖q1 a b c d h‖*‖t‖+
      ‖q2 a b c d h‖*‖t‖^2+‖q3 a b c d h‖*‖t‖^3 := by
  unfold numerator
  calc
    _ ≤ ‖q0 a b c d h+q1 a b c d h*t+q2 a b c d h*t^2‖+‖q3 a b c d h*t^3‖ := norm_add_le _ _
    _ ≤ (‖q0 a b c d h+q1 a b c d h*t‖+‖q2 a b c d h*t^2‖)+‖q3 a b c d h*t^3‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖q0 a b c d h‖+‖q1 a b c d h*t‖)+‖q2 a b c d h*t^2‖)+‖q3 a b c d h*t^3‖ := by gcongr; exact norm_add_le _ _
    _ = _ := by simp [norm_pow]

end SixthMoment.Source.NoDPLocal
