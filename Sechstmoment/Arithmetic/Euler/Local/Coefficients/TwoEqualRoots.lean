import Sechstmoment.Arithmetic.Euler.Local.Bounds.FourNorm

/-! The exact repeated-root formula for two geometric factors. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem coeff2_equal_roots (r : ℝ) (n : ℕ) : coeff2 r r n=((n:ℝ)+1)*r^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [coeff2_succ,ih]; simp only [coeff1,Nat.cast_add,Nat.cast_one,pow_succ]; ring

end Sechstmoment.Source.NoDPLocal
