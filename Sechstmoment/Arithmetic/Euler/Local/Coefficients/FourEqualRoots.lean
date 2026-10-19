import Sechstmoment.Arithmetic.Euler.Local.Coefficients.ThreeEqualRoots

/-! The cubic binomial coefficient for four coinciding local roots. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem coeff4_equal_roots (r : ℝ) (n : ℕ) :
    coeff4 r r r r n=((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)/6*r^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [coeff4_succ,coeff3_equal_roots,ih]
    simp only [Nat.cast_add,Nat.cast_one,pow_succ]; ring

end Sechstmoment.Source.NoDPLocal
