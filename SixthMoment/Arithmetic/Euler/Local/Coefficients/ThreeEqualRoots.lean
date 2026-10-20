import SixthMoment.Arithmetic.Euler.Local.Coefficients.TwoEqualRoots


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem coeff3_equal_roots (r : ℝ) (n : ℕ) : coeff3 r r r n=((n:ℝ)+1)*((n:ℝ)+2)/2*r^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [coeff3_succ,coeff2_equal_roots,ih]
    simp only [Nat.cast_add,Nat.cast_one,pow_succ]; ring

end SixthMoment.Source.NoDPLocal
