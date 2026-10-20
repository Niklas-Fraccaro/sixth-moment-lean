import SixthMoment.Arithmetic.Euler.Local.Bounds.FourRootBound


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem norm_coeff4_polynomial (a b c d : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r) (n : ℕ) :
    ‖coeff4 a b c d n‖≤((n:ℝ)+3)^3*r^n := by
  apply (norm_coeff4_closed a b c d r hr ha hb hc hd n).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr n)
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  nlinarith [sq_nonneg (n:ℝ),mul_nonneg hn (sq_nonneg (n:ℝ))]

end SixthMoment.Source.NoDPLocal
