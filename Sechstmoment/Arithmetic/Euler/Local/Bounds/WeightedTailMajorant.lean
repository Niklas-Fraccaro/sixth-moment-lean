import Sechstmoment.Arithmetic.Euler.Local.Bounds.FourPolynomialMajorant


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem norm_tail_weighted (a b c d t : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r) (h n : ℕ) :
    ‖coeff4 a b c d (h+n)*t^n‖≤r^h*(((n:ℝ)+((h:ℝ)+3))^3*(r*‖t‖)^n) := by
  rw [norm_mul,norm_pow]
  calc
    _ ≤ (((h+n:ℕ):ℝ)+3)^3*r^(h+n)*‖t‖^n :=
      mul_le_mul_of_nonneg_right (norm_coeff4_polynomial a b c d r hr ha hb hc hd (h+n)) (by positivity)
    _ = _ := by push_cast; rw [pow_add,mul_pow]; ring

end Sechstmoment.Source.NoDPLocal
