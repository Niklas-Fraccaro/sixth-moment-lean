import Sechstmoment.Arithmetic.Euler.Local.Rational.ConvergentLocalFactorization


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem one_sub_mul_ne_zero (a t : ℂ) (r : ℝ) (ha : ‖a‖≤r) (ht : r*‖t‖<1) : 1-a*t≠0 := by
  intro H
  have he : a*t=1 := (sub_eq_zero.mp H).symm
  have hn : ‖a*t‖<1 := by rw [norm_mul]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right ha (norm_nonneg t)) ht
  rw [he,norm_one] at hn
  exact (lt_irrefl (1:ℝ)) hn
theorem denom_norm_region_ne_zero (a b c d t : ℂ) (r : ℝ)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r) (ht : r*‖t‖<1) : denom a b c d t≠0 :=
  denom_ne_zero a b c d t (one_sub_mul_ne_zero a t r ha ht) (one_sub_mul_ne_zero b t r hb ht)
    (one_sub_mul_ne_zero c t r hc ht) (one_sub_mul_ne_zero d t r hd ht)

end Sechstmoment.Source.NoDPLocal
