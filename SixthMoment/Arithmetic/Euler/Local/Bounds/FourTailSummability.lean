import SixthMoment.Arithmetic.Euler.Local.Bounds.PolynomialGeometricSummability


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem coeff4_tail_summable (a b c d t : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r)
    (ht : r*‖t‖<1) (h : ℕ) : Summable (fun n=>coeff4 a b c d (h+n)*t^n) := by
  have hs : ‖r*‖t‖‖<1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr (norm_nonneg t))] using ht
  apply ((polynomial_geometric_summable (r*‖t‖) ((h:ℝ)+3) hs).mul_left (r^h)).of_norm_bounded
  intro n
  exact norm_tail_weighted a b c d t r hr ha hb hc hd h n

end SixthMoment.Source.NoDPLocal
