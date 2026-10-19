import Sechstmoment.Arithmetic.Euler.Local.Bounds.NormRegionNonzero

/-! The shifted local series is an explicit rational function. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem localSeries_eq_rational (a b c d t : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r)
    (ht : r*‖t‖<1) (h : ℕ) :
    localSeries a b c d t h=numerator a b c d h t/denom a b c d t := by
  apply (eq_div_iff (denom_norm_region_ne_zero a b c d t r ha hb hc hd ht)).mpr
  rw [mul_comm]
  exact local_series_factorization a b c d t r hr ha hb hc hd ht h

end Sechstmoment.Source.NoDPLocal
