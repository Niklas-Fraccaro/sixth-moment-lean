import Sechstmoment.Arithmetic.Euler.Local.Rational.RationalLocalTail


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem localSeries_base (a b c d t : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r)
    (ht : r*‖t‖<1) : localSeries a b c d t 0=(denom a b c d t)⁻¹ := by
  rw [localSeries_eq_rational a b c d t r hr ha hb hc hd ht 0,numerator_base,one_div]

end Sechstmoment.Source.NoDPLocal
