import Sechstmoment.Arithmetic.Euler.Local.Coefficients.FourEqualRoots


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem norm_coeff4_closed (a b c d : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r) (n : ℕ) :
    ‖coeff4 a b c d n‖≤((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)/6*r^n := by
  rw [← coeff4_equal_roots]
  exact norm_coeff4_le a b c d r hr ha hb hc hd n

end Sechstmoment.Source.NoDPLocal
