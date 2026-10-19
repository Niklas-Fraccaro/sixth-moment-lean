import Sechstmoment.Arithmetic.Euler.Local.Recurrence.LocalSeriesRecurrence

/-! The actual infinite local tail times its Euler denominator is cubic. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem local_series_factorization (a b c d t : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r)
    (ht : r*‖t‖<1) (h : ℕ) :
    denom a b c d t*localSeries a b c d t h=numerator a b c d h t := by
  have H0 := localSeries_shift a b c d t r hr ha hb hc hd ht h
  have H1 := localSeries_shift a b c d t r hr ha hb hc hd ht (h+1)
  have H2 := localSeries_shift a b c d t r hr ha hb hc hd ht (h+2)
  have H3 := localSeries_shift a b c d t r hr ha hb hc hd ht (h+3)
  have H4 := localSeries_recurrence a b c d t r hr ha hb hc hd ht h
  simp only [Nat.add_assoc] at H1 H2 H3
  rw [denom_expansion]
  unfold numerator q0 q1 q2 q3
  linear_combination
    (1-e1 a b c d*t+e2 a b c d*t^2-e3 a b c d*t^3)*H0+
    (t-e1 a b c d*t^2+e2 a b c d*t^3)*H1+
    (t^2-e1 a b c d*t^3)*H2+t^3*H3+t^4*H4

end Sechstmoment.Source.NoDPLocal
