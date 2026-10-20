import SixthMoment.Arithmetic.Euler.Local.Rational.LocalSeries


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem localSeries_shift (a b c d t : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r)
    (ht : r*‖t‖<1) (h : ℕ) :
    localSeries a b c d t h=coeff4 a b c d h+t*localSeries a b c d t (h+1) := by
  have H := (coeff4_tail_summable a b c d t r hr ha hb hc hd ht h).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,Nat.add_zero,pow_zero,mul_one] at H
  change (∑' n : ℕ, coeff4 a b c d (h+n)*t^n) = _
  rw [← H]
  congr 1
  rw [localSeries,← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [show h+(n+1)=(h+1)+n by omega,pow_succ]
  ring

end SixthMoment.Source.NoDPLocal
