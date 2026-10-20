import SixthMoment.Arithmetic.Euler.Local.Rational.LocalSeriesShift


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem localSeries_recurrence (a b c d t : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r)
    (ht : r*‖t‖<1) (h : ℕ) :
    localSeries a b c d t (h+4)=e1 a b c d*localSeries a b c d t (h+3)-
      e2 a b c d*localSeries a b c d t (h+2)+e3 a b c d*localSeries a b c d t (h+1)-e4 a b c d*localSeries a b c d t h := by
  have Hs (k : ℕ) := (coeff4_tail_summable a b c d t r hr ha hb hc hd ht (h+k)).hasSum
  have H := ((((Hs 3).mul_left (e1 a b c d)).sub ((Hs 2).mul_left (e2 a b c d))).add
    ((Hs 1).mul_left (e3 a b c d))).sub ((Hs 0).mul_left (e4 a b c d))
  apply HasSum.tsum_eq
  convert H using 1
  ext n
  simp only [Nat.add_zero,show h+4+n=(h+n)+4 by omega,
    show h+3+n=(h+n)+3 by omega,show h+2+n=(h+n)+2 by omega,
    show h+1+n=(h+n)+1 by omega]
  rw [coeff4_recurrence]
  ring
  all_goals simp only [localSeries,Nat.add_zero]

end SixthMoment.Source.NoDPLocal
