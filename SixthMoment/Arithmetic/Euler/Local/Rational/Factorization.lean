import SixthMoment.Arithmetic.Euler.Local.Prime.ShiftedPrimeLocalIdentity


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem local_factorization_complete (a b c d t : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r)
    (ht : r*‖t‖<1) (h : ℕ) :
    Summable (fun n : ℕ=>coeff4 a b c d (h+n)*t^n) ∧ denom a b c d t≠0 ∧
      localSeries a b c d t h=numerator a b c d h t/denom a b c d t :=
  ⟨coeff4_tail_summable a b c d t r hr ha hb hc hd ht h,
    denom_norm_region_ne_zero a b c d t r ha hb hc hd ht,
    localSeries_eq_rational a b c d t r hr ha hb hc hd ht h⟩

end SixthMoment.Source.NoDPLocal
