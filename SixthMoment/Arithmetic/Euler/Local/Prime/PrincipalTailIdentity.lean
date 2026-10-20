import SixthMoment.Arithmetic.Euler.Local.Prime.PrincipalCubicNumerator


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem principal_tail_rational (t : ℂ) (ht : ‖t‖<1) (h : ℕ) :
    localSeries (1:ℂ) 1 1 1 t h=numerator (1:ℂ) 1 1 1 h t/(1-t)^4 := by
  have H := localSeries_eq_rational (1:ℂ) 1 1 1 t 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simpa using ht) h
  convert H using 1
  unfold denom
  ring

end SixthMoment.Source.NoDPLocal
