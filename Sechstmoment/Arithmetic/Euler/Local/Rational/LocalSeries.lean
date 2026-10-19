import Sechstmoment.Arithmetic.Euler.Local.Coefficients.LowerCoefficientComparison

/-! The genuine infinite tail used in the local Euler correction. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

noncomputable def localSeries (a b c d t : ℂ) (h : ℕ) : ℂ :=
  ∑' n : ℕ, coeff4 a b c d (h+n)*t^n
@[simp] theorem localSeries_at_zero (a b c d : ℂ) (h : ℕ) : localSeries a b c d 0 h=coeff4 a b c d h := by
  unfold localSeries
  rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

end Sechstmoment.Source.NoDPLocal
