import Sechstmoment.Arithmetic.Euler.Local.Coefficients.TwoFiniteSum

/-! The threefold divisor coefficient as an iterated finite sum. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem coeff3_eq_sum (a b c : R) (n : ℕ) :
    coeff3 a b c n=∑ k ∈ range (n+1), a^(n-k)*coeff2 b c k := step_eq_sum a (coeff2 b c) n

end Sechstmoment.Source.NoDPLocal
