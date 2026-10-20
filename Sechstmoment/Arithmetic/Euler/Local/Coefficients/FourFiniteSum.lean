import Sechstmoment.Arithmetic.Euler.Local.Coefficients.ThreeFiniteSum


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem coeff4_eq_sum (a b c d : R) (n : ℕ) :
    coeff4 a b c d n=∑ k ∈ range (n+1), a^(n-k)*coeff3 b c d k := step_eq_sum a (coeff3 b c d) n

end Sechstmoment.Source.NoDPLocal
