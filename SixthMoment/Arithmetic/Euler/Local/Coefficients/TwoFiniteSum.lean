import SixthMoment.Arithmetic.Euler.Local.Geometric.StepFiniteSum


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem coeff2_eq_sum (a b : R) (n : ℕ) : coeff2 a b n=∑ k ∈ range (n+1), a^(n-k)*b^k := by
  simpa only [coeff2,coeff1] using step_eq_sum a (coeff1 b) n

end SixthMoment.Source.NoDPLocal
