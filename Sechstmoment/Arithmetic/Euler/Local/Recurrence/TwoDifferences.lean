import Sechstmoment.Arithmetic.Euler.Local.Coefficients.ElementarySymmetric


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem delta_two (a b : R) (f : ℕ → R) (n : ℕ) :
    delta a (delta b f) n = f (n+2)-(a+b)*f (n+1)+a*b*f n := by
  simp only [delta]; ring

end Sechstmoment.Source.NoDPLocal
