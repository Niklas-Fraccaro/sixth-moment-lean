import Sechstmoment.Arithmetic.Euler.Local.Recurrence.TwoDifferences


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem delta_three (a b c : R) (f : ℕ → R) (n : ℕ) :
    delta a (delta b (delta c f)) n =
      f (n+3)-(a+b+c)*f (n+2)+(a*b+a*c+b*c)*f (n+1)-a*b*c*f n := by
  simp only [delta, Nat.add_assoc]; ring

end Sechstmoment.Source.NoDPLocal
