import Sechstmoment.Arithmetic.Euler.Local.Recurrence.ThreeDifferences


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem delta_four (a b c d : R) (f : ℕ → R) (n : ℕ) :
    delta a (delta b (delta c (delta d f))) n =
      f (n+4)-e1 a b c d*f (n+3)+e2 a b c d*f (n+2)-e3 a b c d*f (n+1)+e4 a b c d*f n := by
  simp only [delta, e1, e2, e3, e4, Nat.add_assoc]; ring

end Sechstmoment.Source.NoDPLocal
