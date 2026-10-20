import Sechstmoment.Arithmetic.Euler.Local.Recurrence.FourDifferences


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem delta_translate (a : R) (f : ℕ → R) (h n : ℕ) :
    delta a (fun k => f (h+k)) n = delta a f (h+n) := by
  simp only [delta, Nat.add_assoc]
theorem delta_zero_sequence (a : R) (n : ℕ) : delta a (fun _ : ℕ => (0:R)) n = 0 := by
  simp [delta]

end Sechstmoment.Source.NoDPLocal
