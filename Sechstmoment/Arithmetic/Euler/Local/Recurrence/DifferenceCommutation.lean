import Sechstmoment.Arithmetic.Euler.Local.Recurrence.DifferenceOperator

/-! The Euler difference operators commute. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem delta_comm (a b : R) (f : ℕ → R) (n : ℕ) :
    delta a (delta b f) n = delta b (delta a f) n := by
  simp only [delta]; ring
theorem delta_smul (a c : R) (f : ℕ → R) (n : ℕ) :
    delta a (fun k => c*f k) n = c*delta a f n := by unfold delta; ring

end Sechstmoment.Source.NoDPLocal
