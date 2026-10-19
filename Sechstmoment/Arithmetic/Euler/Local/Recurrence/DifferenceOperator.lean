import Sechstmoment.Arithmetic.Euler.Local.Geometric.StepLinearity

/-! The forward difference associated with an Euler denominator. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
def delta (a : R) (f : ℕ → R) (n : ℕ) : R := f (n+1) - a*f n
@[simp] theorem delta_step (a : R) (f : ℕ → R) (n : ℕ) :
    delta a (step a f) n = f (n+1) := by simp [delta]
theorem delta_add (a : R) (f g : ℕ → R) (n : ℕ) :
    delta a (fun k => f k+g k) n = delta a f n+delta a g n := by
  unfold delta; ring

end Sechstmoment.Source.NoDPLocal
