import Sechstmoment.Arithmetic.Euler.Local.Geometric.GeometricStep


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem step_add (a : R) (f g : ℕ → R) (n : ℕ) :
    step a (fun k => f k + g k) n = step a f n + step a g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [step_succ, ih]; ring
theorem step_smul (a c : R) (f : ℕ → R) (n : ℕ) :
    step a (fun k => c * f k) n = c * step a f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [step_succ, ih]; ring
@[simp] theorem step_zero_sequence (a : R) (n : ℕ) : step a (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

end Sechstmoment.Source.NoDPLocal
