import Sechstmoment.Arithmetic.Euler.Local.Rational.FourGeometricProduct

/-! Geometric convolution is compatible with ring homomorphisms. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S]
theorem step_map (F : R →+* S) (a : R) (f : ℕ → R) (n : ℕ) :
    F (step a f n)=step (F a) (fun k=>F (f k)) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [step_succ,map_add,map_mul,ih]

end Sechstmoment.Source.NoDPLocal
