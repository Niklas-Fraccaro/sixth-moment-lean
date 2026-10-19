import Sechstmoment.Arithmetic.Euler.Local.Geometric.ZeroStepParameter

/-! The lower order recurrence for two geometric factors. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem coeff2_annihilated (a b : R) (n : ℕ) : delta b (delta a (coeff2 a b)) n = 0 := by
  simp only [delta,coeff2_succ,coeff1_succ,Nat.add_assoc]; ring
theorem coeff2_recurrence (a b : R) (n : ℕ) :
    coeff2 a b (n+2) = (a+b)*coeff2 a b (n+1)-a*b*coeff2 a b n := by
  have h := coeff2_annihilated a b n
  rw [delta_two] at h
  linear_combination h

end Sechstmoment.Source.NoDPLocal
