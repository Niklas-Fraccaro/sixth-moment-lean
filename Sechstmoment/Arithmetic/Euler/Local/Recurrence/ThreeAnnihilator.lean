import Sechstmoment.Arithmetic.Euler.Local.Recurrence.TwoAnnihilator


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem coeff3_annihilated (a b c : R) (n : ℕ) :
    delta c (delta b (delta a (coeff3 a b c))) n = 0 := by
  simp only [delta,coeff3_succ,coeff2_succ,coeff1_succ,Nat.add_assoc]; ring
theorem coeff3_recurrence (a b c : R) (n : ℕ) :
    coeff3 a b c (n+3) = (a+b+c)*coeff3 a b c (n+2)-
      (a*b+a*c+b*c)*coeff3 a b c (n+1)+a*b*c*coeff3 a b c n := by
  have h := coeff3_annihilated a b c n
  rw [delta_three] at h
  linear_combination h

end Sechstmoment.Source.NoDPLocal
