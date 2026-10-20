import SixthMoment.Arithmetic.Euler.Local.Recurrence.FourAnnihilator


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem coeff4_recurrence (a b c d : R) (n : ℕ) :
    coeff4 a b c d (n+4) = e1 a b c d*coeff4 a b c d (n+3)-
      e2 a b c d*coeff4 a b c d (n+2)+e3 a b c d*coeff4 a b c d (n+1)-e4 a b c d*coeff4 a b c d n := by
  have h := coeff4_annihilated a b c d n
  rw [delta_four] at h
  simp only [e1,e2,e3,e4] at h ⊢
  linear_combination h

end SixthMoment.Source.NoDPLocal
