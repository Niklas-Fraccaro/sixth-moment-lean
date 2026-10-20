import Sechstmoment.Arithmetic.Euler.Local.Recurrence.FourRecurrenceUniqueness


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem step_scaled (a r : R) (f : ℕ → R) (n : ℕ) :
    step (r*a) (fun k => r^k*f k) n = r^n*step a f n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [step_succ,ih,pow_succ]; ring
theorem coeff1_scaled (a r : R) (n : ℕ) : coeff1 (r*a) n=r^n*coeff1 a n := by
  simp [coeff1,mul_pow]

end Sechstmoment.Source.NoDPLocal
