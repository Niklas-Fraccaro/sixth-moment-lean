import SixthMoment.Arithmetic.Euler.Local.Prime.ShiftedPrimeParameters


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem shiftedPrimeCoeff_recurrence (p : ℕ) (shifts : Fin 4 → ℂ) (n : ℕ) :
    shiftedPrimeCoeff p shifts (n+4)=
      e1 (primeRoot p (shifts 0)) (primeRoot p (shifts 1)) (primeRoot p (shifts 2)) (primeRoot p (shifts 3))*shiftedPrimeCoeff p shifts (n+3)-
      e2 (primeRoot p (shifts 0)) (primeRoot p (shifts 1)) (primeRoot p (shifts 2)) (primeRoot p (shifts 3))*shiftedPrimeCoeff p shifts (n+2)+
      e3 (primeRoot p (shifts 0)) (primeRoot p (shifts 1)) (primeRoot p (shifts 2)) (primeRoot p (shifts 3))*shiftedPrimeCoeff p shifts (n+1)-
      e4 (primeRoot p (shifts 0)) (primeRoot p (shifts 1)) (primeRoot p (shifts 2)) (primeRoot p (shifts 3))*shiftedPrimeCoeff p shifts n := coeff4_recurrence _ _ _ _ n

end SixthMoment.Source.NoDPLocal
