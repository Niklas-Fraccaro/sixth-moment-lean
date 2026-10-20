import SixthMoment.Arithmetic.Euler.Local.Recurrence.ShiftedPrimeRecurrence


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem shifted_prime_local_factorization (p : ℕ) (shifts : Fin 4 → ℂ) (u s : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖primeRoot p (shifts 0)‖≤r) (hb : ‖primeRoot p (shifts 1)‖≤r)
    (hc : ‖primeRoot p (shifts 2)‖≤r) (hd : ‖primeRoot p (shifts 3)‖≤r)
    (ht : r*‖u*(p:ℂ)^(-s)‖<1) (h : ℕ) :
    denom (primeRoot p (shifts 0)) (primeRoot p (shifts 1)) (primeRoot p (shifts 2)) (primeRoot p (shifts 3)) (u*(p:ℂ)^(-s))*
      (∑' n : ℕ,shiftedPrimeCoeff p shifts (h+n)*(u*(p:ℂ)^(-s))^n)=
    numerator (primeRoot p (shifts 0)) (primeRoot p (shifts 1)) (primeRoot p (shifts 2)) (primeRoot p (shifts 3)) h (u*(p:ℂ)^(-s)) :=
  local_series_factorization _ _ _ _ _ r hr ha hb hc hd ht h
theorem shifted_prime_ramified (p : ℕ) (shifts : Fin 4 → ℂ) (s : ℂ) (h : ℕ) :
    (∑' n : ℕ,shiftedPrimeCoeff p shifts (h+n)*((0:ℂ)*(p:ℂ)^(-s))^n)=shiftedPrimeCoeff p shifts h := by
  simpa only [zero_mul,shiftedPrimeCoeff,localSeries] using
    localSeries_at_zero (primeRoot p (shifts 0)) (primeRoot p (shifts 1))
      (primeRoot p (shifts 2)) (primeRoot p (shifts 3)) h

end SixthMoment.Source.NoDPLocal
