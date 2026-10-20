import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Sechstmoment.Arithmetic.Euler.Local.Prime.PrincipalFactorIdentity


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

noncomputable def primeRoot (p : ℕ) (shifts : ℂ) : ℂ := (p:ℂ)^(-shifts)
noncomputable def shiftedPrimeCoeff (p : ℕ) (shifts : Fin 4 → ℂ) (h : ℕ) : ℂ :=
  coeff4 (primeRoot p (shifts 0)) (primeRoot p (shifts 1)) (primeRoot p (shifts 2)) (primeRoot p (shifts 3)) h
@[simp] theorem shiftedPrimeCoeff_zero (p : ℕ) (shifts : Fin 4 → ℂ) : shiftedPrimeCoeff p shifts 0=1 := by simp [shiftedPrimeCoeff]
theorem shiftedPrimeCoeff_one (p : ℕ) (shifts : Fin 4 → ℂ) :
    shiftedPrimeCoeff p shifts 1=primeRoot p (shifts 0)+primeRoot p (shifts 1)+primeRoot p (shifts 2)+primeRoot p (shifts 3) := by simp [shiftedPrimeCoeff]

end Sechstmoment.Source.NoDPLocal
