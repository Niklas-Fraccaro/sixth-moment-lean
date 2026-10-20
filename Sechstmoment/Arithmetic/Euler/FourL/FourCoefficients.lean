import Sechstmoment.Arithmetic.Euler.FourL.FixedEuler

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section

def fourAF (s : Fin 4 → ℂ) : ArithmeticFunction ℂ :=
  powerAF (s 0) * (powerAF (s 1) * (powerAF (s 2) * powerAF (s 3)))

theorem threeAF_prime_pow (a b c : ℂ) (p : ℕ) (hp : p.Prime) (h : ℕ) :
    (powerAF a * (powerAF b * powerAF c)) (p^h) =
      coeff3 (primeRoot p a) (primeRoot p b) (primeRoot p c) h := by
  rw [af_mul_prime_pow _ _ p hp h,coeff3_eq_sum]
  simp_rw [powerAF_prime_pow _ p hp,twoAF_prime_pow _ _ p hp]
  rfl

theorem fourAF_prime_pow (s : Fin 4 → ℂ) (p : ℕ) (hp : p.Prime) (h : ℕ) :
    fourAF s (p^h) = shiftedPrimeCoeff p s h := by
  rw [fourAF,af_mul_prime_pow _ _ p hp h,shiftedPrimeCoeff,coeff4_eq_sum]
  simp_rw [powerAF_prime_pow _ p hp,threeAF_prime_pow _ _ _ p hp]
  rfl

theorem fourAF_multiplicative (s : Fin 4 → ℂ) : (fourAF s).IsMultiplicative :=
  (powerAF_multiplicative _).mul ((powerAF_multiplicative _).mul
    ((powerAF_multiplicative _).mul (powerAF_multiplicative _)))

theorem fourAF_eq_shiftedCoeff (s : Fin 4 → ℂ) : (fourAF s : ℕ → ℂ) = shiftedCoeff s := by
  apply eulerCoeff_unique
  · exact ArithmeticFunction.map_zero
  · exact (fourAF_multiplicative s).map_one
  · intro m n hmn
    exact (fourAF_multiplicative s).map_mul_of_coprime hmn
  · exact fourAF_prime_pow s

@[simp] theorem fourAF_zero (s : Fin 4 → ℂ) : fourAF s 0 = 0 := ArithmeticFunction.map_zero
@[simp] theorem fourAF_one (s : Fin 4 → ℂ) : fourAF s 1 = 1 := (fourAF_multiplicative s).map_one

end
end Sechstmoment.Source.NoDPGlobalLFactorization
