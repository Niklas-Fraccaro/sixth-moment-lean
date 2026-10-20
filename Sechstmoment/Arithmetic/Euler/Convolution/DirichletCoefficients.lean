import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Convolution
import Sechstmoment.Arithmetic.Euler.Convolution.EulerBridges

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalConvolution
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest
open scoped BigOperators
noncomputable section

def powerAF (z : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (n:ℂ)^(-z), by simp⟩

theorem powerAF_apply (z : ℂ) (n : ℕ) (hn : n ≠ 0) : powerAF z n = (n:ℂ)^(-z) := by
  simp [powerAF,hn]

theorem powerAF_multiplicative (z : ℂ) : (powerAF z).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [powerAF], ?_⟩
  intro m n hm hn _
  rw [powerAF_apply _ _ (mul_ne_zero hm hn), powerAF_apply _ _ hm, powerAF_apply _ _ hn]
  simpa only [Nat.cast_mul] using Complex.natCast_mul_natCast_cpow m n (-z)

theorem powerAF_prime_pow (z : ℂ) (p : ℕ) (hp : p.Prime) (h : ℕ) :
    powerAF z (p^h) = ((p:ℂ)^(-z))^h := by
  rw [powerAF_apply _ _ (pow_ne_zero _ hp.ne_zero), Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul, mul_comm, Complex.cpow_mul_nat]

theorem powerAF_euler (z : ℂ) :
    (powerAF z : ℕ → ℂ) = eulerCoeff (fun p h => ((p:ℂ)^(-z))^h) := by
  apply eulerCoeff_unique
  · exact ArithmeticFunction.map_zero
  · exact (powerAF_multiplicative z).map_one
  · intro m n hmn
    exact (powerAF_multiplicative z).map_mul_of_coprime hmn
  · exact powerAF_prime_pow z

theorem af_mul_prime_pow (f g : ArithmeticFunction ℂ) (p : ℕ) (hp : p.Prime) (h : ℕ) :
    (f*g) (p^h) = ∑ j ∈ Finset.range (h+1), f (p^(h-j)) * g (p^j) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun x y => f x * g y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.pow_div (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hp.pos]

def tripleAF (s : Fin 4 → ℂ) : ArithmeticFunction ℂ :=
  powerAF (1+s 1) * (powerAF (1+s 2) * powerAF (1+s 3))

def tripleCoeff (s : Fin 4 → ℂ) (n : ℕ) : ℂ := tripleAF s n

def tripleLocal (s : Fin 4 → ℂ) (p h : ℕ) : ℂ :=
  coeff3 (primeX p * primeRoot p (s 1)) (primeX p * primeRoot p (s 2))
    (primeX p * primeRoot p (s 3)) h

theorem primeX_mul_root (p : ℕ) (hp : p ≠ 0) (z : ℂ) :
    (p:ℂ)^(-(1+z)) = primeX p * primeRoot p z := by
  rw [neg_add, Complex.cpow_add _ _ (by exact_mod_cast hp)]
  simp only [primeX, primeRoot, Complex.cpow_neg, Complex.cpow_one]

theorem twoAF_prime_pow (b c : ℂ) (p : ℕ) (hp : p.Prime) (h : ℕ) :
    (powerAF b * powerAF c) (p^h) = coeff2 ((p:ℂ)^(-b)) ((p:ℂ)^(-c)) h := by
  rw [af_mul_prime_pow _ _ p hp h, coeff2_eq_sum]
  simp_rw [powerAF_prime_pow _ p hp]

theorem tripleCoeff_prime_pow (s : Fin 4 → ℂ) (p : ℕ) (hp : p.Prime) (h : ℕ) :
    tripleCoeff s (p^h) = tripleLocal s p h := by
  rw [tripleCoeff, tripleAF, af_mul_prime_pow _ _ p hp h]
  simp_rw [powerAF_prime_pow _ p hp, twoAF_prime_pow _ _ p hp]
  rw [tripleLocal, ← primeX_mul_root p hp.ne_zero, ← primeX_mul_root p hp.ne_zero,
    ← primeX_mul_root p hp.ne_zero, coeff3_eq_sum]

theorem tripleAF_multiplicative (s : Fin 4 → ℂ) : (tripleAF s).IsMultiplicative :=
  (powerAF_multiplicative _).mul ((powerAF_multiplicative _).mul (powerAF_multiplicative _))

theorem tripleCoeff_euler (s : Fin 4 → ℂ) : tripleCoeff s = eulerCoeff (tripleLocal s) := by
  apply eulerCoeff_unique
  · exact ArithmeticFunction.map_zero
  · exact (tripleAF_multiplicative s).map_one
  · intro m n hmn
    exact (tripleAF_multiplicative s).map_mul_of_coprime hmn
  · exact tripleCoeff_prime_pow s

@[simp] theorem tripleLocal_base (s : Fin 4 → ℂ) (p : ℕ) : tripleLocal s p 0 = 1 := by
  simp [tripleLocal]

@[simp] theorem tripleCoeff_zero (s : Fin 4 → ℂ) : tripleCoeff s 0 = 0 :=
  ArithmeticFunction.map_zero

@[simp] theorem tripleCoeff_one (s : Fin 4 → ℂ) : tripleCoeff s 1 = 1 :=
  (tripleAF_multiplicative s).map_one

end
end Sechstmoment.Source.NoDPGlobalConvolution
