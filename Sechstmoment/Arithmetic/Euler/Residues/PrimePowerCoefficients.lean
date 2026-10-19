import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Sechstmoment.Arithmetic.Euler.Residues.FiniteCorrections

/-!
# Multiplicative extension of the actual prime-power coefficients
This is a canonical Euler extension. Identification with an independently defined
fourfold Dirichlet convolution is a separate theorem, not a definition here.
-/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPResidues
open NoDPLocal
open scoped BigOperators
variable {R : Type*} [CommMonoidWithZero R]
noncomputable def eulerCoeff (A : ℕ → ℕ → R) (n : ℕ) : R :=
  if n = 0 then 0 else n.factorization.prod A

@[simp] theorem eulerCoeff_zero (A : ℕ → ℕ → R) : eulerCoeff A 0 = 0 := by simp [eulerCoeff]
@[simp] theorem eulerCoeff_one (A : ℕ → ℕ → R) : eulerCoeff A 1 = 1 := by simp [eulerCoeff]

theorem eulerCoeff_nonzero (A : ℕ → ℕ → R) (n : ℕ) (hn : n ≠ 0) :
    eulerCoeff A n = n.factorization.prod A := by simp [eulerCoeff, hn]

theorem eulerCoeff_prime_pow (A : ℕ → ℕ → R) (hA : ∀ p, A p 0 = 1)
    (p : ℕ) (hp : p.Prime) (k : ℕ) : eulerCoeff A (p^k) = A p k := by
  rw [eulerCoeff_nonzero A (p^k) (pow_ne_zero _ hp.ne_zero), hp.factorization_pow]
  exact Finsupp.prod_single_index (hA p)

theorem eulerCoeff_prime (A : ℕ → ℕ → R) (hA : ∀ p, A p 0 = 1)
    (p : ℕ) (hp : p.Prime) : eulerCoeff A p = A p 1 := by
  simpa using eulerCoeff_prime_pow A hA p hp 1

theorem eulerCoeff_coprime (A : ℕ → ℕ → R) (m n : ℕ) (hmn : m.Coprime n) :
    eulerCoeff A (m*n) = eulerCoeff A m*eulerCoeff A n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [eulerCoeff_nonzero A (m*n) (mul_ne_zero hm hn), eulerCoeff_nonzero A m hm,
    eulerCoeff_nonzero A n hn, Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors A

theorem eulerCoeff_congr (A B : ℕ → ℕ → R)
    (hAB : ∀ p, p.Prime → ∀ k, 0 < k → A p k = B p k) (n : ℕ) :
    eulerCoeff A n = eulerCoeff B n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [eulerCoeff_nonzero A n hn, eulerCoeff_nonzero B n hn]
  apply Finsupp.prod_congr
  intro p hp
  exact hAB p (Nat.prime_of_mem_primeFactors hp) _
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))

theorem eulerCoeff_unique (A : ℕ → ℕ → R) (f : ℕ → R) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hm : ∀ m n, m.Coprime n → f (m*n) = f m*f n)
    (hp : ∀ p, p.Prime → ∀ k, f (p^k) = A p k) : f = eulerCoeff A := by
  funext n
  by_cases hn : n = 0
  · simp [hn, h0]
  rw [eulerCoeff_nonzero A n hn, Nat.multiplicative_factorization f hm h1 hn]
  apply Finsupp.prod_congr
  intro p hpn
  exact hp p (Nat.prime_of_mem_primeFactors hpn) _

theorem eulerCoeff_pointwise_product (A B : ℕ → ℕ → R) (n : ℕ) :
    eulerCoeff (fun p k => A p k*B p k) n = eulerCoeff A n*eulerCoeff B n := by
  by_cases hn : n = 0
  · simp [hn]
  simp only [eulerCoeff_nonzero _ n hn, Finsupp.prod_mul]

theorem eulerCoeff_norm (A : ℕ → ℕ → ℂ) (n : ℕ) :
    ‖eulerCoeff A n‖ = eulerCoeff (fun p k => ‖A p k‖) n := by
  by_cases hn : n = 0
  · simp [hn]
  simp [eulerCoeff_nonzero _ n hn, Finsupp.prod, norm_prod]

noncomputable def shiftedCoeff (shifts : Fin 4 → ℂ) : ℕ → ℂ := eulerCoeff (fun p k => shiftedPrimeCoeff p shifts k)

theorem shiftedCoeff_prime_pow (shifts : Fin 4 → ℂ) (p : ℕ) (hp : p.Prime) (k : ℕ) :
    shiftedCoeff shifts (p^k) = shiftedPrimeCoeff p shifts k :=
  eulerCoeff_prime_pow _ (fun _ => shiftedPrimeCoeff_zero _ _) p hp k

theorem shiftedCoeff_coprime (shifts : Fin 4 → ℂ) (m n : ℕ) (hmn : m.Coprime n) :
    shiftedCoeff shifts (m*n) = shiftedCoeff shifts m*shiftedCoeff shifts n :=
  eulerCoeff_coprime _ m n hmn

end Sechstmoment.Source.NoDPResidues
