import Sechstmoment.Arithmetic.Euler.Convolution.PairEuler

/-! Scalar, separable and diagonal Euler coefficients over ordinary positive integers. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalConvolution
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommSemiring R]

theorem eulerCoeff_primeSupport (A : ℕ → ℕ → R) (n : ℕ) (hn : n ≠ 0) :
    eulerCoeff A n = ∏ p ∈ primeSupport n, A p.val (n.factorization p.val) := by
  rw [eulerCoeff_nonzero A n hn, Finsupp.prod]
  exact (Finset.prod_subtype_of_mem (fun p => A p (n.factorization p))
    (fun p hp => Nat.prime_of_mem_primeFactors hp)).symm

theorem eulerCoeff_ambient (A : ℕ → ℕ → R) (hA : ∀ p : Nat.Primes, A p.val 0 = 1)
    (n : ℕ) (hn : n ≠ 0) (S : Finset Nat.Primes) (hS : primeSupport n ⊆ S) :
    eulerCoeff A n = ∏ p ∈ S, A p.val (n.factorization p.val) := by
  rw [eulerCoeff_primeSupport A n hn]
  apply Finset.prod_subset hS
  intro p _ hp
  rw [factorization_outside_support n (primeSupport n) (fun _ h => h) p hp, hA]

theorem primeSupport_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    primeSupport (m*n) = primeSupport m ∪ primeSupport n := by
  ext p
  simp only [mem_primeSupport, Nat.primeFactors_mul hm hn, Finset.mem_union]

theorem pairEuler_total (W : ℕ → ℕ → R) (m n : ℕ) :
    pairEuler (fun p h k => W p.val (h+k)) m n = eulerCoeff W (m*n) := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [pairEuler, ite_eq_right (by simp [hm,hn]),
    eulerCoeff_primeSupport W (m*n) (mul_ne_zero hm hn), primeSupport_mul m n hm hn,
    Nat.factorization_mul hm hn]
  rfl

theorem pairEuler_separable (A B : ℕ → ℕ → R)
    (hA : ∀ p : Nat.Primes, A p.val 0 = 1) (hB : ∀ p : Nat.Primes, B p.val 0 = 1) (m n : ℕ) :
    pairEuler (fun p h k => A p.val h * B p.val k) m n = eulerCoeff A m * eulerCoeff B n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  let S := primeSupport m ∪ primeSupport n
  rw [pairEuler, ite_eq_right (by simp [hm,hn]),
    eulerCoeff_ambient A hA m hm S Finset.subset_union_left,
    eulerCoeff_ambient B hB n hn S Finset.subset_union_right, ← Finset.prod_mul_distrib]

end
end Sechstmoment.Source.NoDPGlobalConvolution
