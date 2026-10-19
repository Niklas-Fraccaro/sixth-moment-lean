import Sechstmoment.Arithmetic.Euler.FourL.FixedEuler

/-! A divisor sum of bivariate Euler coefficients factors into finite local
diagonal sums. This is the finite arithmetic step used for the residues. -/

namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPResidues NoDPGlobalConvolution
open scoped BigOperators
noncomputable section
set_option autoImplicit false
variable {R : Type*} [CommSemiring R]

theorem pairEuler_divisor_box (A : Nat.Primes → ℕ → ℕ → R)
    (hA : ∀ p, A p 0 0 = 1) (S : Finset Nat.Primes) (n : ℕ) (hn : n ≠ 0)
    (hS : primeSupport n ⊆ S) (f : ExponentBox S n) :
    pairEuler A (boxValue S n f) (n/boxValue S n f) =
      ∏ p : S, A p.val (f p).val (n.factorization p.val.val-(f p).val) := by
  classical
  rw [pairEuler_ambient A hA _ _
    (show boxValue S n f ≠ 0 from (primeProduct_pos _ _).ne')
    (quotient_box_ne_zero S n hn f) S (primeProduct_support _ _)
    ((primeSupport_dvd (Nat.div_dvd_of_dvd (boxValue_dvd S n hn f)) hn).trans hS),
    ← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p _
  rw [boxValue_factor S n f p,quotient_box_factor S n hn f p]

theorem divisor_pairEuler_local_trace (A : Nat.Primes → ℕ → ℕ → R)
    (hA : ∀ p, A p 0 0 = 1) (n : ℕ) :
    fixedEuler (fun p h => ∑ k : Fin (h+1), A p k.val (h-k.val)) ∅ n =
      ∑ d ∈ n.divisors, pairEuler A d (n/d) := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  let S := primeSupport n
  have hS : primeSupport n ⊆ S := fun _ h => h
  have hbase (p : Nat.Primes) (_hp : p ∉ (∅ : Finset Nat.Primes)) :
      (∑ k : Fin (0+1), A p k.val (0-k.val)) = 1 := by simp [hA]
  rw [fixedEuler_ambient _ ∅ hbase n hn S (Finset.empty_subset _) hS,
    sum_divisors_box S n hn hS]
  simp_rw [pairEuler_divisor_box A hA S n hn hS]
  rw [← Finset.prod_coe_sort S]
  exact Fintype.prod_sum (fun p : S => fun k : Fin (n.factorization p.val.val+1) =>
    A p.val k.val (n.factorization p.val.val-k.val))

end
end Sechstmoment.Source.NoDPGlobalLFactorization
