import SixthMoment.Arithmetic.Euler.Convolution.Factorization

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace SixthMoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section
open Classical
variable {R : Type*} [CommSemiring R]

def fixedEuler (A : Nat.Primes → ℕ → R) (D : Finset Nat.Primes) (n : ℕ) : R :=
  if n = 0 then 0 else ∏ p ∈ D ∪ primeSupport n, A p (n.factorization p.val)

@[simp] theorem fixedEuler_zero (A : Nat.Primes → ℕ → R) (D : Finset Nat.Primes) :
    fixedEuler A D 0 = 0 := by simp [fixedEuler]

theorem fixedEuler_ambient (A : Nat.Primes → ℕ → R) (D : Finset Nat.Primes)
    (hA : ∀ p ∉ D, A p 0 = 1) (n : ℕ) (hn : n ≠ 0) (S : Finset Nat.Primes)
    (hD : D ⊆ S) (hS : primeSupport n ⊆ S) :
    fixedEuler A D n = ∏ p ∈ S, A p (n.factorization p.val) := by
  rw [fixedEuler,ite_eq_right hn]
  apply Finset.prod_subset (Finset.union_subset hD hS)
  intro p _ hp
  have hpD : p ∉ D := fun h => hp (Finset.mem_union_left _ h)
  have hpn : p ∉ primeSupport n := fun h => hp (Finset.mem_union_right _ h)
  rw [factorization_outside_support n (primeSupport n) (fun _ h => h) p hpn,hA p hpD]

theorem fixedEuler_eq_eulerCoeff (A : ℕ → ℕ → R)
    (hA : ∀ p : Nat.Primes, A p.val 0 = 1) (D : Finset Nat.Primes) (n : ℕ) :
    fixedEuler (fun p => A p.val) D n = eulerCoeff A n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [fixedEuler,ite_eq_right hn,eulerCoeff_ambient A hA n hn (D ∪ primeSupport n)
    Finset.subset_union_right]

def scalarConvolution (A B : Nat.Primes → ℕ → R) (p : Nat.Primes) (h : ℕ) : R :=
  ∑ i : Fin (h+1), A p i.val * B p (h-i.val)

theorem fixedEuler_box (A : Nat.Primes → ℕ → R) (D : Finset Nat.Primes)
    (hA : ∀ p ∉ D, A p 0 = 1) (S : Finset Nat.Primes) (hD : D ⊆ S)
    (n : ℕ) (f : ExponentBox S n) :
    fixedEuler A D (boxValue S n f) = ∏ p : S, A p.val (f p).val := by
  rw [fixedEuler_ambient A D hA _ (show boxValue S n f ≠ 0 from (primeProduct_pos _ _).ne')
    S hD (primeProduct_support _ _), ← Finset.prod_coe_sort]
  exact Finset.prod_congr rfl (fun p _ => by rw [boxValue_factor S n f p])

theorem fixedEuler_quotient_box (A : Nat.Primes → ℕ → R) (D : Finset Nat.Primes)
    (hA : ∀ p ∉ D, A p 0 = 1) (S : Finset Nat.Primes) (hD : D ⊆ S)
    (n : ℕ) (hn : n ≠ 0) (hS : primeSupport n ⊆ S) (f : ExponentBox S n) :
    fixedEuler A D (n / boxValue S n f) =
      ∏ p : S, A p.val (n.factorization p.val.val - (f p).val) := by
  rw [fixedEuler_ambient A D hA _ (quotient_box_ne_zero S n hn f) S hD
    ((primeSupport_dvd (Nat.div_dvd_of_dvd (boxValue_dvd S n hn f)) hn).trans hS),
    ← Finset.prod_coe_sort]
  exact Finset.prod_congr rfl (fun p _ => by rw [quotient_box_factor S n hn f p])

theorem fixedEuler_convolution (A B : Nat.Primes → ℕ → R) (D : Finset Nat.Primes)
    (hA : ∀ p ∉ D, A p 0 = 1) (hB : ∀ p ∉ D, B p 0 = 1) (n : ℕ) :
    fixedEuler (scalarConvolution A B) D n =
      ∑ d ∈ n.divisors, fixedEuler A D d * fixedEuler B D (n/d) := by
  by_cases hn : n = 0
  · simp [hn]
  let S := D ∪ primeSupport n
  have hD : D ⊆ S := Finset.subset_union_left
  have hS : primeSupport n ⊆ S := Finset.subset_union_right
  have hAB : ∀ p ∉ D, scalarConvolution A B p 0 = 1 := by
    intro p hp
    simp [scalarConvolution,hA p hp,hB p hp]
  rw [fixedEuler_ambient _ D hAB n hn S hD hS,sum_divisors_box S n hn hS]
  simp_rw [fixedEuler_box A D hA S hD,fixedEuler_quotient_box B D hB S hD n hn hS,
    ← Finset.prod_mul_distrib]
  rw [← Finset.prod_coe_sort S]
  exact Fintype.prod_sum (fun p : S => fun i : Fin (n.factorization p.val.val+1) =>
    A p.val i.val * B p.val (n.factorization p.val.val-i.val))

end
end SixthMoment.Source.NoDPGlobalLFactorization
