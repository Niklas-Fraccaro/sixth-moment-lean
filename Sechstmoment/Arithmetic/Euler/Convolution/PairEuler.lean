import Sechstmoment.Arithmetic.Euler.Convolution.PrimeBoxes

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace Sechstmoment.Source.NoDPGlobalConvolution
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest
open scoped BigOperators
noncomputable section
open Classical
variable {R : Type*} [CommSemiring R]

def pairEuler (A : Nat.Primes → ℕ → ℕ → R) (m n : ℕ) : R :=
  if m = 0 ∨ n = 0 then 0 else
    ∏ p ∈ primeSupport m ∪ primeSupport n, A p (m.factorization p.val) (n.factorization p.val)

@[simp] theorem pairEuler_zero_left (A : Nat.Primes → ℕ → ℕ → R) (n : ℕ) :
    pairEuler A 0 n = 0 := by simp [pairEuler]

@[simp] theorem pairEuler_zero_right (A : Nat.Primes → ℕ → ℕ → R) (n : ℕ) :
    pairEuler A n 0 = 0 := by simp [pairEuler]

theorem pairEuler_ambient (A : Nat.Primes → ℕ → ℕ → R) (hA : ∀ p, A p 0 0 = 1)
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (S : Finset Nat.Primes)
    (hSm : primeSupport m ⊆ S) (hSn : primeSupport n ⊆ S) :
    pairEuler A m n = ∏ p ∈ S, A p (m.factorization p.val) (n.factorization p.val) := by
  rw [pairEuler, ite_eq_right (by simp [hm,hn])]
  apply Finset.prod_subset (Finset.union_subset hSm hSn)
  intro p _ hp
  have hpm : p ∉ primeSupport m := fun h => hp (Finset.mem_union_left _ h)
  have hpn : p ∉ primeSupport n := fun h => hp (Finset.mem_union_right _ h)
  rw [factorization_outside_support m (primeSupport m) (fun _ h => h) p hpm,
    factorization_outside_support n (primeSupport n) (fun _ h => h) p hpn, hA]

theorem primeProduct_support (S : Finset Nat.Primes) (h : S → ℕ) :
    primeSupport (primeProduct S h) ⊆ S := by
  intro p hp
  by_contra hn
  have H := primeProduct_factor_not_mem S h p hn
  have HN : (primeProduct S h).factorization p.val ≠ 0 := by
    exact Finsupp.mem_support_iff.mp ((mem_primeSupport _ p).mp hp)
  exact HN H

theorem pairEuler_box (A : Nat.Primes → ℕ → ℕ → R) (hA : ∀ p, A p 0 0 = 1)
    (S : Finset Nat.Primes) (m n : ℕ) (f : ExponentBox S m) (g : ExponentBox S n) :
    pairEuler A (boxValue S m f) (boxValue S n g) =
      ∏ p : S, A p.val (f p).val (g p).val := by
  rw [pairEuler_ambient A hA _ _
    (show boxValue S m f ≠ 0 from (primeProduct_pos _ _).ne')
    (show boxValue S n g ≠ 0 from (primeProduct_pos _ _).ne')
    S (primeProduct_support _ _) (primeProduct_support _ _)]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p _
  rw [boxValue_factor S m f p, boxValue_factor S n g p]

theorem quotient_box_ne_zero (S : Finset Nat.Primes) (n : ℕ) (hn : n ≠ 0)
    (f : ExponentBox S n) : n / boxValue S n f ≠ 0 :=
  (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (boxValue_dvd S n hn f))
    (primeProduct_pos _ _)).ne'

theorem pairEuler_quotient_box (A : Nat.Primes → ℕ → ℕ → R) (hA : ∀ p, A p 0 0 = 1)
    (S : Finset Nat.Primes) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hSm : primeSupport m ⊆ S) (hSn : primeSupport n ⊆ S)
    (f : ExponentBox S m) (g : ExponentBox S n) :
    pairEuler A (m / boxValue S m f) (n / boxValue S n g) =
      ∏ p : S, A p.val (m.factorization p.val.val - (f p).val)
        (n.factorization p.val.val - (g p).val) := by
  rw [pairEuler_ambient A hA _ _ (quotient_box_ne_zero S m hm f) (quotient_box_ne_zero S n hn g)
    S ((primeSupport_dvd (Nat.div_dvd_of_dvd (boxValue_dvd S m hm f)) hm).trans hSm)
      ((primeSupport_dvd (Nat.div_dvd_of_dvd (boxValue_dvd S n hn g)) hn).trans hSn)]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p _
  rw [quotient_box_factor S m hm f p, quotient_box_factor S n hn g p]

def localConvolution (A B : Nat.Primes → ℕ → ℕ → R) (p : Nat.Primes) (h k : ℕ) : R :=
  ∑ i : Fin (h+1), ∑ j : Fin (k+1), A p i.val j.val * B p (h-i.val) (k-j.val)

theorem localConvolution_base (A B : Nat.Primes → ℕ → ℕ → R)
    (hA : ∀ p, A p 0 0 = 1) (hB : ∀ p, B p 0 0 = 1) (p : Nat.Primes) :
    localConvolution A B p 0 0 = 1 := by simp [localConvolution, hA, hB]

theorem double_prod_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℕ)
    (F : (p : ι) → Fin (a p + 1) → Fin (b p + 1) → R) :
    (∑ f : (p : ι) → Fin (a p+1), ∑ g : (p : ι) → Fin (b p+1), ∏ p, F p (f p) (g p)) =
      ∏ p, ∑ i, ∑ j, F p i j := by
  classical
  calc
    _ = ∑ f : (p : ι) → Fin (a p+1), ∏ p, ∑ j, F p (f p) j := by
      apply Finset.sum_congr rfl
      intro f _
      exact (Fintype.prod_sum (fun p j => F p (f p) j)).symm
    _ = _ := (Fintype.prod_sum (fun p i => ∑ j, F p i j)).symm

theorem pairEuler_convolution (A B : Nat.Primes → ℕ → ℕ → R)
    (hA : ∀ p, A p 0 0 = 1) (hB : ∀ p, B p 0 0 = 1) (m n : ℕ) :
    pairEuler (localConvolution A B) m n =
      ∑ d ∈ m.divisors, ∑ e ∈ n.divisors, pairEuler A d e * pairEuler B (m/d) (n/e) := by
  by_cases hm : m = 0
  · subst m
    simp
  by_cases hn : n = 0
  · subst n
    simp
  let S := primeSupport m ∪ primeSupport n
  have hSm : primeSupport m ⊆ S := Finset.subset_union_left
  have hSn : primeSupport n ⊆ S := Finset.subset_union_right
  rw [pairEuler_ambient _ (localConvolution_base A B hA hB) m n hm hn S hSm hSn]
  rw [sum_divisors_box S m hm hSm]
  simp_rw [sum_divisors_box S n hn hSn]
  simp_rw [pairEuler_box A hA, pairEuler_quotient_box B hB S m n hm hn hSm hSn,
    ← Finset.prod_mul_distrib]
  rw [← Finset.prod_coe_sort S]
  exact (double_prod_sum (fun p : S => m.factorization p.val.val)
    (fun p : S => n.factorization p.val.val)
    (fun p i j => A p.val i.val j.val * B p.val
      (m.factorization p.val.val-i.val) (n.factorization p.val.val-j.val))).symm

end
end Sechstmoment.Source.NoDPGlobalConvolution
