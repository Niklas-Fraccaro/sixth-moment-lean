import Mathlib.NumberTheory.Divisors
import SixthMoment.Arithmetic.Euler.Remainder.Factorization

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace SixthMoment.Source.NoDPGlobalConvolution
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest
open scoped BigOperators
noncomputable section

theorem divisor_ne_zero {d n : ℕ} (hd : d ∈ n.divisors) : d ≠ 0 :=
  ne_zero_of_dvd_ne_zero (Nat.ne_zero_of_mem_divisors hd) (Nat.dvd_of_mem_divisors hd)

def primeSupport (n : ℕ) : Finset Nat.Primes := n.primeFactors.subtype Nat.Prime

theorem mem_primeSupport (n : ℕ) (p : Nat.Primes) :
    p ∈ primeSupport n ↔ p.val ∈ n.primeFactors := Finset.mem_subtype

def primeProduct (S : Finset Nat.Primes) (h : S → ℕ) : ℕ := ∏ p : S, p.val.val ^ h p

theorem primeProduct_pos (S : Finset Nat.Primes) (h : S → ℕ) : 0 < primeProduct S h :=
  Finset.prod_pos (fun p _ => pow_pos p.val.property.pos _)

theorem primeProduct_factor_mem (S : Finset Nat.Primes) (h : S → ℕ)
    (p : Nat.Primes) (hp : p ∈ S) :
    (primeProduct S h).factorization p.val = h ⟨p,hp⟩ := by
  rw [primeProduct, config_factorization]
  rw [Finset.sum_eq_single ⟨p,hp⟩]
  · simp
  · intro q _ hq
    have H : q.val ≠ p := fun H => hq (Subtype.ext H)
    simp [H]
  · simp

theorem primeProduct_factor_not_mem (S : Finset Nat.Primes) (h : S → ℕ)
    (p : Nat.Primes) (hp : p ∉ S) : (primeProduct S h).factorization p.val = 0 := by
  rw [primeProduct, config_factorization]
  apply Finset.sum_eq_zero
  intro q _
  have H : q.val ≠ p := fun H => hp (H ▸ q.property)
  simp [H]

theorem primeProduct_injective (S : Finset Nat.Primes) : Function.Injective (primeProduct S) := by
  intro h k hk
  funext p
  have H := congrArg (fun n => n.factorization p.val.val) hk
  simpa only [primeProduct_factor_mem S h p.val p.property,
    primeProduct_factor_mem S k p.val p.property] using H

theorem factorization_outside_support (n : ℕ) (S : Finset Nat.Primes)
    (hS : primeSupport n ⊆ S) (p : Nat.Primes) (hp : p ∉ S) : n.factorization p.val = 0 := by
  apply Finsupp.notMem_support_iff.mp
  intro hn
  exact hp (hS ((mem_primeSupport n p).mpr hn))

theorem primeProduct_factorization (n : ℕ) (hn : n ≠ 0) (S : Finset Nat.Primes)
    (hS : primeSupport n ⊆ S) : primeProduct S (fun p => n.factorization p.val.val) = n := by
  apply Nat.eq_of_factorization_eq' (primeProduct_pos _ _).ne' hn
  ext q
  by_cases hq : q.Prime
  · let p : Nat.Primes := ⟨q,hq⟩
    by_cases hp : p ∈ S
    · exact primeProduct_factor_mem S _ p hp
    · rw [primeProduct_factor_not_mem S _ p hp, factorization_outside_support n S hS p hp]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq, Nat.factorization_eq_zero_of_not_prime _ hq]

theorem primeSupport_dvd {d n : ℕ} (hdn : d ∣ n) (hn : n ≠ 0) :
    primeSupport d ⊆ primeSupport n := by
  intro p hp
  rw [mem_primeSupport] at hp ⊢
  exact Nat.mem_primeFactors.mpr ⟨p.property, (Nat.dvd_of_mem_primeFactors hp).trans hdn, hn⟩

abbrev ExponentBox (S : Finset Nat.Primes) (n : ℕ) := (p : S) → Fin (n.factorization p.val.val + 1)

def boxValue (S : Finset Nat.Primes) (n : ℕ) (h : ExponentBox S n) : ℕ :=
  primeProduct S (fun p => (h p).val)

theorem boxValue_dvd (S : Finset Nat.Primes) (n : ℕ) (hn : n ≠ 0)
    (h : ExponentBox S n) : boxValue S n h ∣ n := by
  apply (Nat.factorization_le_iff_dvd (primeProduct_pos _ _).ne' hn).mp
  intro q
  by_cases hq : q.Prime
  · let p : Nat.Primes := ⟨q,hq⟩
    by_cases hp : p ∈ S
    · rw [show (primeProduct S (fun p => (h p).val)).factorization q = (h ⟨p,hp⟩).val from
        primeProduct_factor_mem S _ p hp]
      exact Nat.le_of_lt_succ (h ⟨p,hp⟩).isLt
    · rw [show (primeProduct S (fun p => (h p).val)).factorization q = 0 from primeProduct_factor_not_mem S _ p hp]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq]
    exact Nat.zero_le _

def divisorBox (S : Finset Nat.Primes) (n : ℕ) (hn : n ≠ 0)
    (d : n.divisors) : ExponentBox S n := fun p =>
  ⟨d.val.factorization p.val.val, Nat.lt_succ_of_le
    ((Nat.factorization_le_iff_dvd (divisor_ne_zero d.property) hn).mpr
      (Nat.dvd_of_mem_divisors d.property) p.val.val)⟩

theorem boxValue_divisorBox (S : Finset Nat.Primes) (n : ℕ) (hn : n ≠ 0)
    (hS : primeSupport n ⊆ S) (d : n.divisors) :
    boxValue S n (divisorBox S n hn d) = d.val :=
  primeProduct_factorization d.val (divisor_ne_zero d.property) S
    ((primeSupport_dvd (Nat.dvd_of_mem_divisors d.property) hn).trans hS)

def divisorsEquivBox (S : Finset Nat.Primes) (n : ℕ) (hn : n ≠ 0)
    (hS : primeSupport n ⊆ S) : n.divisors ≃ ExponentBox S n where
  toFun := divisorBox S n hn
  invFun h := ⟨boxValue S n h, Nat.mem_divisors.mpr ⟨boxValue_dvd S n hn h, hn⟩⟩
  left_inv d := Subtype.ext (boxValue_divisorBox S n hn hS d)
  right_inv h := by
    funext p
    apply Fin.ext
    exact primeProduct_factor_mem S _ p.val p.property

theorem sum_divisors_box {R : Type*} [AddCommMonoid R] (S : Finset Nat.Primes)
    (n : ℕ) (hn : n ≠ 0) (hS : primeSupport n ⊆ S) (f : ℕ → R) :
    (∑ d ∈ n.divisors, f d) = ∑ h : ExponentBox S n, f (boxValue S n h) := by
  rw [← Finset.sum_coe_sort n.divisors f]
  exact ((divisorsEquivBox S n hn hS).symm.sum_comp (fun d : n.divisors => f d.val)).symm

theorem boxValue_factor (S : Finset Nat.Primes) (n : ℕ) (h : ExponentBox S n) (p : S) :
    (boxValue S n h).factorization p.val.val = (h p).val :=
  primeProduct_factor_mem S _ p.val p.property

theorem quotient_box_factor (S : Finset Nat.Primes) (n : ℕ) (hn : n ≠ 0)
    (h : ExponentBox S n) (p : S) :
    (n / boxValue S n h).factorization p.val.val = n.factorization p.val.val - (h p).val := by
  rw [Nat.factorization_div (boxValue_dvd S n hn h), Finsupp.tsub_apply, boxValue_factor]

end
end SixthMoment.Source.NoDPGlobalConvolution
