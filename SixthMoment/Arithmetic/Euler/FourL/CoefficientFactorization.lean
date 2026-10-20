import SixthMoment.Arithmetic.Euler.FourL.LocalPolynomial

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace SixthMoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section

def localNumerator (d : ℕ) (s : Fin 4 → ℂ) (u : ℕ →* ℂ) (p : Nat.Primes) (k : ℕ) : ℂ :=
  numeratorCoeff (primeRoot p.val (s 0)) (primeRoot p.val (s 1))
    (primeRoot p.val (s 2)) (primeRoot p.val (s 3)) (d.factorization p.val) k * (u p.val)^k

def localFour (s : Fin 4 → ℂ) (u : ℕ →* ℂ) (p : Nat.Primes) (k : ℕ) : ℂ :=
  shiftedPrimeCoeff p.val s k * (u p.val)^k

def localShift (d : ℕ) (s : Fin 4 → ℂ) (u : ℕ →* ℂ) (p : Nat.Primes) (k : ℕ) : ℂ :=
  shiftedPrimeCoeff p.val s (d.factorization p.val+k) * (u p.val)^k

theorem localNumerator_outside (d : ℕ) (s : Fin 4 → ℂ) (u : ℕ →* ℂ)
    (p : Nat.Primes) (hp : p ∉ primeSupport d) (k : ℕ) :
    localNumerator d s u p k = if k = 0 then 1 else 0 := by
  rw [localNumerator,factorization_outside_support d (primeSupport d) (fun _ h => h) p hp,
    numeratorCoeff_base]
  by_cases hk : k = 0 <;> simp [hk]

@[simp] theorem localFour_base (s : Fin 4 → ℂ) (u : ℕ →* ℂ) (p : Nat.Primes) :
    localFour s u p 0 = 1 := by simp [localFour]

theorem localShift_base_outside (d : ℕ) (s : Fin 4 → ℂ) (u : ℕ →* ℂ)
    (p : Nat.Primes) (hp : p ∉ primeSupport d) : localShift d s u p 0 = 1 := by
  rw [localShift,factorization_outside_support d (primeSupport d) (fun _ h => h) p hp]
  simp

theorem localNumerator_convolution (d : ℕ) (s : Fin 4 → ℂ) (u : ℕ →* ℂ)
    (p : Nat.Primes) (k : ℕ) :
    scalarConvolution (localNumerator d s u) (localFour s u) p k = localShift d s u p k := by
  unfold scalarConvolution localNumerator localFour localShift shiftedPrimeCoeff
  rw [numeratorCoeff_convolution,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val ≤ k := Nat.le_of_lt_succ i.isLt
  have H : (u p.val)^k = (u p.val)^i.val * (u p.val)^(k-i.val) := by
    rw [← pow_add,Nat.add_sub_of_le hi]
  rw [H]
  ring

theorem hom_prime_product (u : ℕ →* ℂ) (n : ℕ) (hn : n ≠ 0)
    (S : Finset Nat.Primes) (hS : primeSupport n ⊆ S) :
    u n = ∏ p ∈ S, (u p.val)^(n.factorization p.val) := by
  have H := congrArg u (primeProduct_factorization n hn S hS)
  simp only [primeProduct,map_prod,map_pow] at H
  exact H.symm.trans (Finset.prod_coe_sort S (fun p => (u p.val)^(n.factorization p.val)))

def twistedAF (u : ℕ →* ℂ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => f n * u n, by simp⟩

theorem twistedAF_euler (s : Fin 4 → ℂ) (u : ℕ →* ℂ) (n : ℕ) :
    twistedAF u (fourAF s) n = eulerCoeff (fun p k => shiftedPrimeCoeff p s k * (u p)^k) n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [show twistedAF u (fourAF s) n = fourAF s n * u n from rfl,
    fourAF_eq_shiftedCoeff,shiftedCoeff,eulerCoeff_primeSupport _ n hn,eulerCoeff_primeSupport _ n hn,
    hom_prime_product u n hn (primeSupport n) (fun _ h => h),← Finset.prod_mul_distrib]

def correctionAF (d : ℕ) (s : Fin 4 → ℂ) (u : ℕ →* ℂ) : ArithmeticFunction ℂ :=
  ⟨fixedEuler (localNumerator d s u) (primeSupport d),by simp⟩

def shiftedAF (d : ℕ) (s : Fin 4 → ℂ) (u : ℕ →* ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else fourAF s (d*n) * u n,by simp⟩

theorem shiftedAF_fixedEuler (d : ℕ) (hd : d ≠ 0) (s : Fin 4 → ℂ)
    (u : ℕ →* ℂ) (n : ℕ) :
    shiftedAF d s u n = fixedEuler (localShift d s u) (primeSupport d) n := by
  by_cases hn : n = 0
  · simp [hn,shiftedAF]
  rw [show shiftedAF d s u n = fourAF s (d*n) * u n from by simp [shiftedAF,hn],
    fourAF_eq_shiftedCoeff,shiftedCoeff,eulerCoeff_primeSupport _ (d*n) (mul_ne_zero hd hn),
    primeSupport_mul d n hd hn,fixedEuler,ite_eq_right hn,
    hom_prime_product u n hn (primeSupport d ∪ primeSupport n) Finset.subset_union_right,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [Nat.factorization_mul hd hn,Finsupp.add_apply]
  rfl

theorem shiftedAF_factorization (d : ℕ) (hd : d ≠ 0) (s : Fin 4 → ℂ) (u : ℕ →* ℂ) :
    shiftedAF d s u = correctionAF d s u * twistedAF u (fourAF s) := by
  ext n
  rw [shiftedAF_fixedEuler d hd s u n]
  have H : localShift d s u = scalarConvolution (localNumerator d s u) (localFour s u) := by
    funext p k
    exact (localNumerator_convolution d s u p k).symm
  rw [H,fixedEuler_convolution _ _ (primeSupport d)
    (fun p hp => by simpa using localNumerator_outside d s u p hp 0)
    (fun p _ => localFour_base s u p),ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => correctionAF d s u a * twistedAF u (fourAF s) b)]
  apply Finset.sum_congr rfl
  intro a _
  rw [show correctionAF d s u a = fixedEuler (localNumerator d s u) (primeSupport d) a from rfl,
    twistedAF_euler]
  congr 1
  exact fixedEuler_eq_eulerCoeff (fun p k => shiftedPrimeCoeff p s k * (u p)^k)
    (fun p => by simp) (primeSupport d) (n/a)

end
end SixthMoment.Source.NoDPGlobalLFactorization
