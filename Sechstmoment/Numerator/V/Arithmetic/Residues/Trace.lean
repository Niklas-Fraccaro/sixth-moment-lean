import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Sechstmoment.Arithmetic.Euler.Residues.DivisorEulerTrace
import Sechstmoment.Numerator.V.Arithmetic.Residues.Local


namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def principalResidueLocalPair (β : Fin 4 → ℂ) (p : Nat.Primes) (k h : ℕ) : ℂ :=
  (ArithmeticFunction.moebius (p.val^k):ℂ)*(primeRoot p.val (β 0))^k*
    (if k = 0 then 1 else
      den3 (primeRoot p.val (β 1)) (primeRoot p.val (β 2)) (primeRoot p.val (β 3))
        ((p.val:ℂ)^(-(1-β 0))))*
    primeCorrection p.val β (if k = 0 then 1 else 0) h (1-β 0)

@[simp] theorem principalResidueLocalPair_zero (β : Fin 4 → ℂ) (p : Nat.Primes) (h : ℕ) :
    principalResidueLocalPair β p 0 h = primeCorrection p.val β 1 h (1-β 0) := by
  simp [principalResidueLocalPair]

@[simp] theorem principalResidueLocalPair_one (β : Fin 4 → ℂ) (p : Nat.Primes) (h : ℕ) :
    principalResidueLocalPair β p 1 h =
      -(primeRoot p.val (β 0)*
        den3 (primeRoot p.val (β 1)) (primeRoot p.val (β 2)) (primeRoot p.val (β 3))
          ((p.val:ℂ)^(-(1-β 0)))*primeCorrection p.val β 0 h (1-β 0)) := by
  simp [principalResidueLocalPair,ArithmeticFunction.moebius_apply_prime p.property]

theorem principalResidueLocalPair_vanish (β : Fin 4 → ℂ) (p : Nat.Primes)
    {k : ℕ} (hk : 2 ≤ k) (h : ℕ) : principalResidueLocalPair β p k h = 0 := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  simp only [principalResidueLocalPair,ArithmeticFunction.moebius_apply_prime_pow p.property hk0,
    ite_eq_right hk1,Int.cast_zero,zero_mul]

theorem principalResidueLocalPair_trace (β : Fin 4 → ℂ) (p : Nat.Primes) (h : ℕ) :
    (∑ k : Fin (h+1), principalResidueLocalPair β p k.val (h-k.val)) =
      (p.val:ℂ)^h*primeWeight p.val β h := by
  classical
  have hp0 : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have H := congrArg (fun z : ℂ => (p.val:ℂ)^h*z)
    (primeWeight_principal_correction p.val p.property β h)
  rw [← mul_assoc,primeX,← mul_pow,mul_inv_cancel₀ hp0,one_pow,one_mul] at H
  cases h with
  | zero => simp [primeWeight]
  | succ h =>
    have hrest :
        (∑ k : Fin (h+1), principalResidueLocalPair β p (k.val+1) (h+1-(k.val+1))) =
          principalResidueLocalPair β p 1 h := by
      calc
        _ = principalResidueLocalPair β p ((0:Fin (h+1)).val+1)
            (h+1-((0:Fin (h+1)).val+1)) := by
          apply Finset.sum_eq_single (0:Fin (h+1))
          · intro k _ hk
            have hkval : k.val ≠ 0 := by
              intro he
              exact hk (Fin.ext he)
            exact principalResidueLocalPair_vanish β p (by omega) _
          · simp
        _ = _ := by simp
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,Nat.sub_zero]
    rw [hrest,principalResidueLocalPair_zero,principalResidueLocalPair_one]
    simpa only [Nat.succ_ne_zero,ite_false,Nat.succ_sub_one,sub_eq_add_neg] using H.symm

theorem principalResiduePair_divisor_trace (β : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hβ : ∀ j, ‖β j‖ ≤ ρ) (N : ℕ) :
    (∑ q ∈ N.divisors, pairEuler (principalResidueLocalPair β) q (N/q)) =
      (N:ℂ)*originalCoeffAt 0 β N 1 := by
  classical
  have hbase (p : Nat.Primes) : principalResidueLocalPair β p 0 0 = 1 := by simp
  rw [← divisor_pairEuler_local_trace (principalResidueLocalPair β) hbase]
  have hlocal (p : Nat.Primes) (h : ℕ) :
      (∑ k : Fin (h+1), principalResidueLocalPair β p k.val (h-k.val)) =
        (p.val:ℂ)^h*primeWeight p.val β h := principalResidueLocalPair_trace β p h
  simp_rw [hlocal]
  rw [fixedEuler_eq_eulerCoeff (fun p h => (p:ℂ)^h*primeWeight p β h)
    (fun p => by simp [primeWeight]),eulerCoeff_pointwise_product]
  have hnat : (fun n : ℕ => (n:ℂ)) = eulerCoeff (fun p h => (p:ℂ)^h) := by
    apply eulerCoeff_unique
    · simp
    · simp
    · intro m n _
      exact Nat.cast_mul m n
    · intro p _ h
      exact Nat.cast_pow p h
  rw [← hnat]
  have horiginal : originalCoeffAt 0 β N 1 = eulerCoeff (fun p h => primeWeight p β h) N := by
    simpa only [originalCoeffAt,reindexShifts,Equiv.swap_self,Equiv.coe_refl,
      Function.comp_id,mul_one] using originalCoeff_weightEuler β ρ hρ0 hρ hβ N 1
  rw [horiginal]

end
end Sechstmoment.Source.NoDPGlobalLFactorization
