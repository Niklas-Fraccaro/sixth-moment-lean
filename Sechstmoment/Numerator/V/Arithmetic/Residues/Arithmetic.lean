import Sechstmoment.Numerator.V.Arithmetic.Residues.Trace
import Sechstmoment.Numerator.V.Arithmetic.ShiftPermutation


namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def principalResidueEulerZero (β : Fin 4 → ℂ) (q : ℕ) : ℂ :=
  ∏ p ∈ primeSupport q,
    den3 (primeRoot p.val (β 1)) (primeRoot p.val (β 2)) (primeRoot p.val (β 3))
      ((p.val:ℂ)^(-(1-β 0)))

theorem principalResiduePair_eq_character (β : Fin 4 → ℂ)
    (q : ℕ) [NeZero q] (d : ℕ) (hd : d ≠ 0) :
    pairEuler (principalResidueLocalPair β) q d =
      (ArithmeticFunction.moebius q:ℂ)*(q:ℂ)^(-β 0)*principalResidueEulerZero β q*
        eulerCorrection (1 : DirichletCharacter ℂ q) d β (1-β 0) := by
  classical
  have hq : q ≠ 0 := NeZero.ne q
  let S := primeSupport q ∪ primeSupport d
  have hqS : primeSupport q ⊆ S := Finset.subset_union_left
  have hdS : primeSupport d ⊆ S := Finset.subset_union_right
  have hmuFun : (fun n : ℕ => (ArithmeticFunction.moebius n:ℂ)) =
      eulerCoeff (fun p k => (ArithmeticFunction.moebius (p^k):ℂ)) := by
    apply eulerCoeff_unique
    · simp
    · simp
    · intro m n hmn
      exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn
    · intro p _ k
      rfl
  have hmu : (∏ p ∈ S, (ArithmeticFunction.moebius (p.val^q.factorization p.val):ℂ)) =
      (ArithmeticFunction.moebius q:ℂ) := by
    rw [congrFun hmuFun q]
    exact (eulerCoeff_ambient
      (fun (p k : ℕ) => (ArithmeticFunction.moebius (p^k):ℂ))
      (fun p => by simp) q hq S hqS).symm
  have hroot : (∏ p ∈ S, (primeRoot p.val (β 0))^q.factorization p.val) =
      (q:ℂ)^(-β 0) := by
    have H := congrArg (fun n : ℕ => (n:ℂ)^(-β 0))
      (primeProduct_factorization q hq S hqS)
    rw [primeProduct,nat_prod_cpow] at H
    rw [← H,← Finset.prod_coe_sort S]
    apply Finset.prod_congr rfl
    intro p _
    rw [Nat.cast_pow,← Complex.natCast_cpow_natCast_mul,mul_comm,Complex.cpow_mul_nat]
    rfl
  let D (p : Nat.Primes) : ℂ :=
    den3 (primeRoot p.val (β 1)) (primeRoot p.val (β 2)) (primeRoot p.val (β 3))
      ((p.val:ℂ)^(-(1-β 0)))
  have hden : (∏ p ∈ S, if q.factorization p.val = 0 then 1 else D p) =
      principalResidueEulerZero β q := by
    calc
      _ = ∏ p ∈ primeSupport q, if q.factorization p.val = 0 then 1 else D p := by
        symm
        apply Finset.prod_subset hqS
        intro p _ hp
        rw [factorization_outside_support q (primeSupport q) (fun _ h => h) p hp]
        simp
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p hp
        have hf : q.factorization p.val ≠ 0 :=
          Finsupp.mem_support_iff.mp ((mem_primeSupport q p).mp hp)
        simp only [ite_eq_right hf]
        rfl
  have hchar (p : Nat.Primes) :
      (if q.factorization p.val = 0 then (1:ℂ) else 0) =
        (1 : DirichletCharacter ℂ q) (p.val:ZMod q) := by
    rw [principalCharacter_prime_value q p.val p.property]
    by_cases hp : p.val ∣ q
    · simp [hp,(p.property.factorization_pos_of_dvd hq hp).ne']
    · have hf : q.factorization p.val = 0 := by
        by_contra H
        exact hp (Nat.dvd_of_factorization_pos H)
      simp [hp,hf]
  have hcorr : (∏ p ∈ S, primeCorrection p.val β
      (if q.factorization p.val = 0 then 1 else 0) (d.factorization p.val) (1-β 0)) =
        eulerCorrection (1 : DirichletCharacter ℂ q) d β (1-β 0) := by
    simp_rw [hchar]
    exact (eulerCoeff_ambient (fun (p h : ℕ) => primeCorrection p β
      ((1 : DirichletCharacter ℂ q) (p:ZMod q)) h (1-β 0))
      (fun p => primeCorrection_base p.val β _ _)
      d hd S hdS).symm
  rw [pairEuler_ambient _ (fun p => by simp) q d hq hd S hqS hdS]
  simp only [principalResidueLocalPair,Finset.prod_mul_distrib]
  change ((∏ p ∈ S, (ArithmeticFunction.moebius (p.val^q.factorization p.val):ℂ))*
    (∏ p ∈ S, (primeRoot p.val (β 0))^q.factorization p.val))*
    (∏ p ∈ S, if q.factorization p.val = 0 then 1 else D p)*
    (∏ p ∈ S, primeCorrection p.val β (if q.factorization p.val = 0 then 1 else 0)
      (d.factorization p.val) (1-β 0)) = _
  rw [hmu,hroot,hden,hcorr]

def principalResidueArithmeticTerm (β : Fin 4 → ℂ) (q d : ℕ) : ℂ :=
  if hq : q = 0 then 0 else
    let : NeZero q := ⟨hq⟩
    (ArithmeticFunction.moebius q:ℂ)*(q:ℂ)^(-β 0)*principalResidueEulerZero β q*
      eulerCorrection (1 : DirichletCharacter ℂ q) d β (1-β 0)

theorem principalResidueEulerZero_reindex (i : Fin 4) (β : Fin 4 → ℂ) (q : ℕ) :
    principalResidueEulerZero (reindexShifts i β) q =
      ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
        ∏ p ∈ q.primeFactors, (1-(p:ℂ)^(-(1+β j-β i))) := by
  classical
  have hnat : principalResidueEulerZero (reindexShifts i β) q =
      ∏ p ∈ q.primeFactors,
        den3 (primeRoot p (reindexShifts i β 1)) (primeRoot p (reindexShifts i β 2))
          (primeRoot p (reindexShifts i β 3)) ((p:ℂ)^(-(1-β i))) := by
    unfold principalResidueEulerZero
    rw [reindexShifts_distinguished]
    exact Finset.prod_subtype_of_mem
        (fun p : ℕ => den3 (primeRoot p (reindexShifts i β 1))
          (primeRoot p (reindexShifts i β 2)) (primeRoot p (reindexShifts i β 3))
          ((p:ℂ)^(-(1-β i)))) (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [hnat]
  calc
    _ = ∏ p ∈ q.primeFactors, ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
        (1-(p:ℂ)^(-(1+β j-β i))) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (p:ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      have he (j : Fin 4) :
          primeRoot p (reindexShifts i β j)*(p:ℂ)^(-(1-β i)) =
            (p:ℂ)^(-(1+β (Equiv.swap 0 i j)-β i)) := by
        rw [primeRoot,← Complex.cpow_add _ _ hp0]
        congr 1
        change -(β (Equiv.swap 0 i j)) + -(1-β i) = _
        ring
      rw [den3,he 1,he 2,he 3,mul_assoc]
      exact swap_complement_product i (fun j => 1-(p:ℂ)^(-(1+β j-β i)))
    _ = _ := Finset.prod_comm

theorem principalResidueArithmeticTerm_reindex (i : Fin 4) (β : Fin 4 → ℂ)
    (q : ℕ) [NeZero q] (d : ℕ) :
    principalResidueArithmeticTerm (reindexShifts i β) q d =
      (ArithmeticFunction.moebius q:ℂ)*(q:ℂ)^(-β i)*
        (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
          ∏ p ∈ q.primeFactors, (1-(p:ℂ)^(-(1+β j-β i))))*
        eulerCorrection (1 : DirichletCharacter ℂ q) d β (1-β i) := by
  rw [principalResidueArithmeticTerm,dite_eq_right (NeZero.ne q),
    reindexShifts_distinguished,principalResidueEulerZero_reindex,
    eulerCorrection_reindexShifts]

theorem principalResidueArithmetic_divisor_sum (β : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hβ : ∀ j, ‖β j‖ ≤ ρ) (N : ℕ) :
    (∑ q ∈ N.divisors, principalResidueArithmeticTerm β q (N/q)) =
      (N:ℂ)*originalCoeffAt 0 β N 1 := by
  classical
  rw [← principalResiduePair_divisor_trace β ρ hρ0 hρ hβ N]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 := divisor_ne_zero hq
  have hd : N/q ≠ 0 := (Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hq))
      (Nat.dvd_of_mem_divisors hq)) (Nat.pos_of_ne_zero hq0)).ne'
  let : NeZero q := ⟨hq0⟩
  rw [principalResidueArithmeticTerm,dite_eq_right hq0]
  exact (principalResiduePair_eq_character β q (N/q) hd).symm

theorem principalResidueArithmetic_divisor_sum_at (i : Fin 4) (β : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hβ : ∀ j, ‖β j‖ ≤ ρ) (N : ℕ) :
    (∑ q ∈ N.divisors, principalResidueArithmeticTerm (reindexShifts i β) q (N/q)) =
      (N:ℂ)*originalCoeffAt i β N 1 := by
  have H := principalResidueArithmetic_divisor_sum (reindexShifts i β) ρ hρ0 hρ
    (fun j => hβ (Equiv.swap 0 i j)) N
  simpa only [originalCoeffAt,reindexShifts,Equiv.swap_self,Equiv.coe_refl,
    Function.comp_id] using H

end
end Sechstmoment.Source.NoDPGlobalLFactorization
