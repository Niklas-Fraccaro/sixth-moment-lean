import SixthMoment.Arithmetic.Euler.FourL.Continuation


namespace SixthMoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem principalCharacter_prime_value (q : ℕ) [NeZero q] (p : ℕ) (hp : p.Prime) :
    (1 : DirichletCharacter ℂ q) (p:ZMod q) = if p ∣ q then 0 else 1 := by
  classical
  by_cases hd : p ∣ q
  · rw [ite_eq_left hd]
    apply MulChar.map_nonunit
    intro hu
    exact (hp.coprime_iff_not_dvd.mp ((ZMod.isUnit_iff_coprime p q).mp hu)) hd
  · rw [ite_eq_right hd]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd))

theorem primeWeight_principal_correction (p : ℕ) (hp : p.Prime)
    (β : Fin 4 → ℂ) (h : ℕ) :
    primeWeight p β h = (primeX p)^h*
      (primeCorrection p β 1 h (1-β 0)-
        if h = 0 then 0 else
          primeRoot p (β 0)*
            den3 (primeRoot p (β 1)) (primeRoot p (β 2)) (primeRoot p (β 3))
              ((p:ℂ)^(-(1-β 0)))*primeCorrection p β 0 (h-1) (1-β 0)) := by
  rw [primeWeight,weightedResidue_homogeneous _ _ _ _ _
    (primeRoot_ne_zero p hp.ne_zero (β 0)),← prime_pole_parameter p hp]
  simp only [primeCorrection,eulerParameter,one_mul,zero_mul,numerator_at_zero]
  cases h with
  | zero => simp
  | succ h =>
    simp only [Nat.succ_ne_zero,ite_false,Nat.succ_sub_one]
    rw [show primeRoot p (β 0)*
        den3 (primeRoot p (β 1)) (primeRoot p (β 2)) (primeRoot p (β 3))
          ((p:ℂ)^(-(1-β 0)))*
        coeff4 (primeRoot p (β 0)) (primeRoot p (β 1))
          (primeRoot p (β 2)) (primeRoot p (β 3)) h =
      primeRoot p (β 0)*
        coeff4 (primeRoot p (β 0)) (primeRoot p (β 1))
          (primeRoot p (β 2)) (primeRoot p (β 3)) h*
        den3 (primeRoot p (β 1)) (primeRoot p (β 2)) (primeRoot p (β 3))
          ((p:ℂ)^(-(1-β 0))) by ring]
    rw [numerator_residue_cancel]

theorem originalCoeffAt_prime_power_principal_correction
    (p : ℕ) (hp : p.Prime) (i : Fin 4) (β : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hβ : ∀ j, ‖β j‖ ≤ ρ) (h : ℕ) :
    originalCoeffAt i β (p^h) 1 = (primeX p)^h*
      (primeCorrection p (reindexShifts i β) 1 h (1-β i)-
        if h = 0 then 0 else
          primeRoot p (β i)*
            den3 (primeRoot p (reindexShifts i β 1))
              (primeRoot p (reindexShifts i β 2)) (primeRoot p (reindexShifts i β 3))
              ((p:ℂ)^(-(1-β i)))*
            primeCorrection p (reindexShifts i β) 0 (h-1) (1-β i)) := by
  unfold originalCoeffAt
  rw [originalCoeff_weightEuler (reindexShifts i β) ρ hρ0 hρ
    (fun j => hβ (Equiv.swap 0 i j)) (p^h) 1,mul_one]
  rw [eulerCoeff_prime_pow _ (fun q => by simp [primeWeight]) p hp h]
  simpa only [reindexShifts_distinguished] using
    primeWeight_principal_correction p hp (reindexShifts i β) h

end
end SixthMoment.Source.NoDPGlobalLFactorization
