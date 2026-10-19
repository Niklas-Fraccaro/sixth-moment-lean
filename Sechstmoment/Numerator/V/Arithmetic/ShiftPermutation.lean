import Sechstmoment.Arithmetic.Euler.FourL.Continuation

/-! Reindexing the distinguished residue leaves the actual fourfold
Dirichlet coefficients and the entire arithmetic correction unchanged. -/

namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem fourAF_eq_product (β : Fin 4 → ℂ) :
    fourAF β = ∏ j : Fin 4, powerAF (β j) := by
  simp [fourAF,Fin.prod_univ_succ]

theorem fourAF_reindexShifts (i : Fin 4) (β : Fin 4 → ℂ) :
    fourAF (reindexShifts i β) = fourAF β := by
  rw [fourAF_eq_product,fourAF_eq_product]
  exact Equiv.prod_comp (Equiv.swap (0:Fin 4) i) (fun j => powerAF (β j))

theorem shiftedPrimeCoeff_reindexShifts (p : ℕ) (hp : p.Prime)
    (i : Fin 4) (β : Fin 4 → ℂ) (h : ℕ) :
    shiftedPrimeCoeff p (reindexShifts i β) h = shiftedPrimeCoeff p β h := by
  rw [← fourAF_prime_pow (reindexShifts i β) p hp h,fourAF_reindexShifts,
    fourAF_prime_pow β p hp h]

theorem primeCorrection_reindexShifts (p : ℕ) (hp : p.Prime)
    (i : Fin 4) (β : Fin 4 → ℂ) (u : ℂ) (h : ℕ) (s : ℂ) :
    primeCorrection p (reindexShifts i β) u h s = primeCorrection p β u h s := by
  have hc (n : ℕ) :
      coeff4 (primeRoot p (reindexShifts i β 0)) (primeRoot p (reindexShifts i β 1))
        (primeRoot p (reindexShifts i β 2)) (primeRoot p (reindexShifts i β 3)) n =
      coeff4 (primeRoot p (β 0)) (primeRoot p (β 1))
        (primeRoot p (β 2)) (primeRoot p (β 3)) n :=
    shiftedPrimeCoeff_reindexShifts p hp i β n
  have he1 :
      e1 (primeRoot p (reindexShifts i β 0)) (primeRoot p (reindexShifts i β 1))
        (primeRoot p (reindexShifts i β 2)) (primeRoot p (reindexShifts i β 3)) =
      e1 (primeRoot p (β 0)) (primeRoot p (β 1))
        (primeRoot p (β 2)) (primeRoot p (β 3)) := by
    fin_cases i <;> norm_num [reindexShifts,Equiv.swap_apply_def,e1] <;> ring
  have he2 :
      e2 (primeRoot p (reindexShifts i β 0)) (primeRoot p (reindexShifts i β 1))
        (primeRoot p (reindexShifts i β 2)) (primeRoot p (reindexShifts i β 3)) =
      e2 (primeRoot p (β 0)) (primeRoot p (β 1))
        (primeRoot p (β 2)) (primeRoot p (β 3)) := by
    fin_cases i <;> norm_num [reindexShifts,Equiv.swap_apply_def,e2] <;> ring
  have he3 :
      e3 (primeRoot p (reindexShifts i β 0)) (primeRoot p (reindexShifts i β 1))
        (primeRoot p (reindexShifts i β 2)) (primeRoot p (reindexShifts i β 3)) =
      e3 (primeRoot p (β 0)) (primeRoot p (β 1))
        (primeRoot p (β 2)) (primeRoot p (β 3)) := by
    fin_cases i <;> norm_num [reindexShifts,Equiv.swap_apply_def,e3] <;> ring
  unfold primeCorrection numerator q0 q1 q2 q3
  simp_rw [hc,he1,he2,he3]

theorem eulerCorrection_reindexShifts {q : ℕ} (χ : DirichletCharacter ℂ q)
    (d : ℕ) (i : Fin 4) (β : Fin 4 → ℂ) (s : ℂ) :
    eulerCorrection χ d (reindexShifts i β) s = eulerCorrection χ d β s := by
  by_cases hd : d = 0
  · subst d
    simp [eulerCorrection]
  simp only [eulerCorrection,arithmeticCorrection_eq_finite d hd,finiteCorrection]
  apply Finset.prod_congr rfl
  intro p hp
  exact primeCorrection_reindexShifts p (Nat.prime_of_mem_primeFactors hp) i β _ _ _

theorem shiftedContinuation_reindexShifts {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (d : ℕ) (i : Fin 4) (β : Fin 4 → ℂ) (s : ℂ) :
    shiftedContinuation χ d (reindexShifts i β) s = shiftedContinuation χ d β s := by
  unfold shiftedContinuation
  rw [eulerCorrection_reindexShifts]
  congr 1
  exact Equiv.prod_comp (Equiv.swap (0:Fin 4) i) (fun j => χ.LFunction (s+β j))

end
end Sechstmoment.Source.NoDPGlobalLFactorization
