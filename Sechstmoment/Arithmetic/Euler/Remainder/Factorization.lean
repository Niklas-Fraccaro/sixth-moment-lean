import Sechstmoment.Arithmetic.Euler.Remainder.CoefficientContracts
import Sechstmoment.Arithmetic.Euler.Remainder.EulerIdentification
import Sechstmoment.Arithmetic.Euler.Remainder.ShiftLipschitz

/-! Completed global remainder chapter: every residue index, (6.5), (6.6),
the actual Euler/Dirichlet identification, and the exact zero-shift factor.
This chapter does not assert the six-zeta convolution for the original global
residue coefficients or the V-generator asymptotic. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalRest
open NoDPLocal NoDPResidues NoDPLocalClosure
open scoped BigOperators
noncomputable section

def reindexShifts (i : Fin 4) (s : Fin 4 → ℂ) : Fin 4 → ℂ := s ∘ Equiv.swap 0 i
def gammaAt (i : Fin 4) (s : Fin 4 → ℂ) : ℕ × ℕ → ℂ := gamma (reindexShifts i s)
def restDirichletAt (i : Fin 4) (s : Fin 4 → ℂ) (u v : ℂ) : ℂ :=
  restDirichlet (reindexShifts i s) u v

theorem reindexShifts_distinguished (i : Fin 4) (s : Fin 4 → ℂ) : reindexShifts i s 0 = s i := by
  simp [reindexShifts]

theorem reindexShifts_norm_le (i : Fin 4) (s : Fin 4 → ℂ) : ‖reindexShifts i s‖ ≤ ‖s‖ := by
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg s)).mpr (fun j => norm_le_pi_norm s _)

theorem gammaAt_weighted_summable (i : Fin 4) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    Summable (fun n : ℕ × ℕ => ‖gammaAt i s n‖ * pairWeight ρ n) :=
  gamma_weighted_summable _ ρ hρ0 hρ (fun j => hs (Equiv.swap 0 i j))

theorem gammaAt_weighted_bound (i : Fin 4) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    (∑' n : ℕ × ℕ, ‖gammaAt i s n‖ * pairWeight ρ n) ≤ globalBound ρ :=
  gamma_weighted_bound _ ρ hρ0 hρ (fun j => hs (Equiv.swap 0 i j))

theorem gammaAt_lipschitz_zero (i : Fin 4) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ : ρ < 1/4) (hs : ‖s‖ ≤ ρ/2) :
    (∑' n : ℕ × ℕ, ‖gammaAt i s n - gammaAt i (fun _ => 0) n‖) ≤
      (2 * uniformBound ρ / ρ) * ‖s‖ := by
  have H := gamma_lipschitz_zero (reindexShifts i s) ρ hρ0 hρ
    ((reindexShifts_norm_le i s).trans hs)
  change (∑' n, ‖gamma (reindexShifts i s) n - gamma (fun _ => 0) n‖) ≤ _
  exact H.trans (mul_le_mul_of_nonneg_left (reindexShifts_norm_le i s) (by
    unfold uniformBound
    positivity))

theorem restDirichletAt_euler (i : Fin 4) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : -ρ ≤ u.re) (hv : -ρ ≤ v.re) :
    HasProd (fun p : Nat.Primes =>
      primeRest p.val (reindexShifts i s) ((p.val : ℂ)^(-u)) ((p.val : ℂ)^(-v)))
      (restDirichletAt i s u v) :=
  restDirichlet_euler_hasProd _ ρ hρ0 hρ (fun j => hs (Equiv.swap 0 i j)) u v hu hv

theorem restDirichletAt_zero : ∀ i : Fin 4,
    restDirichletAt i (fun _ => 0) 0 0 = arithmeticConstant := by
  intro i
  exact zero_shift_global_factor

theorem global_rest_chapter_complete (ρ : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1/4)
    (s : Fin 4 → ℂ) (hs : ‖s‖ ≤ ρ/2) :
    (∀ i : Fin 4,
      Summable (fun n : ℕ × ℕ => ‖gammaAt i s n‖ * pairWeight ρ n) ∧
      (∑' n : ℕ × ℕ, ‖gammaAt i s n‖ * pairWeight ρ n) ≤ globalBound ρ ∧
      (∑' n : ℕ × ℕ, ‖gammaAt i s n - gammaAt i (fun _ => 0) n‖) ≤
        (2 * uniformBound ρ / ρ) * ‖s‖ ∧
      (∀ u v : ℂ, -ρ ≤ u.re → -ρ ≤ v.re →
        HasProd (fun p : Nat.Primes =>
          primeRest p.val (reindexShifts i s) ((p.val : ℂ)^(-u)) ((p.val : ℂ)^(-v)))
          (restDirichletAt i s u v))) ∧
    (∀ i : Fin 4, restDirichletAt i (fun _ => 0) 0 0 = arithmeticConstant) := by
  have HS (j : Fin 4) : ‖s j‖ ≤ ρ := (norm_le_pi_norm s j).trans (hs.trans (by linarith))
  refine ⟨?_, restDirichletAt_zero⟩
  intro i
  exact ⟨gammaAt_weighted_summable i s ρ hρ0.le hρ HS,
    gammaAt_weighted_bound i s ρ hρ0.le hρ HS,
    gammaAt_lipschitz_zero i s ρ hρ0 hρ hs,
    fun u v hu hv => restDirichletAt_euler i s ρ hρ0.le hρ HS u v hu hv⟩

end
end Sechstmoment.Source.NoDPGlobalRest
