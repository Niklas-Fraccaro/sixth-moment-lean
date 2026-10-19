import Sechstmoment.Arithmetic.Euler.FourL.GlobalIdentity
import Sechstmoment.Arithmetic.Euler.FourL.Subpower

/-! No new poles, and height-uniform correction bounds for genuinely logarithmically small shifts. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section

def shiftedContinuation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ)
    (s : Fin 4 → ℂ) (z : ℂ) : ℂ := eulerCorrection χ d s z *
      ∏ j : Fin 4, DirichletCharacter.LFunction χ (z+s j)

theorem continuation_eq_series {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (d : ℕ) (hd : d ≠ 0) (s : Fin 4 → ℂ) (z : ℂ) (H : ∀ j, 1 < (z+s j).re) :
    shiftedContinuation χ d s z = shiftedDirichlet χ d s z :=
  (global_L_factorization χ d hd s z H).symm

theorem continuation_differentiableAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (d : ℕ) (s : Fin 4 → ℂ) (z : ℂ) (H : ∀ j, z+s j ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (shiftedContinuation χ d s) z := by
  apply (eulerCorrection_entire χ d s z).mul
  apply DifferentiableAt.fun_finsetProd
  intro j _
  exact (DirichletCharacter.differentiableAt_LFunction χ (z+s j) (H j)).comp z
    (differentiableAt_id.add_const (s j))

theorem nonprincipal_continuation_entire {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (d : ℕ) (s : Fin 4 → ℂ) : Differentiable ℂ (shiftedContinuation χ d s) :=
  fun z => continuation_differentiableAt χ d s z (fun _ => Or.inr hχ)

theorem continuation_no_new_poles {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (d : ℕ) (s : Fin 4 → ℂ) :
    DifferentiableOn ℂ (shiftedContinuation χ d s) {z | ∀ j, z ≠ 1-s j} := by
  intro z hz
  apply (continuation_differentiableAt χ d s z _).differentiableWithinAt
  intro j
  left
  intro H
  exact hz j (by linear_combination H)

theorem eulerCorrection_subpower (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ _ : NeZero q, ∀ χ : DirichletCharacter ℂ q,
      ∀ d : ℕ, d ≠ 0 → ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ min κ (ε/2)) →
        ∀ z : ℂ, κ ≤ z.re → ‖eulerCorrection χ d s z‖ ≤ C*(d:ℝ)^ε := by
  obtain ⟨C,hC,H⟩ := arithmeticCorrection_subpower κ ε hκ hε
  refine ⟨C,hC,?_⟩
  intro q hq χ d hd s hs z hz
  let : NeZero q := hq
  exact H d hd s hs (characterHom χ) (fun p _ => χ.norm_le_one (p : ZMod q)) z hz

/-- The precise uniformity needed for shifts bounded by R / log T in the PDF. -/
theorem eulerCorrection_log_shifts (κ ε R : ℝ) (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ q : ℕ, ∀ _ : NeZero q, ∀ χ : DirichletCharacter ℂ q, ∀ d : ℕ, d ≠ 0 →
        ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ R / Real.log T) →
          ∀ z : ℂ, κ ≤ z.re → ‖eulerCorrection χ d s z‖ ≤ C*(d:ℝ)^ε := by
  obtain ⟨C,hC,H⟩ := eulerCorrection_subpower κ ε hκ hε
  let δ := min κ (ε/2)
  have hδ : 0 < δ := lt_min hκ (by linarith)
  refine ⟨C,hC,max (Real.exp (R/δ)) 2,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro T hT q hq χ d hd s hs z hz
  have hlog : 0 < Real.log T := Real.log_pos (by have := (le_max_right (Real.exp (R/δ)) 2).trans hT; linarith)
  have hRT : R/δ ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos (R/δ)) ((le_max_left _ _).trans hT)
    simpa only [Real.log_exp] using h
  have hsmall : R / Real.log T ≤ δ := by
    apply (div_le_iff₀ hlog).mpr
    have H := (div_le_iff₀ hδ).mp hRT
    nlinarith
  exact H q hq χ d hd s (fun j => (hs j).trans hsmall) z hz

end
end Sechstmoment.Source.NoDPGlobalLFactorization
