import Sechstmoment.Analysis.Mellin.SmoothMellinEntire
import Sechstmoment.Arithmetic.Euler.FourL.Continuation

/-! An entire numerator for the actual principal-character Mellin integrand.
The four actual L-functions are retained, with their poles removed by the
standard regularized trivial-character L-function. -/

namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def principalMellinNumerator (q : ℕ) [NeZero q] (d : ℕ) (w : ℝ → ℂ)
    (β : Fin 4 → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  mellin w s*(x:ℂ)^s*eulerCorrection (1 : DirichletCharacter ℂ q) d β s*
    ∏ j : Fin 4, DirichletCharacter.LFunctionTrivChar₁ q (s+β j)

theorem principalMellinNumerator_entire {w : ℝ → ℂ} (hw : Continuous w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) (q : ℕ) [NeZero q] (d : ℕ)
    (β : Fin 4 → ℂ) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (principalMellinNumerator q d w β x) := by
  have hxC : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hp : Differentiable ℂ (fun s : ℂ => (x:ℂ)^s) := by
    have he : (fun s : ℂ => (x:ℂ)^s) = fun s : ℂ => Complex.exp (Complex.log (x:ℂ)*s) :=
      funext (Complex.cpow_def_of_ne_zero hxC)
    rw [he]
    fun_prop
  have hprod : Differentiable ℂ (fun s : ℂ =>
      ∏ j : Fin 4, DirichletCharacter.LFunctionTrivChar₁ q (s+β j)) := by
    apply Differentiable.fun_finsetProd
    intro j _
    exact (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).comp
      (differentiable_id.add_const (β j))
  exact (((compact_dyadic_mellin_entire hw hws).mul hp).mul
    (eulerCorrection_entire (1 : DirichletCharacter ℂ q) d β)).mul hprod

theorem principalMellinNumerator_div_poles (q : ℕ) [NeZero q] (d : ℕ)
    (w : ℝ → ℂ) (β : Fin 4 → ℂ) (x : ℝ) (s : ℂ)
    (hs : ∀ j, s ≠ 1-β j) :
    principalMellinNumerator q d w β x s/(∏ j : Fin 4, (s-(1-β j))) =
      mellin w s*(x:ℂ)^s*shiftedContinuation (1 : DirichletCharacter ℂ q) d β s := by
  have hne (j : Fin 4) : s+β j ≠ 1 := by
    intro he
    exact hs j (by linear_combination he)
  have hQ : (∏ j : Fin 4, (s-(1-β j))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => sub_ne_zero.mpr (hs j))
  have hreg (j : Fin 4) : DirichletCharacter.LFunctionTrivChar₁ q (s+β j) =
      (s-(1-β j))*(1 : DirichletCharacter ℂ q).LFunction (s+β j) := by
    rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne (hne j)]
    congr 1
    ring
  unfold principalMellinNumerator
  simp_rw [hreg]
  rw [Finset.prod_mul_distrib]
  calc
    _ = (mellin w s*(x:ℂ)^s*eulerCorrection (1 : DirichletCharacter ℂ q) d β s*
        (∏ j : Fin 4, (1 : DirichletCharacter ℂ q).LFunction (s+β j)))*
          (∏ j : Fin 4, (s-(1-β j)))/(∏ j : Fin 4, (s-(1-β j))) := by ring
    _ = mellin w s*(x:ℂ)^s*eulerCorrection (1 : DirichletCharacter ℂ q) d β s*
        (∏ j : Fin 4, (1 : DirichletCharacter ℂ q).LFunction (s+β j)) :=
      mul_div_cancel_right₀ _ hQ
    _ = _ := by rw [shiftedContinuation]; ring

end
end Sechstmoment.Source.NoDPGlobalLFactorization
