import Sechstmoment.Arithmetic.Euler.FourL.FinitePolynomial
import Sechstmoment.Arithmetic.Euler.FourL.FourLSeries

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators
noncomputable section

theorem correctionAF_LSeriesHasSum (d : ℕ) (hd : d ≠ 0) (s : Fin 4 → ℂ) (u : ℕ →* ℂ) (z : ℂ) :
    LSeriesHasSum (correctionAF d s u) z (arithmeticCorrection d s u z) := by
  have H := correctionAF_hasSum d hd s u z
  change HasSum _ _
  convert H using 1
  funext n
  exact LSeries.term_def₀ ArithmeticFunction.map_zero z n

theorem shiftedAF_LSeriesHasSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (d : ℕ) (hd : d ≠ 0) (s : Fin 4 → ℂ) (z : ℂ) (H : ∀ j, 1 < (z+s j).re) :
    LSeriesHasSum (shiftedAF d s (characterHom χ)) z
      (arithmeticCorrection d s (characterHom χ) z * fourL χ s z) := by
  rw [shiftedAF_factorization d hd]
  exact ArithmeticFunction.LSeriesHasSum_mul (correctionAF_LSeriesHasSum d hd s (characterHom χ) z)
    (twisted_four_hasSum χ s z H)

def shiftedTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ) (s : Fin 4 → ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  fourAF s (d*n) * χ n * (n:ℂ)^(-z)

def shiftedDirichlet {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ) (s : Fin 4 → ℂ) (z : ℂ) : ℂ :=
  ∑' n, shiftedTerm χ d s z n

def eulerCorrection {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ) (s : Fin 4 → ℂ) (z : ℂ) : ℂ :=
  arithmeticCorrection d s (characterHom χ) z

theorem shiftedTerm_eq_LSeries {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ)
    (s : Fin 4 → ℂ) (z : ℂ) (n : ℕ) :
    shiftedTerm χ d s z n = LSeries.term (shiftedAF d s (characterHom χ)) z n := by
  by_cases hn : n = 0
  · simp [hn,shiftedTerm]
  rw [LSeries.term_def₀ ArithmeticFunction.map_zero]
  simp [shiftedTerm,shiftedAF,hn,characterHom]

theorem shiftedTerm_hasSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ) (hd : d ≠ 0)
    (s : Fin 4 → ℂ) (z : ℂ) (H : ∀ j, 1 < (z+s j).re) :
    HasSum (shiftedTerm χ d s z) (eulerCorrection χ d s z *
      ∏ j : Fin 4, DirichletCharacter.LFunction χ (z+s j)) := by
  rw [← fourL_eq_product]
  have h := shiftedAF_LSeriesHasSum χ d hd s z H
  rw [show shiftedTerm χ d s z = LSeries.term (shiftedAF d s (characterHom χ)) z from
    funext (shiftedTerm_eq_LSeries χ d s z)]
  exact h

theorem shiftedTerm_absolute {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ) (hd : d ≠ 0)
    (s : Fin 4 → ℂ) (z : ℂ) (H : ∀ j, 1 < (z+s j).re) :
    Summable (fun n => ‖shiftedTerm χ d s z n‖) :=
  (shiftedTerm_hasSum χ d hd s z H).summable.norm

theorem global_L_factorization {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ) (hd : d ≠ 0)
    (s : Fin 4 → ℂ) (z : ℂ) (H : ∀ j, 1 < (z+s j).re) :
    shiftedDirichlet χ d s z = eulerCorrection χ d s z *
      ∏ j : Fin 4, DirichletCharacter.LFunction χ (z+s j) :=
  (shiftedTerm_hasSum χ d hd s z H).tsum_eq

theorem eulerCorrection_entire {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ) (s : Fin 4 → ℂ) :
    Differentiable ℂ (eulerCorrection χ d s) := arithmeticCorrection_entire d s (characterHom χ)

theorem eulerCorrection_ramified {q : ℕ} (χ : DirichletCharacter ℂ q) (d : ℕ) (s : Fin 4 → ℂ)
    (H : ∀ p ∈ d.primeFactors, χ p = 0) (z : ℂ) :
    eulerCorrection χ d s z = fourAF s d := by
  rw [eulerCorrection,arithmeticCorrection_ramified d s (characterHom χ) H,
    ← fourAF_eq_shiftedCoeff]

end
end Sechstmoment.Source.NoDPGlobalLFactorization
