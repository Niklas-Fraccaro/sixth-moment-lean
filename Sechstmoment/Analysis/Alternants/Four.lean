import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Sechstmoment.Analysis.Simplex.Exponential
import Std

/-! The actual four-by-four exponential determinant of (3.5).
Its expansion along the first two columns contains six signed two-by-two
minor products. The Vandermonde factor is the manuscript's convention. -/

namespace Sechstmoment
open scoped BigOperators

set_option maxHeartbeats 0

def matrixMinorTwo {R : Type*} [CommRing R]
    (M : Matrix (Fin 4) (Fin 4) R) (i j k l : Fin 4) : R :=
  M i k * M j l - M i l * M j k

/-- Laplace expansion along columns zero and one, with all six signs. -/
theorem determinant_four_six_minors {R : Type*} [CommRing R]
    (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      matrixMinorTwo M 0 1 0 1 * matrixMinorTwo M 2 3 2 3 -
      matrixMinorTwo M 0 2 0 1 * matrixMinorTwo M 1 3 2 3 +
      matrixMinorTwo M 0 3 0 1 * matrixMinorTwo M 1 2 2 3 +
      matrixMinorTwo M 1 2 0 1 * matrixMinorTwo M 0 3 2 3 -
      matrixMinorTwo M 1 3 0 1 * matrixMinorTwo M 0 2 2 3 +
      matrixMinorTwo M 2 3 0 1 * matrixMinorTwo M 0 1 2 3 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove, matrixMinorTwo]
  ring

noncomputable def fourVandermonde (q : Fin 4 → ℂ) : ℂ :=
  (q 1-q 0)*(q 2-q 0)*(q 3-q 0)*(q 2-q 1)*(q 3-q 1)*(q 3-q 2)

theorem fourVandermonde_eq_indexed (q : Fin 4 → ℂ) :
    fourVandermonde q =
      ∏ i : Fin 4, ∏ j : Fin 4, (if i < j then q j-q i else 1) := by
  norm_num [fourVandermonde, Fin.prod_univ_succ]
  ring

noncomputable def expAlternantMatrix (x rho : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => Complex.exp (x i*rho j)

noncomputable def exponentialAlternant (x rho : Fin 4 → ℂ) : ℂ :=
  Complex.exp (x 0+x 1) * (expAlternantMatrix x rho).det / fourVandermonde x

/-- The six products of actual exponential minors, including the outer factor. -/
theorem exponentialAlternant_six_minors (x rho : Fin 4 → ℂ) :
    exponentialAlternant x rho = Complex.exp (x 0+x 1) *
      (matrixMinorTwo (expAlternantMatrix x rho) 0 1 0 1 *
          matrixMinorTwo (expAlternantMatrix x rho) 2 3 2 3 -
        matrixMinorTwo (expAlternantMatrix x rho) 0 2 0 1 *
          matrixMinorTwo (expAlternantMatrix x rho) 1 3 2 3 +
        matrixMinorTwo (expAlternantMatrix x rho) 0 3 0 1 *
          matrixMinorTwo (expAlternantMatrix x rho) 1 2 2 3 +
        matrixMinorTwo (expAlternantMatrix x rho) 1 2 0 1 *
          matrixMinorTwo (expAlternantMatrix x rho) 0 3 2 3 -
        matrixMinorTwo (expAlternantMatrix x rho) 1 3 0 1 *
          matrixMinorTwo (expAlternantMatrix x rho) 0 2 2 3 +
        matrixMinorTwo (expAlternantMatrix x rho) 2 3 0 1 *
          matrixMinorTwo (expAlternantMatrix x rho) 0 1 2 3) /
        fourVandermonde x := by
  unfold exponentialAlternant
  rw [determinant_four_six_minors]

end Sechstmoment
