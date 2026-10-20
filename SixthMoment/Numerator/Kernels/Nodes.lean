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
import SixthMoment.Analysis.Alternants.Four
import SixthMoment.Numerator.Kernels.Polynomial
import Std


namespace SixthMoment
open scoped BigOperators

set_option maxHeartbeats 0

noncomputable def numeratorRho (u v : ℝ) : Fin 4 → ℂ :=
  ![-1, (v:ℂ)-1, -(u:ℂ), 0]

theorem numeratorRho_vandermonde (u v : ℝ) :
    fourVandermonde (numeratorRho u v) = 12 * (numeratorP u v : ℂ) := by
  norm_num [fourVandermonde, numeratorRho, numeratorP]
  ring

theorem numeratorRho_divided_difference (u v : ℝ) (z : ℂ)
    (hq : Function.Injective (numeratorRho u v)) (hz : z ≠ 0) :
    fourVandermonde (numeratorRho u v) / (2*z^3) *
      (∑ j : Fin 4, Complex.exp (z*numeratorRho u v j) /
        (∏ k ∈ (Finset.univ : Finset (Fin 4)).erase j,
          (numeratorRho u v j-numeratorRho u v k))) =
      (numeratorP u v : ℂ) * simplexExpGenerator (numeratorRho u v) z := by
  rw [numeratorRho_vandermonde, simplexExpGenerator_distinct _ _ hq hz]
  ring

end SixthMoment
