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
import Sechstmoment.Analysis.Alternants.Confluent
import Sechstmoment.Numerator.Kernels.Nodes
import Std

/-! The genuine confluent exponential determinant with derivative rows
1, rho and rho^2. This identifies the resulting determinant with the simplex
generator; the limiting operation in the original four shift variables is
a separate analytic obligation. -/

namespace Sechstmoment
open scoped BigOperators

set_option maxHeartbeats 0

theorem numeratorRho_confluent_generator (u v : ℝ) (z : ℂ)
    (hq : Function.Injective (numeratorRho u v)) (hz : z ≠ 0) :
    confluentExpGenerator (numeratorRho u v) z =
      (numeratorP u v : ℂ) * simplexExpGenerator (numeratorRho u v) z := by
  rw [confluentExpGenerator_eq_simplex _ _ hq hz, numeratorRho_vandermonde]
  ring

end Sechstmoment
