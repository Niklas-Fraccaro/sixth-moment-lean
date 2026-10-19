import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Instances.Matrix
import Sechstmoment.Analysis.Alternants.Holomorphy
import Sechstmoment.Numerator.Kernels.Nodes
import Sechstmoment.Numerator.Polar.General.Holomorphy
import Std

/-! Holomorphic continuation of the exponential alternant through all source
collisions.  Its derivatives are obtained from the defining compact integrals. -/

namespace Sechstmoment
open Filter MeasureTheory Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1000000

attribute [local irreducible] simplexExpGenerator simplexTriangleExpIntegral expFirstSlope

attribute [local irreducible] expNewtonMatrix

theorem numeratorRho_regularized_u_slice (u v : ℝ) (z : ℂ) :
    exponentialAlternantRegularized (![0,0,z,0]) (numeratorRho u v) =
      (numeratorP u v:ℂ)*simplexExpGenerator (numeratorRho u v) z := by
  rw [exponentialAlternantRegularized_u_slice,numeratorRho_vandermonde]
  ring

end
end Sechstmoment
