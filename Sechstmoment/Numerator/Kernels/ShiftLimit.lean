import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.Topology.Instances.Matrix
import Sechstmoment.Analysis.Alternants.ShiftLimit
import Sechstmoment.Numerator.Kernels.Confluent
import Std


namespace Sechstmoment
open Filter
open scoped Topology BigOperators

set_option maxHeartbeats 0

theorem numeratorRho_joint_shift_limit (u v : ℝ) (z : ℂ)
    (hq : Function.Injective (numeratorRho u v)) (hz : z ≠ 0) :
    Tendsto (fun x : Fin 4 → ℂ => exponentialAlternant x (numeratorRho u v))
      (𝓝[{x : Fin 4 → ℂ | Function.Injective x}] (![0,0,z,0]))
      (𝓝 ((numeratorP u v : ℂ)*simplexExpGenerator (numeratorRho u v) z)) := by
  simpa only [numeratorRho_confluent_generator u v z hq hz] using
    exponentialAlternant_joint_shift_limit (numeratorRho u v) z hz

end Sechstmoment
