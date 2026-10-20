import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformConvergence
import SixthMoment.Analysis.Harmonic.Scaling
import SixthMoment.Numerator.V.DP.DPNormalization
import Std


namespace SixthMoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set Polynomial
open scoped BigOperators Topology
noncomputable section

theorem polynomialSimplexIntegral_eq_dpNormalizedTriple {η : ℝ} (hη : η ≠ 0)
    (P : ℝ[X]) (ν₁ ν₂ ν₃ : ℂ) :
    polynomialSimplexIntegral η P ν₁ ν₂ ν₃ =
      (η:ℂ)^3*dpNormalizedTriple η P ν₁ (-ν₂) (-ν₃) := by
  have hs := continuousIter_scale η 1 [ν₁,ν₂,ν₃] (reversedPolynomial η P)
  simp only [mul_one,List.length_cons,List.length_nil,List.map_cons,List.map_nil] at hs
  rw [polynomialSimplexIntegral,hs]
  have hp : (fun y => reversedPolynomial η P (η*y)) = fun y => ((P.eval y:ℝ):ℂ) := by
    funext y
    simp only [reversedPolynomial,mul_div_cancel_left₀ y hη]
  rw [hp]
  congr 1
  change (∫ x in 0..(1:ℝ),
    (∫ y in 0..(1-x),
      (∫ z in 0..(1-x-y), ((P.eval (1-x-y-z):ℝ):ℂ)*expKernel ((η:ℂ)*ν₃) z)*
        expKernel ((η:ℂ)*ν₂) y)*expKernel ((η:ℂ)*ν₁) x) = _
  simp_rw [← intervalIntegral.integral_mul_const]
  unfold dpNormalizedTriple
  apply intervalIntegral.integral_congr
  intro x _
  apply intervalIntegral.integral_congr
  intro y _
  apply intervalIntegral.integral_congr
  intro z _
  dsimp only
  unfold expKernel
  rw [mul_assoc,mul_assoc,← Complex.exp_add,← Complex.exp_add]
  congr 2
  ring

end
end SixthMoment.Source.NoDPHarmonic
