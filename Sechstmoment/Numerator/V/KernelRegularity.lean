import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Sechstmoment.Numerator.V.DP.DPAllPositiveBilinear
import Sechstmoment.Numerator.V.DP.PolarDerivatives
import Std


namespace Sechstmoment
open Complex MeasureTheory Set Metric Filter
open scoped Topology BigOperators

set_option maxHeartbeats 1000000
noncomputable section

namespace Source

private theorem square_polar_J_analyticAt (η : ℝ) (hη : 0 ≤ η)
    (P : Polynomial ℝ) (z : ℂ) (hz : ‖z‖<4) :
    AnalyticAt ℂ (polarPolynomialJ η P) z := by
  have hg : DifferentiableOn ℂ (fun z => dpAllPositiveRegularKernel η P (dpCoincidentShifts z))
      (ball 0 4) :=
    (dpAllPositiveRegularKernel_differentiableOn hη P).comp
      dpCoincidentShifts_differentiable.differentiableOn (by
        intro z hz
        apply dpCoincidentShifts_mem_polydisc
        exact (show ‖z‖<4 by simpa only [mem_ball,dist_zero_right] using hz).le)
  have hzball : z ∈ ball (0:ℂ) 4 := by simpa only [mem_ball,dist_zero_right] using hz
  have he : polarPolynomialJ η P =ᶠ[𝓝 z]
      (fun z => dpAllPositiveRegularKernel η P (dpCoincidentShifts z)) := by
    filter_upwards [isOpen_ball.mem_nhds hzball] with w hw
    symm
    apply dpAllPositiveRegularKernel_coincident
    have hw4 : ‖w‖<4 := by simpa only [mem_ball,dist_zero_right] using hw
    linarith
  exact (hg.analyticAt (isOpen_ball.mem_nhds hzball)).congr he.symm

theorem polarPolynomialBilinearJ_analyticAt (η : ℝ) (hη : 0 ≤ η)
    (P Q : Polynomial ℝ) (z : ℂ) (hz : ‖z‖<4) :
    AnalyticAt ℂ (polarPolynomialBilinearJ η P Q) z := by
  have h : AnalyticAt ℂ (fun w => (1/4:ℂ)*
      (polarPolynomialJ η (P+Q) w-polarPolynomialJ η (P-Q) w)) z :=
    analyticAt_const.mul ((square_polar_J_analyticAt η hη (P+Q) z hz).sub
      (square_polar_J_analyticAt η hη (P-Q) z hz))
  exact h.congr (Filter.Eventually.of_forall (fun w =>
    (polarPolynomialBilinearJ_polarization η P Q w).symm))

theorem polarPolynomialBilinearJ_iteratedDeriv_polarization (n : ℕ)
    (η : ℝ) (hη : 0 ≤ η) (P Q : Polynomial ℝ) (z : ℂ) (hz : ‖z‖<4) :
    iteratedDeriv n (polarPolynomialBilinearJ η P Q) z =
      (1/4:ℂ)*(iteratedDeriv n (polarPolynomialJ η (P+Q)) z-
        iteratedDeriv n (polarPolynomialJ η (P-Q)) z) := by
  have he : polarPolynomialBilinearJ η P Q =
      (fun w => (1/4:ℂ)*(polarPolynomialJ η (P+Q) w-polarPolynomialJ η (P-Q) w)) :=
    funext (polarPolynomialBilinearJ_polarization η P Q)
  rw [he,iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sub ((square_polar_J_analyticAt η hη (P+Q) z hz).contDiffAt (n := n))
      ((square_polar_J_analyticAt η hη (P-Q) z hz).contDiffAt (n := n))]

end Source
end
end Sechstmoment
