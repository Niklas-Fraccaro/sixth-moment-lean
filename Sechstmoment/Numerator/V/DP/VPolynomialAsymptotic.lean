import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Star
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
import Sechstmoment.Numerator.V.Projection
import Std

namespace Sechstmoment
open Complex MeasureTheory Set Metric Filter Polynomial
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1600000

namespace Source

theorem vPolynomialRawMixedMoment_tendsto (N : ℕ) (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (P Q p : ℝ[X]) (hp : p.natDegree≤N)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T:ℝ => vPolynomialRawMixedMoment T p
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ/
        ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x:ℝ,(Φ x:ℂ))*
        finiteDifferentialOperator N (fun j=>(p.coeff j.val:ℂ))
          (vReflectedPolynomialJ η P Q) 0)) := by
  have ht := vPolynomialMixedGenerator_operator_tendsto N (fun j=>(p.coeff j.val:ℂ))
    hsource η hη hηu P Q Φ hΦ 0 (by norm_num)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  rw [vPolynomialRawMixedMoment_eq_finiteDifferentialOperator N hT hL η η p hp
    _ _ Φ (zeroExtendedPolynomialProfile_zero_above η P)
      (zeroExtendedPolynomialProfile_zero_above η Q) hΦ]

theorem vPolynomialProjectedMixedMoment_tendsto (N : ℕ) (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (P Q p : ℝ[X]) (hp : p.natDegree≤N)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T:ℝ => vPolynomialProjectedMixedMoment T p
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ/
        ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 (Complex.ofReal (((arithmeticFactor:ℂ)*(∫ x:ℝ,(Φ x:ℂ))*
        finiteDifferentialOperator N (fun j=>(p.coeff j.val:ℂ))
          (vReflectedPolynomialJ η P Q) 0).re))) := by
  have ht := vPolynomialRawMixedMoment_tendsto N hsource η hη hηu P Q p hp Φ hΦ
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  apply hc.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  exact (vPolynomialProjectedMixedMoment_normalized_eq_real hT hL η P Q p Φ hΦ).symm

end Source
end
end Sechstmoment
