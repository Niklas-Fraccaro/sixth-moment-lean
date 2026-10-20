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
import Sechstmoment.Analysis.Harmonic.PolynomialProfile
import Std


namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set Polynomial
open scoped BigOperators Topology
noncomputable section

theorem continuousStep_const_mul (ν c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    continuousStep ν (fun x => c*f x) t = c*continuousStep ν f t := by
  unfold continuousStep
  simp_rw [mul_assoc]
  exact intervalIntegral.integral_const_mul c _

theorem continuousStep_scale (c t : ℝ) (ν : ℂ) (f : ℝ → ℂ) :
    continuousStep ν f (c*t) =
      (c:ℂ)*continuousStep ((c:ℂ)*ν) (fun y => f (c*y)) t := by
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (a := (0:ℝ)) (b := t) (fun x => f (c*t-x)*expKernel ν x) c
  simp only [mul_zero,Complex.real_smul] at hs
  change (∫ x in 0..c*t, f (c*t-x)*expKernel ν x) = _
  rw [← hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [show c*t-c*x = c*(t-x) by ring]
  congr 1
  unfold expKernel
  congr 1
  push_cast
  ring

theorem continuousIter_scale (c t : ℝ) (νs : List ℂ) (f : ℝ → ℂ) :
    continuousIter νs f (c*t) = (c:ℂ)^νs.length*
      continuousIter (νs.map (fun ν => (c:ℂ)*ν)) (fun y => f (c*y)) t := by
  induction νs generalizing t with
  | nil => simp only [continuousIter,List.length_nil,List.map_nil,pow_zero,one_mul]
  | cons ν νs ih =>
    change continuousStep ν (continuousIter νs f) (c*t) = _
    rw [continuousStep_scale,show (fun y => continuousIter νs f (c*y)) =
      (fun y => (c:ℂ)^νs.length*
        continuousIter (νs.map (fun z => (c:ℂ)*z)) (fun x => f (c*x)) y) from funext ih,
      continuousStep_const_mul]
    simp only [List.length_cons,List.map_cons,continuousIter,pow_succ]
    ring

end
end Sechstmoment.Source.NoDPHarmonic
