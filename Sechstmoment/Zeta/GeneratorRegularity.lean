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
import Sechstmoment.Analysis.Integration.ComplexParameter
import Sechstmoment.Zeta.Centering.Exact
import Std

namespace Sechstmoment
open Complex MeasureTheory Set Metric Filter Polynomial
open scoped Topology BigOperators ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000

theorem riemannZeta_iteratedDeriv_analyticAt (n : ℕ) (s : ℂ) (hs : s ≠ 1) :
    AnalyticAt ℂ (iteratedDeriv n riemannZeta) s := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using
      (analyticOn_riemannZeta s (by simpa using hs))
  | succ n hn => simpa only [iteratedDeriv_succ] using hn.deriv

theorem riemannZeta_iteratedDeriv_conj (n : ℕ) (s : ℂ) :
    iteratedDeriv n riemannZeta (conj s) = conj (iteratedDeriv n riemannZeta s) := by
  induction n generalizing s with
  | zero => simpa only [iteratedDeriv_zero] using riemannZeta_conj s
  | succ n hn =>
    have he : (fun z => conj (iteratedDeriv n riemannZeta (conj z))) =
        iteratedDeriv n riemannZeta := by
      funext z
      rw [hn, conj_conj]
    have he' : (conj ∘ iteratedDeriv n riemannZeta ∘ conj) =
        iteratedDeriv n riemannZeta := he
    have hd := congrFun (deriv_conj_conj (f := iteratedDeriv n riemannZeta)) s
    rw [he'] at hd
    simp only [Function.comp_apply] at hd
    rw [← iteratedDeriv_succ] at hd
    have hh := congrArg conj hd
    simpa only [conj_conj] using hh.symm

theorem centeredZetaDerivative_conj (T : ℝ) (n : ℕ) (s : ℂ) :
    centeredZetaDerivative T n (conj s) = conj (centeredZetaDerivative T n s) := by
  simp only [centeredZetaDerivative, map_sum, map_mul, map_div₀, map_pow,
    conj_natCast, conj_ofReal, map_one, map_ofNat, riemannZeta_iteratedDeriv_conj]

theorem zetaCp_conj (T t : ℝ) (p : ℝ[X]) :
    star (zetaCp T t p) = zetaPolynomialDerivative T p (1-criticalLinePoint t) := by
  rw [criticalLinePoint_one_sub]
  change conj (zetaPolynomialDerivative T p (criticalLinePoint t)) = _
  unfold zetaPolynomialDerivative
  rw [Polynomial.sum_def, Polynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_mul,conj_ofReal,← centeredZetaDerivative_conj]
  rfl

theorem iteratedDeriv_shiftedZetaGenerator_at {T : ℝ} (hT : 1<T)
    (s z : ℂ) (n : ℕ) (hs : s+z/(Real.log T:ℂ) ≠ 1) :
    iteratedDeriv n (shiftedZetaGenerator T s) z =
      Complex.exp (z/2)*centeredZetaDerivative T n (s+z/(Real.log T:ℂ)) := by
  have he : (fun w => shiftedZetaGenerator T s (z+w)) =
      (fun w => Complex.exp (z/2)*shiftedZetaGenerator T (s+z/(Real.log T:ℂ)) w) := by
    funext w
    unfold shiftedZetaGenerator
    rw [show (z+w)/2=z/2+w/2 by ring,Complex.exp_add]
    rw [mul_assoc]
    congr 2
    ring
  have hd := congrArg (fun f : ℂ→ℂ => iteratedDeriv n f 0) he
  rw [iteratedDeriv_comp_const_add,iteratedDeriv_const_mul_field,
    iteratedDeriv_shiftedZetaGenerator_of_one_lt T _ n hT hs] at hd
  simpa only [add_zero] using hd

theorem centeredZetaDerivative_analyticAt (T : ℝ) (n : ℕ) (s : ℂ) (hs : s≠1) :
    AnalyticAt ℂ (centeredZetaDerivative T n) s := by
  unfold centeredZetaDerivative
  apply Finset.analyticAt_fun_sum
  intro j _
  exact analyticAt_const.mul (riemannZeta_iteratedDeriv_analyticAt j s hs)

private theorem minus_shift_ne_one {T : ℝ} (hT : 1<T) (t : ℝ) (z : ℂ)
    (hz : 2*‖z‖<Real.log T) : 1-criticalLinePoint t+z/(Real.log T:ℂ) ≠ 1 := by
  have hh := centeringShift_mem_strip (Real.log_pos hT) (-t) z hz
  have he : centeringShift T (-t) z = 1-criticalLinePoint t+z/(Real.log T:ℂ) := by
    unfold centeringShift criticalLinePoint
    push_cast
    ring
  rw [he] at hh
  intro h
  rw [h] at hh
  norm_num at hh

theorem zetaCMinus_iteratedDeriv_analyticAt (n : ℕ) {T : ℝ} (hT : 1<T)
    (t : ℝ) (z : ℂ) (hz : 2*‖z‖<Real.log T) :
    AnalyticAt ℂ (iteratedDeriv n (zetaCMinus T t)) z := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    unfold zetaCMinus shiftedZetaGenerator
    exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ=>Complex.exp (z/2)) z).mul
      ((analyticOn_riemannZeta _ (by simpa using minus_shift_ne_one hT t z hz)).comp
        (f := fun w:ℂ=>1-criticalLinePoint t+w/(Real.log T:ℂ)) (by fun_prop))
  | succ n hn => simpa only [iteratedDeriv_succ] using hn.deriv

theorem zetaCMinus_iteratedDeriv_joint_continuous (n : ℕ) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) :
    Continuous (fun p : ball (0:ℂ) 4 × ℝ =>
      iteratedDeriv n (zetaCMinus T p.2) p.1.1) := by
  have hp (p : ball (0:ℂ) 4 × ℝ) : 2*‖p.1.1‖<Real.log T := by
    have hn : ‖p.1.1‖<4 := by simpa only [mem_ball,dist_zero_right] using p.1.2
    linarith
  have he (p : ball (0:ℂ) 4 × ℝ) :
      iteratedDeriv n (zetaCMinus T p.2) p.1.1 =
        Complex.exp (p.1.1/2)*centeredZetaDerivative T n
          (1-criticalLinePoint p.2+p.1.1/(Real.log T:ℂ)) :=
    iteratedDeriv_shiftedZetaGenerator_at hT _ _ n
      (minus_shift_ne_one hT p.2 p.1.1 (hp p))
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro p
  have hs : Continuous (fun p : ball (0:ℂ) 4 × ℝ =>
      1-criticalLinePoint p.2+p.1.1/(Real.log T:ℂ)) := by
    unfold criticalLinePoint
    fun_prop
  exact (by fun_prop : ContinuousAt (fun p : ball (0:ℂ) 4 × ℝ=>
      Complex.exp (p.1.1/2)) p).mul
    ((centeredZetaDerivative_analyticAt T n _
      (minus_shift_ne_one hT p.2 p.1.1 (hp p))).continuousAt.comp (f := fun p : ball (0:ℂ) 4 × ℝ =>
      1-criticalLinePoint p.2+p.1.1/(Real.log T:ℂ)) hs.continuousAt)

end
end Sechstmoment
