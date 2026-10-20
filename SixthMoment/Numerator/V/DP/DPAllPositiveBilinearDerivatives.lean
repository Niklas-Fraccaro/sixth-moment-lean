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
import SixthMoment.Numerator.V.KernelRegularity
import Std


namespace SixthMoment
open Complex MeasureTheory Set Metric Filter
open scoped Topology BigOperators

set_option maxHeartbeats 1000000
noncomputable section

theorem dpAllPositiveBilinearMoment_differentiableOn_normalized {T : ℝ} (hT : 1 < T)
    (η : ℝ) (P Q : Polynomial ℝ) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (fun σ => dpAllPositiveBilinearMoment T η P Q σ Φ)
      (momentNormalizedShiftDomain T) := by
  simp_rw [dpAllPositiveBilinearMoment_eq_raw]
  exact (allPositiveRawMoment_differentiableOn hT η η _ _ Φ
    (zeroExtendedPolynomialProfile_zero_above η P)
    (zeroExtendedPolynomialProfile_zero_above η Q) hΦ).comp
      (rawMomentShifts_differentiable T).differentiableOn (fun _ h => h)

theorem dpAllPositiveBilinearMoment_differentiableOn_polydisc {T : ℝ} (hT : 1 < T)
    (R : Fin 4 → ℝ) (hR : ∀ j, 2*R j < Real.log T)
    (η : ℝ) (P Q : Polynomial ℝ) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (fun σ => dpAllPositiveBilinearMoment T η P Q σ Φ)
      (rectangularClosedPolydisc R) :=
  (dpAllPositiveBilinearMoment_differentiableOn_normalized hT η P Q Φ hΦ).mono
    (closedPolydisc_subset_momentNormalizedShiftDomain hT R hR)

namespace Source

private theorem square_actual_moment_analyticAt {T : ℝ} (hT : 1 < T)
    (hL : 16 < Real.log T) (η : ℝ) (P : Polynomial ℝ) (Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖<4) :
    AnalyticAt ℂ (fun z => dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ) z := by
  have hR : ∀ j, 2*dpCauchyRadii j < Real.log T := by
    intro j
    have hr : dpCauchyRadii j ≤ (8:ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
    linarith
  have hm := dpAllPositiveMoment_differentiableOn_polydisc hT dpCauchyRadii hR η P Φ hΦ
  have hd : DifferentiableOn ℂ (fun z => dpAllPositiveMoment T η P (dpCoincidentShifts z) Φ)
      (ball 0 4) := hm.comp dpCoincidentShifts_differentiable.differentiableOn (by
        intro w hw
        apply dpCoincidentShifts_mem_polydisc
        exact (show ‖w‖<4 by simpa only [mem_ball,dist_zero_right] using hw).le)
  exact hd.analyticAt (isOpen_ball.mem_nhds
    (by simpa only [mem_ball,dist_zero_right] using hz))

theorem dpAllPositiveBilinearMoment_polarPolynomialBilinearJ_derivative_tendsto_at
    (n : ℕ) (hsource : DPv2SharpInput) (η : ℝ) (hη : 0 < η) (hηu : η < 1/4)
    (P Q : Polynomial ℝ) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (z : ℂ) (hz : ‖z‖≤2) :
    Tendsto (fun T : ℝ =>
      iteratedDeriv n (fun w => dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts w) Φ) z/
        ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        iteratedDeriv n (polarPolynomialBilinearJ η P Q) z)) := by
  have hp := dpAllPositiveMoment_polarPolynomialJ_derivative_tendsto_at n
    hsource η hη hηu (P+Q) Φ hΦ z hz
  have hm := dpAllPositiveMoment_polarPolynomialJ_derivative_tendsto_at n
    hsource η hη hηu (P-Q) Φ hΦ z hz
  have ht := (hp.sub hm).const_mul (1/4:ℂ)
  have hz4 : ‖z‖<4 := by linarith
  have hk := polarPolynomialBilinearJ_iteratedDeriv_polarization n η hη.le P Q z hz4
  have he : (1/4:ℂ)*
      ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*iteratedDeriv n (polarPolynomialJ η (P+Q)) z-
        (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*iteratedDeriv n (polarPolynomialJ η (P-Q)) z) =
      (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*iteratedDeriv n (polarPolynomialBilinearJ η P Q) z := by
    rw [hk]
    ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  have hR (j : Fin 4) : 2*dpCauchyRadii j < Real.log T := by
    have hj : dpCauchyRadii j ≤ (8:ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
    linarith
  have hEq : (fun w => dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts w) Φ) =ᶠ[𝓝 z]
      (fun w => (1/4:ℂ)*(dpAllPositiveMoment T η (P+Q) (dpCoincidentShifts w) Φ-
        dpAllPositiveMoment T η (P-Q) (dpCoincidentShifts w) Φ)) := by
    filter_upwards [isOpen_ball.mem_nhds
      (show z ∈ ball (0:ℂ) 4 by simpa only [mem_ball,dist_zero_right] using hz4)] with w hw
    have hw4 : ‖w‖<4 := by simpa only [mem_ball,dist_zero_right] using hw
    exact dpAllPositiveBilinearMoment_polarization hT η P Q (dpCoincidentShifts w) Φ
      (closedPolydisc_subset_momentNormalizedShiftDomain hT dpCauchyRadii hR
        (dpCoincidentShifts_mem_polydisc hw4.le)) hΦ
  rw [hEq.iteratedDeriv_eq n,iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sub
      ((square_actual_moment_analyticAt hT hL η (P+Q) Φ hΦ z hz4).contDiffAt (n := n))
      ((square_actual_moment_analyticAt hT hL η (P-Q) Φ hΦ z hz4).contDiffAt (n := n))]
  ring

theorem dpAllPositiveBilinearMoment_polarPolynomialBilinearJ_operator_tendsto
    (N : ℕ) (q : Fin (N+1) → ℂ) (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P Q : Polynomial ℝ)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (z : ℂ) (hz : ‖z‖≤2) :
    Tendsto (fun T : ℝ => finiteDifferentialOperator N q
      (fun w => dpAllPositiveBilinearMoment T η P Q (dpCoincidentShifts w) Φ) z/
        ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        finiteDifferentialOperator N q (polarPolynomialBilinearJ η P Q) z)) := by
  have ht := tendsto_finsetSum Finset.univ (fun j (_hj : j ∈ Finset.univ) =>
    (tendsto_const_nhds (x := q j)).mul
      (dpAllPositiveBilinearMoment_polarPolynomialBilinearJ_derivative_tendsto_at j.val
        hsource η hη hηu P Q Φ hΦ z hz))
  convert ht using 1
  · funext T
    unfold finiteDifferentialOperator
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · congr 1
    unfold finiteDifferentialOperator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

end Source
end
end SixthMoment
