import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import SixthMoment.Analysis.Profiles.Polynomial
import SixthMoment.Numerator.V.DP.DPWeightedSimplex
import SixthMoment.Zeta.Moments.AnalyticMomentLinearity
import Std


namespace SixthMoment
open Complex MeasureTheory Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 0

private theorem raw_shifts_eventually_real_small (σ : MomentShifts) :
    ∀ᶠ T : ℝ in atTop, ∀ j, |(rawMomentShifts T σ j).re| < 1/2 := by
  let B : ℝ := ∑ j : Fin 4, |(σ j).re|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hj (j : Fin 4) : |(σ j).re| ≤ B := by
    change |(σ j).re| ≤ ∑ k : Fin 4, |(σ k).re|
    exact Finset.single_le_sum (f := fun k : Fin 4 => |(σ k).re|)
      (fun k _ => abs_nonneg ((σ k).re)) (Finset.mem_univ j)
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (2*B+1))] with T hT
  intro j
  have hL : 0 < Real.log T := by linarith
  simp only [rawMomentShifts, Complex.div_ofReal_re, abs_div, abs_of_pos hL]
  apply (div_lt_iff₀ hL).mpr
  linarith [hj j]

namespace Source
noncomputable section

def dpNormalizedBilinearFourResidues (q η : ℝ) (P Q : Polynomial ℝ)
    (σ : MomentShifts) : ℂ :=
  Complex.exp ((q:ℂ)*(-σ 0-σ 2-σ 3))*
      dpNormalizedTriple η P (σ 1) (σ 2) (σ 3)*
      dpNormalizedTriple η Q (σ 1) (σ 2) (σ 3) /
      ((σ 1-σ 0)*(σ 0+σ 2)*(σ 0+σ 3)) +
    Complex.exp ((q:ℂ)*(-σ 1-σ 2-σ 3))*
      dpNormalizedTriple η P (σ 0) (σ 2) (σ 3)*
      dpNormalizedTriple η Q (σ 0) (σ 2) (σ 3) /
      ((σ 0-σ 1)*(σ 1+σ 2)*(σ 1+σ 3)) +
    Complex.exp ((q:ℂ)*(-σ 3))*
      dpNormalizedTriple η P (σ 1) (-σ 0) (σ 3)*
      dpNormalizedTriple η Q (σ 1) (-σ 0) (σ 3) /
      ((σ 1+σ 2)*(σ 0+σ 2)*(σ 2-σ 3)) +
    Complex.exp ((q:ℂ)*(-σ 2))*
      dpNormalizedTriple η P (σ 1) (σ 2) (-σ 0)*
      dpNormalizedTriple η Q (σ 1) (σ 2) (-σ 0) /
      ((σ 1+σ 3)*(σ 3-σ 2)*(σ 0+σ 3))

theorem dpNormalizedBilinearFourResidues_polarization (q η : ℝ)
    (P Q : Polynomial ℝ) (σ : MomentShifts) :
    dpNormalizedBilinearFourResidues q η P Q σ =
      (1/4:ℂ)*(dpNormalizedFourResidues q η (P+Q) σ-
        dpNormalizedFourResidues q η (P-Q) σ) := by
  unfold dpNormalizedBilinearFourResidues dpNormalizedFourResidues
  simp only [dpNormalizedTriple_add, dpNormalizedTriple_sub]
  ring

theorem dpActualBilinearMoment_normalized_tendsto (hsource : DPv2Input)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P Q : Polynomial ℝ)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (σ : MomentShifts) (hσ : DPSeparated σ) :
    Tendsto (fun T : ℝ => chiTwistedFourthMoment T (rawMomentShifts T σ)
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ /
        ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*(η:ℂ)^6*
        dpNormalizedBilinearFourResidues 1 η P Q σ)) := by
  have hp := dpActualMoment_normalized_tendsto hsource η hη hηu (P+Q) Φ hΦ σ hσ
  have hm := dpActualMoment_normalized_tendsto hsource η hη hηu (P-Q) Φ hΦ σ hσ
  have ht := (hp.sub hm).const_mul (1/4:ℂ)
  have hk : (1/4:ℂ)*
      ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*(η:ℂ)^6*
        dpNormalizedFourResidues 1 η (P+Q) σ-
       (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*(η:ℂ)^6*
        dpNormalizedFourResidues 1 η (P-Q) σ) =
      (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*(η:ℂ)^6*
        dpNormalizedBilinearFourResidues 1 η P Q σ := by
    rw [dpNormalizedBilinearFourResidues_polarization]
    ring
  rw [hk] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ), raw_shifts_eventually_real_small σ] with T hT hα
  have hmoment := chiTwistedFourthMoment_polarization hT η (rawMomentShifts T σ)
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ hα
    (fun x hx => zeroExtendedPolynomialProfile_zero_above η P x hx)
    (fun x hx => zeroExtendedPolynomialProfile_zero_above η Q x hx) hΦ
  rw [← zeroExtendedPolynomialProfile_add, ← zeroExtendedPolynomialProfile_sub] at hmoment
  rw [hmoment]
  ring

end
end Source
end SixthMoment
