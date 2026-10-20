import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import SixthMoment.Analysis.Gaussian.Integrability
import Std


namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

theorem gaussian_polynomial_half_integrable (n : ℕ) :
    Integrable (fun v : ℝ => (1+|v|)^n*Real.exp (-(1/2)*v^2)) := by
  have hg := integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)
  have hp : Integrable (fun v : ℝ => |v|^n*Real.exp (-(1/2)*v^2)) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (s := (n : ℝ))
      (by norm_num) (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)).norm
    simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow, Real.abs_exp] using h
  have hs : Integrable (fun v : ℝ => (1+|v|^n)*Real.exp (-(1/2)*v^2)) := by
    convert hg.add hp using 1
    ext v
    simp only [Pi.add_apply]
    ring
  apply (hs.const_mul (2^n)).mono' (by fun_prop)
  filter_upwards [] with v
  rw [Real.norm_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_right (SixthMoment.one_add_abs_pow_le n v)
    (Real.exp_pos (-(1/2)*v^2)).le
  simpa only [mul_assoc] using h

def gaussianTailConstant (n : ℕ) : ℝ :=
  ∫ v : ℝ, (1+|v|)^n*Real.exp (-(1/2)*v^2)

theorem gaussianTailConstant_nonneg (n : ℕ) : 0 ≤ gaussianTailConstant n :=
  integral_nonneg (fun _ => by positivity)

theorem gaussian_integral_tail_norm_le (f : ℝ → ℂ) (hfi : Integrable f)
    (n : ℕ) {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hf : ∀ v, ‖f v‖ ≤ B*(1+|v|)^n*Real.exp (-v^2)) :
    ‖∫ v in {v : ℝ | R < |v|}, f v‖ ≤
      B*gaussianTailConstant n*Real.exp (-(1/2)*R^2) := by
  let s : Set ℝ := {v : ℝ | R < |v|}
  have hs : MeasurableSet s := (isOpen_lt continuous_const continuous_abs).measurableSet
  let c : ℝ := B*Real.exp (-(1/2)*R^2)
  let g : ℝ → ℝ := fun v => c*((1+|v|)^n*Real.exp (-(1/2)*v^2))
  have hgi : Integrable g := (gaussian_polynomial_half_integrable n).const_mul c
  have hpoint : ∀ v ∈ s, ‖f v‖ ≤ g v := by
    intro v hv
    have hsq : R^2 ≤ v^2 := by
      have hh : R < |v| := hv
      nlinarith [sq_abs v]
    have he : Real.exp (-v^2) ≤ Real.exp (-(1/2)*R^2)*Real.exp (-(1/2)*v^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    calc
      _ ≤ B*(1+|v|)^n*Real.exp (-v^2) := hf v
      _ ≤ B*(1+|v|)^n*(Real.exp (-(1/2)*R^2)*Real.exp (-(1/2)*v^2)) := by gcongr
      _ = g v := by dsimp [g,c]; ring
  calc
    _ ≤ ∫ v in s, ‖f v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v in s, g v := setIntegral_mono_on hfi.norm.integrableOn hgi.integrableOn hs hpoint
    _ ≤ ∫ v : ℝ, g v := setIntegral_le_integral hgi
      (Eventually.of_forall (fun _ => by dsimp [g,c]; positivity))
    _ = _ := by rw [integral_const_mul]; dsimp [c,gaussianTailConstant]; ring

end
end SixthMoment.Source
