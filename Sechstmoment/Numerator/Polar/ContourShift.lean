import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.PowerSeries.Basic
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
import Mathlib.Topology.UniformSpace.UniformConvergence
import Sechstmoment.Analysis.Complex.SimplePole
import Sechstmoment.Numerator.Polar.Mellin.ContourBounds
import Std

/-!
# Rectangle contour movement with the literal simple pole at zero

The rectangle calculation uses the holomorphic divided difference `dslope`.
The simple-pole contribution is computed from the actual truncated inverse
vertical integral, using the explicit rational primitives and arctangent
limits. No contour-displacement identity is supplied as an assumption.
-/

namespace Sechstmoment

open Real Complex MeasureTheory Filter Set
open scoped BigOperators Topology

noncomputable section

/-- The actual weighted nine-zeta Euler contour moves from `Re z=1` to
`Re z=-δ/2`, with precisely its genuine simple-pole value at zero. All
analytic boundary hypotheses of the rectangle theorem are discharged. -/
theorem polarMellinWeightedKernel_contour_shift
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {δ x : ℝ} {u v : ℂ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4) (hx : 0 < x)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re)
    (hρ : ∀ ij : Fin 2 × Fin 2, purePolarRoot T σ (m,ij) ≠ 0) :
    Source.verticalIntegral 1 (polarMellinWeightedKernel T σ m u v x) =
      polarMellinRemovedKernel T σ m u v 0+
        polarMellinRemainderIntegral T σ m u v x δ := by
  let F : ℂ → ℂ := polarMellinRemovedKernel T σ m u v
  let H : ℂ → ℂ := fun z => F z*(x:ℂ)^(2*z)
  have hxne : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hPow : DifferentiableOn ℂ (fun z : ℂ => (x:ℂ)^(2*z))
      (polarMellinHolomorphicDomain δ) :=
    (differentiableOn_id.const_mul (2:ℂ)).const_cpow (.inl hxne)
  have hH : DifferentiableOn ℂ H (polarMellinHolomorphicDomain δ) :=
    (polarMellinRemovedKernel_differentiableOn T σ m hδ hδ1 hα hu hv).mul hPow
  have hρb (ij : Fin 2 × Fin 2) : ‖purePolarRoot T σ (m,ij)‖ ≤ δ/4 :=
    purePolarRoot_norm_le_of_rawShifts hα (m,ij)
  have hOffLeft (y : ℝ) (ij : Fin 2 × Fin 2) :
      ((-δ/2:ℝ)+(y:ℂ)*I : ℂ) ≠ purePolarRoot T σ (m,ij) := by
    intro he
    have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hρb ij))).1
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  have hOffRight (y : ℝ) (ij : Fin 2 × Fin 2) :
      (1+(y:ℂ)*I : ℂ) ≠ purePolarRoot T σ (m,ij) := by
    intro he
    have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hρb ij))).2
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  have hOffHigh (c y : ℝ) (hy : 1 ≤ |y|) (ij : Fin 2 × Fin 2) :
      ((c:ℂ)+(y:ℂ)*I : ℂ) ≠ purePolarRoot T σ (m,ij) := by
    intro he
    have him := (Complex.abs_im_le_norm (purePolarRoot T σ (m,ij))).trans (hρb ij)
    rw [← he] at him
    simp at him
    linarith
  have hEq {z : ℂ} (hz : ∀ ij : Fin 2 × Fin 2, z ≠ purePolarRoot T σ (m,ij)) :
      H z/z = polarMellinWeightedKernel T σ m u v x z := by
    dsimp only [H,F]
    rw [polarMellinRemovedKernel_eq T σ m u v hρ hz]
    unfold polarMellinWeightedKernel
    ring
  have hLeftEq :
      (fun y : ℝ => H ((-δ/2:ℝ)+(y:ℂ)*I)/((-δ/2:ℝ)+(y:ℂ)*I)) =
      (fun y : ℝ => polarMellinWeightedKernel T σ m u v x ((-δ/2:ℝ)+(y:ℂ)*I)) :=
    funext (fun y => hEq (hOffLeft y))
  have hRightEq : (fun y : ℝ => H (1+(y:ℂ)*I)/(1+(y:ℂ)*I)) =
      (fun y : ℝ => polarMellinWeightedKernel T σ m u v x (1+(y:ℂ)*I)) :=
    funext (fun y => hEq (hOffRight y))
  have hLeft : Integrable (fun y : ℝ => H ((-δ/2:ℝ)+(y:ℂ)*I)/((-δ/2:ℝ)+(y:ℂ)*I)) := by
    rw [hLeftEq]
    exact polarMellinRemainderIntegrand_left_integrable T σ m hδ hδ1 hx hα hu hv
  have hRight : Integrable (fun y : ℝ => H (1+(y:ℂ)*I)/(1+(y:ℂ)*I)) := by
    rw [hRightEq]
    exact polarMellinWeightedKernel_right_integrable T σ m hδ hδ1 hx hα hu hv
  have hedge : Tendsto (fun y : ℝ => ∫ c in (-δ/2)..1,
      H ((c:ℂ)+(y:ℂ)*I)/((c:ℂ)+(y:ℂ)*I)) (cocompact ℝ) (𝓝 0) := by
    apply (polarMellinWeightedKernel_horizontal_integral_tendsto_zero T σ m
      hδ hδ1 hx hα hu hv).congr'
    have habs : Tendsto (fun y : ℝ => |y|) (cocompact ℝ) atTop := by
      rw [cocompact_eq_atBot_atTop]
      exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
    filter_upwards [habs.eventually (eventually_ge_atTop (1:ℝ))] with y hy
    apply intervalIntegral.integral_congr
    intro c _
    dsimp only
    exact (hEq (hOffHigh c y hy)).symm
  have hstrip : ∀ z : ℂ, -δ/2 ≤ z.re → z.re ≤ 1 →
      z ∈ polarMellinHolomorphicDomain δ := by
    intro z hz _
    change -3*δ/4 < z.re
    linarith
  have hshift := mellinRectangle_simplePole_shift H (polarMellinHolomorphicDomain_isOpen δ)
    hH (show -δ/2 < (0:ℝ) by linarith) (by norm_num : (0:ℝ) < 1)
    hstrip hLeft hRight hedge
  simp only [Complex.ofReal_one] at hshift
  rw [hLeftEq,hRightEq] at hshift
  have hH0 : H 0 = F 0 := by simp [H]
  rw [hH0] at hshift
  have hp : (2*Real.pi:ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  unfold polarMellinRemainderIntegral Source.verticalIntegral
  simp only [Complex.ofReal_one]
  rw [hshift]
  rw [mul_add]
  have he : (1/(2*Real.pi):ℂ)*((2*Real.pi:ℂ)*polarMellinRemovedKernel T σ m u v 0) =
      polarMellinRemovedKernel T σ m u v 0 := by field_simp
  rw [he]
  unfold polarMellinWeightedKernel
  ring

end

end Sechstmoment
