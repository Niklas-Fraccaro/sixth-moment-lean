import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Tactic

/-! Removing a strictly positive exponential tilt from compact test functions.
The measure is arbitrary; the actual diagonal measures are supplied by the
terminal D01 assembly. -/

namespace Sechstmoment
open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology CompactlySupported
noncomputable section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

def d01ExponentialTilt (μ : Measure X) (q : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-q x)))

omit [TopologicalSpace X] [BorelSpace X] in
theorem d01ExponentialTilt_injective (q : X → ℝ) (hq : Measurable q) :
    Function.Injective (fun μ : Measure X => d01ExponentialTilt μ q) := by
  intro μ ν h
  have hw : Measurable (fun x => ENNReal.ofReal (Real.exp (-q x))) := by fun_prop
  have hμ := withDensity_inv_same (μ := μ) hw
    (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos (-q x))).ne'))
    (ae_of_all _ (fun _ => ENNReal.ofReal_ne_top))
  have hν := withDensity_inv_same (μ := ν) hw
    (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos (-q x))).ne'))
    (ae_of_all _ (fun _ => ENNReal.ofReal_ne_top))
  change μ.withDensity _ = ν.withDensity _ at h
  rw [← hμ, ← hν, h]

def d01UntiltTest (q : X → ℝ) (hq : Continuous q) (f : C_c(X, ℂ)) : C_c(X, ℂ) where
  toFun x := (Real.exp (q x) : ℂ) * f x
  continuous_toFun := (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hq)).mul
    f.continuous
  hasCompactSupport' := f.hasCompactSupport.mul_left

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem d01UntiltTest_apply (q : X → ℝ) (hq : Continuous q)
    (f : C_c(X, ℂ)) (x : X) :
    d01UntiltTest q hq f x = (Real.exp (q x) : ℂ) * f x := rfl

omit [TopologicalSpace X] [BorelSpace X] in
theorem d01_integral_remove_exponential_tilt (μ : Measure X) (q : X → ℝ)
    (hq : Measurable q) (f : X → ℂ) :
    (∫ x, (Real.exp (q x) : ℂ) * f x ∂d01ExponentialTilt μ q) = ∫ x, f x ∂μ := by
  have hw : Measurable (fun x => ENNReal.ofReal (Real.exp (-q x))) := by fun_prop
  rw [d01ExponentialTilt, integral_withDensity_eq_integral_toReal_smul hw
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  change (Real.exp (-q x) : ℂ) * ((Real.exp (q x) : ℂ) * f x) = f x
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  simp

theorem d01_tendsto_compact_test_of_tilt {ι : Type*} {l : Filter ι}
    (μ : ι → Measure X) (ν : Measure X) (q : X → ℝ) (hq : Continuous q)
    (hweak : ∀ g : X →ᵇ ℂ,
      Tendsto (fun i => ∫ x, g x ∂d01ExponentialTilt (μ i) q) l
        (𝓝 (∫ x, g x ∂d01ExponentialTilt ν q)))
    (f : C_c(X, ℂ)) :
    Tendsto (fun i => ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ν)) := by
  have h := hweak (d01UntiltTest q hq f).toBoundedContinuousFunction
  simpa only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
    d01UntiltTest_apply, d01_integral_remove_exponential_tilt _ _ hq.measurable] using h

end
end Sechstmoment
