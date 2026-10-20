import Sechstmoment.Analysis.Measures.TiltedTests
import Sechstmoment.Denominator.Measures.ExponentialTightness
import Sechstmoment.Denominator.Measures.LaplaceUniqueness
import Sechstmoment.Denominator.Measures.WeightedMeasureConvergence

namespace Sechstmoment
open MeasureTheory Filter Set BoundedContinuousFunction
open scoped Topology BigOperators CompactlySupported
noncomputable section

theorem d01DiagonalMeasure_bounded_compact_tendsto (f : D01LogSpace → ℂ)
    (hfm : Measurable f) (hfc : ∀ᵐ y ∂d01LimitMeasure, ContinuousAt f y)
    (hK : HasCompactSupport f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    Tendsto (fun L : ℝ => ∫ y, f y ∂d01DiagonalMeasure L) atTop
      (𝓝 (∫ y, f y ∂d01LimitMeasure)) := by
  have hscale : Tendsto (fun L : ℝ => max 1 L) atTop atTop :=
    tendsto_atTop_mono (fun L => le_max_right 1 L) tendsto_id
  have h := d01_tendsto_bounded_ae_continuous_compact_test_of_tilt
    (fun L : ℝ => d01DiagonalMeasure (max 1 L)) d01LimitMeasure d01LogTotal
    d01LogTotal_continuous (fun L => d01TiltedDiagonalFiniteMeasure (max 1 L))
    d01TiltedLimitFiniteMeasure
    (fun L => d01TiltedDiagonalFiniteMeasure_toMeasure
      (zero_lt_one.trans_le (le_max_left 1 L)))
    d01TiltedLimitFiniteMeasure_toMeasure
    (d01DiagonalMeasure_tilted_tendsto.comp hscale)
    d01TiltedLimitFiniteMeasure_ne_zero f hfm hfc hK hC
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  rw [max_eq_right hL]

theorem d01DiagonalMeasure_vague_tendsto (f : C_c(D01LogSpace, ℂ)) :
    Tendsto (fun L : ℝ => ∫ y, f y ∂d01DiagonalMeasure L) atTop
      (𝓝 (∫ y, f y ∂d01LimitMeasure)) :=
  d01DiagonalMeasure_bounded_compact_tendsto f f.continuous.measurable
    (ae_of_all _ (fun _ => f.continuous.continuousAt)) f.hasCompactSupport
    (fun y => norm_coe_le_norm f.toBoundedContinuousFunction y)

theorem d01DiagonalMeasure_limit (f : D01LogSpace → ℂ)
    (hfm : Measurable f) (hfc : ∀ᵐ y ∂d01LimitMeasure, ContinuousAt f y)
    (hK : HasCompactSupport f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    Tendsto (fun L : ℝ => ∫ y, f y ∂d01DiagonalMeasure L) atTop
      (𝓝 ((arithmeticFactor : ℂ) *
        ∫ x : D01EdgeSpace, f (d01RowColumnSums x) ∂volume.restrict d01NonnegativeOrthant)) := by
  have h := d01DiagonalMeasure_bounded_compact_tendsto f hfm hfc hK hC
  rw [d01LimitMeasure_integral hfm.stronglyMeasurable] at h
  simpa only [d01EdgeMeasure, Complex.real_smul] using h

theorem d01DiagonalMeasure_log_height_limit (f : D01LogSpace → ℂ)
    (hfm : Measurable f) (hfc : ∀ᵐ y ∂d01LimitMeasure, ContinuousAt f y)
    (hK : HasCompactSupport f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    Tendsto (fun T : ℝ => ∫ y, f y ∂d01DiagonalMeasure (Real.log T)) atTop
      (𝓝 ((arithmeticFactor : ℂ) *
        ∫ x : D01EdgeSpace, f (d01RowColumnSums x) ∂volume.restrict d01NonnegativeOrthant)) :=
  (d01DiagonalMeasure_limit f hfm hfc hK hC).comp Real.tendsto_log_atTop

theorem d01DiagonalMeasure_complex_weighted_limit (f w : D01LogSpace → ℂ)
    (hfm : Measurable f) (hfc : ∀ᵐ y ∂d01LimitMeasure, ContinuousAt f y)
    (hK : HasCompactSupport f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C)
    (hw : Continuous w) :
    Tendsto (fun L : ℝ => ∫ y, w y * f y ∂d01DiagonalMeasure L) atTop
      (𝓝 ((arithmeticFactor : ℂ) *
        ∫ x : D01EdgeSpace, w (d01RowColumnSums x) * f (d01RowColumnSums x)
          ∂volume.restrict d01NonnegativeOrthant)) := by
  obtain ⟨B, hB⟩ := d01_bounded_continuous_mul_compact_test hw hK hC
  apply d01DiagonalMeasure_limit (fun y => w y * f y) (hw.measurable.mul hfm) _
    hK.mul_left hB
  filter_upwards [hfc] with y hy
  exact hw.continuousAt.mul hy

theorem d01LimitMeasure_unique (μ : Measure D01LogSpace)
    (hμ : IsFiniteMeasure (d01ExponentialTilt μ d01LogTotal))
    (hLaplace : ∀ ab : PolarShiftSpace,
      (∀ i, 0 < (ab.1 i).re) → (∀ j, 0 < (ab.2 j).re) →
      (∫ y, d01ComplexLaplaceWeight ab y ∂μ) =
        (arithmeticFactor : ℂ) * ∏ ij : Fin 3 × Fin 3, (ab.1 ij.1 + ab.2 ij.2)⁻¹) :
    μ = d01LimitMeasure := by
  apply d01_measure_eq_of_complexLaplace μ d01LimitMeasure hμ
    d01LimitMeasure_fixedTilt_finite
  intro ab ha hb
  rw [hLaplace ab ha hb, d01LimitMeasure_complexLaplace ab ha hb]

end
end Sechstmoment
