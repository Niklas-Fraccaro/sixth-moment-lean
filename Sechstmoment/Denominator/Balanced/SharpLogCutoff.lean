import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Piecewise
import Sechstmoment.Denominator.Measures.DiagonalMeasureLimit


namespace Sechstmoment
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal CompactlySupported
noncomputable section
set_option maxHeartbeats 0

def d02LogCutCoordinate (y : D01LogSpace) : ℝ := y.1 0 + y.2 0

theorem d02LogCutCoordinate_continuous : Continuous d02LogCutCoordinate := by
  unfold d02LogCutCoordinate
  fun_prop

def d02SharpLogRegion : Set D01LogSpace := {y | d02LogCutCoordinate y ≤ 1}

theorem d02LogCutCoordinate_logPoint (L : ℝ) (x : DiagonalSixIndices) :
    d02LogCutCoordinate (d01LogPoint L x) =
      Real.log ((d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ)) / L := by
  have hm : (d01LeftIndices x 0 : ℝ) ≠ 0 := by
    exact_mod_cast (d01LeftIndices_pos x 0).ne'
  have hn : (d01RightIndices x 0 : ℝ) ≠ 0 := by
    exact_mod_cast (d01RightIndices_pos x 0).ne'
  simp only [d02LogCutCoordinate, d01LogPoint, Real.log_mul hm hn, add_div]

theorem d02SharpLogRegion_logPoint_iff {L : ℝ} (hL : 0 < L)
    (x : DiagonalSixIndices) :
    d01LogPoint L x ∈ d02SharpLogRegion ↔
      (d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ) ≤ Real.exp L := by
  have hp : 0 < (d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ) :=
    mul_pos (by exact_mod_cast d01LeftIndices_pos x 0)
      (by exact_mod_cast d01RightIndices_pos x 0)
  change d02LogCutCoordinate (d01LogPoint L x) ≤ 1 ↔ _
  rw [d02LogCutCoordinate_logPoint, div_le_iff₀ hL, one_mul,
    Real.log_le_iff_le_exp hp]

theorem d02SharpLogRegion_measurable : MeasurableSet d02SharpLogRegion :=
  (isClosed_le d02LogCutCoordinate_continuous continuous_const).measurableSet

def d02SharpLogTest (f : D01LogSpace → ℂ) : D01LogSpace → ℂ :=
  d02SharpLogRegion.indicator f

private def d02EdgeCutCoordinate (x : D01EdgeSpace) : ℝ :=
  (∑ j, x (0,j)) + ∑ i, x (i,0)

private def d02EdgeCutHyperplane : AffineSubspace ℝ D01EdgeSpace where
  carrier := {x | d02EdgeCutCoordinate x = 1}
  smul_vsub_vadd_mem' c x y z hx hy hz := by
    change d02EdgeCutCoordinate (c • (x - y) + z) = 1
    have hlin : ∀ x y z : D01EdgeSpace,
        d02EdgeCutCoordinate (c • (x - y) + z) =
          c * (d02EdgeCutCoordinate x - d02EdgeCutCoordinate y) +
            d02EdgeCutCoordinate z := by
      intro x y z
      simp only [d02EdgeCutCoordinate, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      ring
    rw [hlin, hx, hy, hz]
    ring

private theorem d02EdgeCutHyperplane_ne_top : d02EdgeCutHyperplane ≠ ⊤ := by
  intro h
  have hm : (0 : D01EdgeSpace) ∈ d02EdgeCutHyperplane := by
    rw [h]
    trivial
  change d02EdgeCutCoordinate 0 = 1 at hm
  norm_num [d02EdgeCutCoordinate] at hm

theorem d02EdgeMeasure_cut_boundary_null :
    d01EdgeMeasure {x | d02LogCutCoordinate (d01RowColumnSums x) = 1} = 0 := by
  have hnull : (volume : Measure D01EdgeSpace)
      {x | d02EdgeCutCoordinate x = 1} = 0 :=
    Measure.addHaar_affineSubspace volume d02EdgeCutHyperplane d02EdgeCutHyperplane_ne_top
  change (volume.restrict d01NonnegativeOrthant)
    {x | d02EdgeCutCoordinate x = 1} = 0
  exact Measure.absolutelyContinuous_restrict hnull

theorem d02LimitMeasure_cut_boundary_null :
    d01LimitMeasure {y | d02LogCutCoordinate y = 1} = 0 := by
  rw [d01LimitMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply d01RowColumnSums_continuous.measurable
      (isClosed_eq d02LogCutCoordinate_continuous continuous_const).measurableSet]
  rw [show d01RowColumnSums ⁻¹' {y | d02LogCutCoordinate y = 1} =
      {x | d02LogCutCoordinate (d01RowColumnSums x) = 1} from rfl,
    d02EdgeMeasure_cut_boundary_null, mul_zero]

theorem d02LimitMeasure_ae_off_cut_boundary :
    ∀ᵐ y ∂d01LimitMeasure, d02LogCutCoordinate y ≠ 1 := by
  simpa only [ae_iff, not_not] using d02LimitMeasure_cut_boundary_null

theorem d02SharpLogTest_measurable {f : D01LogSpace → ℂ} (hf : Measurable f) :
    Measurable (d02SharpLogTest f) :=
  hf.indicator d02SharpLogRegion_measurable

theorem d02SharpLogTest_compact_support {f : D01LogSpace → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (d02SharpLogTest f) := by
  apply hf.mono
  rw [d02SharpLogTest, support_indicator]
  exact inter_subset_right

theorem d02SharpLogTest_norm_le {f : D01LogSpace → ℂ} {C : ℝ}
    (hf : ∀ y, ‖f y‖ ≤ C) (y : D01LogSpace) : ‖d02SharpLogTest f y‖ ≤ C :=
  (norm_indicator_le_norm_self (s := d02SharpLogRegion) f y).trans (hf y)

theorem d02SharpLogTest_continuousAt {f : D01LogSpace → ℂ} {y : D01LogSpace}
    (hf : ContinuousAt f y) (hy : d02LogCutCoordinate y ≠ 1) :
    ContinuousAt (d02SharpLogTest f) y := by
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · have he : ∀ᶠ z in 𝓝 y, d02LogCutCoordinate z < 1 :=
      (isOpen_lt d02LogCutCoordinate_continuous continuous_const).mem_nhds hlt
    apply hf.congr_of_eventuallyEq
    filter_upwards [he] with z hz
    exact indicator_of_mem (show z ∈ d02SharpLogRegion from hz.le) f
  · have he : ∀ᶠ z in 𝓝 y, 1 < d02LogCutCoordinate z :=
      (isOpen_lt continuous_const d02LogCutCoordinate_continuous).mem_nhds hgt
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [he] with z hz
    exact indicator_of_notMem (show z ∉ d02SharpLogRegion from not_le.mpr hz) f

theorem d02SharpLogTest_ae_continuous {f : D01LogSpace → ℂ} (hf : Continuous f) :
    ∀ᵐ y ∂d01LimitMeasure, ContinuousAt (d02SharpLogTest f) y := by
  filter_upwards [d02LimitMeasure_ae_off_cut_boundary] with y hy
  exact d02SharpLogTest_continuousAt hf.continuousAt hy

theorem d02DiagonalMeasure_sharp_log_limit (f : D01LogSpace → ℂ)
    (hf : Continuous f) (hK : HasCompactSupport f)
    {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    Tendsto (fun L : ℝ => ∫ y, d02SharpLogTest f y ∂d01DiagonalMeasure L) atTop
      (𝓝 ((arithmeticFactor : ℂ) * ∫ x : D01EdgeSpace,
        d02SharpLogTest f (d01RowColumnSums x)
          ∂volume.restrict d01NonnegativeOrthant)) :=
  d01DiagonalMeasure_limit (d02SharpLogTest f)
    (d02SharpLogTest_measurable hf.measurable) (d02SharpLogTest_ae_continuous hf)
    (d02SharpLogTest_compact_support hK) (d02SharpLogTest_norm_le hC)

theorem d02DiagonalMeasure_complex_weighted_sharp_log_limit
    (f w : D01LogSpace → ℂ) (hf : Continuous f) (hK : HasCompactSupport f)
    {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (hw : Continuous w) :
    Tendsto (fun L : ℝ => ∫ y, w y * d02SharpLogTest f y ∂d01DiagonalMeasure L) atTop
      (𝓝 ((arithmeticFactor : ℂ) * ∫ x : D01EdgeSpace,
        w (d01RowColumnSums x) * d02SharpLogTest f (d01RowColumnSums x)
          ∂volume.restrict d01NonnegativeOrthant)) :=
  d01DiagonalMeasure_complex_weighted_limit (d02SharpLogTest f) w
    (d02SharpLogTest_measurable hf.measurable) (d02SharpLogTest_ae_continuous hf)
    (d02SharpLogTest_compact_support hK) (d02SharpLogTest_norm_le hC) hw

theorem d02DiagonalMeasure_shifted_sharp_log_limit
    (f : D01LogSpace → ℂ) (ab : PolarShiftSpace)
    (hf : Continuous f) (hK : HasCompactSupport f)
    {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    Tendsto (fun L : ℝ => ∫ y,
      d01ComplexLaplaceWeight ab y * d02SharpLogTest f y ∂d01DiagonalMeasure L) atTop
      (𝓝 ((arithmeticFactor : ℂ) * ∫ x : D01EdgeSpace,
        d01ComplexLaplaceWeight ab (d01RowColumnSums x) *
          d02SharpLogTest f (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) :=
  d02DiagonalMeasure_complex_weighted_sharp_log_limit f (d01ComplexLaplaceWeight ab)
    hf hK hC (d01ComplexLaplaceWeight_continuous ab)

theorem d02DiagonalMeasure_shifted_sharp_log_compact_limit
    (f : C_c(D01LogSpace, ℂ)) (ab : PolarShiftSpace) :
    Tendsto (fun L : ℝ => ∫ y,
      d01ComplexLaplaceWeight ab y * d02SharpLogTest f y ∂d01DiagonalMeasure L) atTop
      (𝓝 ((arithmeticFactor : ℂ) * ∫ x : D01EdgeSpace,
        d01ComplexLaplaceWeight ab (d01RowColumnSums x) *
          d02SharpLogTest f (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) :=
  d02DiagonalMeasure_shifted_sharp_log_limit f ab f.continuous f.hasCompactSupport
    (fun y => BoundedContinuousFunction.norm_coe_le_norm f.toBoundedContinuousFunction y)

theorem d02DiagonalMeasure_shifted_sharp_log_height_limit
    (f : C_c(D01LogSpace, ℂ)) (ab : PolarShiftSpace) :
    Tendsto (fun T : ℝ => ∫ y,
      d01ComplexLaplaceWeight ab y * d02SharpLogTest f y
        ∂d01DiagonalMeasure (Real.log T)) atTop
      (𝓝 ((arithmeticFactor : ℂ) * ∫ x : D01EdgeSpace,
        d01ComplexLaplaceWeight ab (d01RowColumnSums x) *
          d02SharpLogTest f (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) :=
  (d02DiagonalMeasure_shifted_sharp_log_compact_limit f ab).comp Real.tendsto_log_atTop

end
end Sechstmoment
