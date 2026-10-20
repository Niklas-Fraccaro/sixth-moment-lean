import Sechstmoment.Analysis.Measures.AlmostContinuousTests
import Sechstmoment.Analysis.Measures.ExponentialTilt


open Filter MeasureTheory Set
open scoped Topology

namespace Sechstmoment

theorem d01_bounded_continuous_mul_compact_test
    {X : Type*} [TopologicalSpace X] {g : X → ℂ} (hg : Continuous g)
    {f : X → ℂ} (hf : HasCompactSupport f)
    {C : ℝ} (hfC : ∀ x, ‖f x‖ ≤ C) :
    ∃ B : ℝ, ∀ x, ‖g x * f x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hf.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max B 0 * max C 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact (norm_mul_le _ _).trans (mul_le_mul
      ((hB x hx).trans (le_max_left _ _))
      ((hfC x).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _))
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, norm_zero]
    exact mul_nonneg (le_max_right _ _) (le_max_right _ _)

theorem d01_bounded_untilted_compact_test
    {X : Type*} [TopologicalSpace X] {q : X → ℝ} (hq : Continuous q)
    {f : X → ℂ} (hf : HasCompactSupport f)
    {C : ℝ} (hfC : ∀ x, ‖f x‖ ≤ C) :
    ∃ B : ℝ, ∀ x, ‖(Real.exp (q x) : ℂ) * f x‖ ≤ B :=
  d01_bounded_continuous_mul_compact_test
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hq)) hf hfC

theorem d01_tendsto_bounded_ae_continuous_compact_test_of_tilt
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [Nonempty X]
    {l : Filter ι} [l.IsCountablyGenerated]
    (μ : ι → Measure X) (ν : Measure X) (q : X → ℝ) (hq : Continuous q)
    (κ : ι → FiniteMeasure X) (νtilt : FiniteMeasure X)
    (hκ : ∀ i, (κ i : Measure X) = d01ExponentialTilt (μ i) q)
    (hνtilt : (νtilt : Measure X) = d01ExponentialTilt ν q)
    (hweak : Tendsto κ l (𝓝 νtilt)) (hνtiltne : νtilt ≠ 0)
    (f : X → ℂ) (hfm : Measurable f) (hfc : ∀ᵐ x ∂ν, ContinuousAt f x)
    (hf : HasCompactSupport f) {C : ℝ} (hfC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun i => ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ν)) := by
  let g : X → ℂ := fun x => (Real.exp (q x) : ℂ) * f x
  have hgm : Measurable g := by fun_prop
  have hac : d01ExponentialTilt ν q ≪ ν := withDensity_absolutelyContinuous _ _
  have hgc : ∀ᵐ x ∂(νtilt : Measure X), ContinuousAt g x := by
    rw [hνtilt]
    filter_upwards [hfc.filter_mono (Measure.ae_le_iff_absolutelyContinuous.mpr hac)] with x hx
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hq)).continuousAt.mul hx
  obtain ⟨B, hB⟩ := d01_bounded_untilted_compact_test hq hf hfC
  have h := D01.finiteMeasure_tendsto_integral_of_ae_continuous hweak hνtiltne hgm hgc hB
  simpa only [hκ, hνtilt, g, d01_integral_remove_exponential_tilt _ _ hq.measurable] using h

theorem d01_tendsto_complex_weighted_compact_test_of_tilt
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [Nonempty X]
    {l : Filter ι} [l.IsCountablyGenerated]
    (μ : ι → Measure X) (ν : Measure X) (q : X → ℝ) (hq : Continuous q)
    (κ : ι → FiniteMeasure X) (νtilt : FiniteMeasure X)
    (hκ : ∀ i, (κ i : Measure X) = d01ExponentialTilt (μ i) q)
    (hνtilt : (νtilt : Measure X) = d01ExponentialTilt ν q)
    (hweak : Tendsto κ l (𝓝 νtilt)) (hνtiltne : νtilt ≠ 0)
    (f : X → ℂ) (hfm : Measurable f) (hfc : ∀ᵐ x ∂ν, ContinuousAt f x)
    (hf : HasCompactSupport f) {C : ℝ} (hfC : ∀ x, ‖f x‖ ≤ C)
    (w : X → ℂ) (hw : Continuous w) :
    Tendsto (fun i => ∫ x, w x * f x ∂μ i) l
      (𝓝 (∫ x, w x * f x ∂ν)) := by
  obtain ⟨B, hB⟩ := d01_bounded_continuous_mul_compact_test hw hf hfC
  apply d01_tendsto_bounded_ae_continuous_compact_test_of_tilt
    μ ν q hq κ νtilt hκ hνtilt hweak hνtiltne
    (fun x => w x * f x) (hw.measurable.mul hfm) ?_ hf.mul_left hB
  filter_upwards [hfc] with x hx
  exact hw.continuousAt.mul hx

end Sechstmoment
