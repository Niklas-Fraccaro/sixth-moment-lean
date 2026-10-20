import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.ContinuousMap.Bounded.Normed


open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace SixthMoment.D01

theorem closure_preimage_closed_ae_eq
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] {μ : Measure X} {f : X → Y}
    (hf : ∀ᵐ x ∂μ, ContinuousAt f x) {s : Set Y} (hs : IsClosed s) :
    closure (f ⁻¹' s) =ᵐ[μ] f ⁻¹' s := by
  filter_upwards [hf] with x hx
  apply propext
  constructor
  · intro h
    have hm := mem_closure_image hx h
    exact hs.closure_subset (closure_mono (image_preimage_subset f s) hm)
  · exact fun h => subset_closure h

theorem probability_tendsto_map_of_ae_continuous
    {X Y ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {l : Filter ι} [l.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) {f : X → Y} (hfm : Measurable f)
    (hfc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x) :
    Tendsto (fun i => (μs i).map f) l (𝓝 (μ.map f)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro s hs
  have heq : (μ : Measure X) (closure (f ⁻¹' s)) = (μ : Measure X) (f ⁻¹' s) :=
    measure_congr (closure_preimage_closed_ae_eq hfc hs)
  simp_rw [ProbabilityMeasure.map_apply' _ hfm.aemeasurable hs.measurableSet]
  rw [← heq]
  exact (Filter.limsup_le_limsup (Eventually.of_forall fun i =>
    measure_mono (subset_closure : f ⁻¹' s ⊆ closure (f ⁻¹' s)))).trans
      (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_closure)

theorem probability_tendsto_integral_of_ae_continuous
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter ι} [l.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) {f : X → ℂ} (hfm : Measurable f)
    (hfc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x)
    {C : ℝ} (hfC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun i => ∫ x, f x ∂(μs i : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  let Y := {z : ℂ // ‖z‖ ≤ C}
  let g : X → Y := fun x => ⟨f x, hfC x⟩
  have hgm : Measurable g := hfm.subtype_mk
  have hgc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt g x := by
    filter_upwards [hfc] with x hx
    exact hx.codRestrict hfC
  let k : Y →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    Subtype.val continuous_subtype_val C (fun z => z.property)
  have hg := probability_tendsto_map_of_ae_continuous hμ hgm hgc
  have hk := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hg k
  simp_rw [ProbabilityMeasure.toMeasure_map,
    integral_map_of_stronglyMeasurable hgm k.continuous.stronglyMeasurable] at hk
  exact hk

theorem finiteMeasure_integral_eq_mass_smul_normalize
    {X : Type*} [MeasurableSpace X] [Nonempty X]
    (μ : FiniteMeasure X) (f : X → ℂ) :
    (∫ x, f x ∂(μ : Measure X)) =
      μ.mass • (∫ x, f x ∂(μ.normalize : Measure X)) := by
  conv_lhs => rw [μ.self_eq_mass_smul_normalize]
  simp only [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  rfl

theorem finiteMeasure_tendsto_integral_of_ae_continuous
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [Nonempty X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter ι} [l.IsCountablyGenerated]
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) (hμne : μ ≠ 0)
    {f : X → ℂ} (hfm : Measurable f)
    (hfc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x)
    {C : ℝ} (hfC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun i => ∫ x, f x ∂(μs i : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  have hc : ∀ᵐ x ∂(μ.normalize : Measure X), ContinuousAt f x := by
    rw [μ.toMeasure_normalize_eq_of_nonzero hμne]
    exact Measure.ae_smul_measure hfc μ.mass⁻¹
  have hp := probability_tendsto_integral_of_ae_continuous
    (FiniteMeasure.tendsto_normalize_of_tendsto hμ hμne) hfm hc hfC
  have h := hμ.mass.smul hp
  simpa only [← finiteMeasure_integral_eq_mass_smul_normalize] using h

end SixthMoment.D01
