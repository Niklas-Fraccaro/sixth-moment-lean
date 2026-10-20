import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated


open Filter MeasureTheory
open scoped Topology

namespace SixthMoment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem d01_probability_tendsto_of_charFun
    {α : Type*} {F : Filter α} [F.IsCountablyGenerated]
    {μ : α → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (h : ∀ t, Tendsto (fun a ↦ charFun (μ a : Measure E) t) F
      (𝓝 (charFun (ν : Measure E) t))) :
    Tendsto μ F (𝓝 ν) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro s hs
  exact ProbabilityMeasure.tendsto_of_tendsto_charFun (fun t ↦ (h t).comp hs)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem d01_charFun_normalize (μ : FiniteMeasure E) (hμ : μ ≠ 0) (t : E) :
    charFun (μ.normalize : Measure E) t =
      ((μ.mass : ℝ) : ℂ)⁻¹ * charFun (μ : Measure E) t := by
  rw [charFun_apply, μ.toMeasure_normalize_eq_of_nonzero hμ,
    integral_smul_nnreal_measure]
  simp [charFun_apply, NNReal.smul_def, Complex.real_smul]

theorem d01_normalize_tendsto_of_charFun
    {α : Type*} {F : Filter α} [F.IsCountablyGenerated]
    {μ : α → FiniteMeasure E} {ν : FiniteMeasure E} (hν : ν ≠ 0)
    (hm : Tendsto (fun a ↦ (μ a).mass) F (𝓝 ν.mass))
    (hc : ∀ t, Tendsto (fun a ↦ charFun (μ a : Measure E) t) F
      (𝓝 (charFun (ν : Measure E) t))) :
    Tendsto (fun a ↦ (μ a).normalize) F (𝓝 ν.normalize) := by
  have hmass : ν.mass ≠ 0 := ν.mass_nonzero_iff.mpr hν
  have he : ∀ᶠ a in F, μ a ≠ 0 := by
    filter_upwards [hm.eventually (eventually_ne_nhds hmass)] with a ha
    exact (μ a).mass_nonzero_iff.mp ha
  apply d01_probability_tendsto_of_charFun
  intro t
  have hmC : Tendsto (fun a ↦ (((μ a).mass : ℝ) : ℂ)) F
      (𝓝 ((ν.mass : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (NNReal.continuous_coe.continuousAt.tendsto.comp hm)
  have hn : ((ν.mass : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmass
  have h := (hmC.inv₀ hn).mul (hc t)
  rw [← d01_charFun_normalize ν hν t] at h
  apply h.congr'
  filter_upwards [he] with a ha
  exact (d01_charFun_normalize (μ a) ha t).symm

theorem d01_finiteMeasure_tendsto_of_charFun
    {α : Type*} {F : Filter α} [F.IsCountablyGenerated]
    {μ : α → FiniteMeasure E} {ν : FiniteMeasure E} (hν : ν ≠ 0)
    (hm : Tendsto (fun a ↦ (μ a).mass) F (𝓝 ν.mass))
    (hc : ∀ t, Tendsto (fun a ↦ charFun (μ a : Measure E) t) F
      (𝓝 (charFun (ν : Measure E) t))) :
    Tendsto μ F (𝓝 ν) := by
  exact (FiniteMeasure.tendsto_normalize_iff_tendsto hν).mp
    ⟨d01_normalize_tendsto_of_charFun hν hm hc, hm⟩

theorem d01_normalized_sequence_tight_of_charFun
    {μ : ℕ → FiniteMeasure E} {ν : FiniteMeasure E} (hν : ν ≠ 0)
    (hm : Tendsto (fun n ↦ (μ n).mass) atTop (𝓝 ν.mass))
    (hc : ∀ t, Tendsto (fun n ↦ charFun (μ n : Measure E) t) atTop
      (𝓝 (charFun (ν : Measure E) t))) :
    IsTightMeasureSet (Set.range (fun n ↦ ((μ n).normalize : Measure E))) := by
  have hn := d01_normalize_tendsto_of_charFun hν hm hc
  have hcn := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hn
  exact isTightMeasureSet_of_tendsto_charFun (by fun_prop) hcn

end SixthMoment

namespace SixthMoment

theorem d01_finiteMeasure_map_homeomorph_inverse
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y]
    (e : X ≃ₜ Y) (μ : FiniteMeasure X) :
    (μ.map e).map e.symm = μ := by
  apply Subtype.ext
  change ((μ : Measure X).map e).map e.symm = (μ : Measure X)
  rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
  rw [show (e.symm ∘ e) = id from funext e.symm_apply_apply]
  exact Measure.map_id

theorem d01_finiteMeasure_tendsto_of_homeomorph_map
    {X Y α : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y]
    (e : X ≃ₜ Y) {F : Filter α} {μ : α → FiniteMeasure X} {ν : FiniteMeasure X}
    (h : Tendsto (fun a ↦ (μ a).map e) F (𝓝 (ν.map e))) :
    Tendsto μ F (𝓝 ν) := by
  have hi := FiniteMeasure.tendsto_map_of_tendsto_of_continuous
    (fun a ↦ (μ a).map e) (ν.map e) h e.symm.continuous
  simpa only [d01_finiteMeasure_map_homeomorph_inverse] using hi

theorem d01_finiteMeasure_mass_map_homeomorph
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y]
    (e : X ≃ₜ Y) (μ : FiniteMeasure X) : (μ.map e).mass = μ.mass := by
  apply le_antisymm (FiniteMeasure.mass_map_le e.continuous.measurable.aemeasurable)
  simpa only [d01_finiteMeasure_map_homeomorph_inverse] using
    (FiniteMeasure.mass_map_le (μ := μ.map e) e.symm.continuous.measurable.aemeasurable)

theorem d01_finiteMeasure_tendsto_of_mapped_charFun
    {X E α : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : X ≃ₜ E) {F : Filter α} [F.IsCountablyGenerated]
    {μ : α → FiniteMeasure X} {ν : FiniteMeasure X} (hν : ν ≠ 0)
    (hm : Tendsto (fun a ↦ (μ a).mass) F (𝓝 ν.mass))
    (hc : ∀ t, Tendsto (fun a ↦ charFun ((μ a).map e : Measure E) t) F
      (𝓝 (charFun (ν.map e : Measure E) t))) :
    Tendsto μ F (𝓝 ν) := by
  have hνe : ν.map e ≠ 0 := by
    intro he
    have hz : (ν.map e).mass = 0 := (ν.map e).mass_zero_iff.mpr he
    rw [d01_finiteMeasure_mass_map_homeomorph] at hz
    exact hν (ν.mass_zero_iff.mp hz)
  apply d01_finiteMeasure_tendsto_of_homeomorph_map e
  apply d01_finiteMeasure_tendsto_of_charFun hνe
  · simpa only [d01_finiteMeasure_mass_map_homeomorph] using hm
  · exact hc

theorem d01_finiteMeasure_eq_of_mapped_charFun
    {X E : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : X ≃ₜ E) (μ ν : FiniteMeasure X)
    (hc : ∀ t, charFun (μ.map e : Measure E) t = charFun (ν.map e : Measure E) t) :
    μ = ν := by
  let μe : FiniteMeasure E := μ.map e
  let νe : FiniteMeasure E := ν.map e
  let : IsFiniteMeasure (μe : Measure E) := μe.prop
  let : IsFiniteMeasure (νe : Measure E) := νe.prop
  have he : μ.map e = ν.map e := by
    apply Subtype.ext
    exact Measure.ext_of_charFun (μ := (μe : Measure E)) (ν := (νe : Measure E)) (funext hc)
  have hi := congrArg (fun m : FiniteMeasure E ↦ m.map e.symm) he
  simpa only [d01_finiteMeasure_map_homeomorph_inverse] using hi

end SixthMoment
