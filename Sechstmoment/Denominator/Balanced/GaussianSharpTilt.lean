import Sechstmoment.Denominator.Balanced.GaussianCutBand

/-! Moving-cut estimates in the finite exponential D01 tilt.  Working with
the literal finite measures permits global bounded continuous band tests;
the convergence and mass bounds are the proved arithmetic D01 results.
-/

namespace Sechstmoment
open MeasureTheory Filter Set BoundedContinuousFunction
open scoped Topology
noncomputable section
set_option maxHeartbeats 0

abbrev d02TiltedDiagonalMeasure (L : ℝ) : Measure D01LogSpace :=
  d01TiltedDiagonalFiniteMeasure L

abbrev d02TiltedLimitMeasure : Measure D01LogSpace := d01TiltedLimitFiniteMeasure

theorem d02TiltedLimitMeasure_ae_off_cut :
    ∀ᵐ y ∂d02TiltedLimitMeasure, d02LogCutCoordinate y ≠ 1 := by
  exact d02LimitMeasure_ae_off_cut_boundary.filter_mono
    (withDensity_absolutelyContinuous d01LimitMeasure
      (fun y => ENNReal.ofReal (Real.exp (-d01LogTotal y)))).ae_le

theorem d02TiltedDiagonalMeasure_ae_orthant {L : ℝ} (hL : 0 < L) :
    ∀ᵐ y ∂d02TiltedDiagonalMeasure L, y ∈ d01PositiveOrthant := by
  unfold d02TiltedDiagonalMeasure
  rw [d01TiltedDiagonalFiniteMeasure_toMeasure hL]
  exact (d01DiagonalMeasure_ae_orthant hL).filter_mono
    (withDensity_absolutelyContinuous (d01DiagonalMeasure L)
      (fun y => ENNReal.ofReal (Real.exp (-d01LogTotal y)))).ae_le

theorem d02TiltedMeasure_band_mass_tendsto_zero :
    Tendsto (fun n : ℕ => ∫ y,
      d02CutBandMajorant n (d02LogCutCoordinate y) ∂d02TiltedLimitMeasure)
      atTop (𝓝 0) := by
  have hlim : ∀ᵐ y ∂d02TiltedLimitMeasure,
      Tendsto (fun n : ℕ => d02CutBandMajorant n (d02LogCutCoordinate y))
        atTop (𝓝 (0:ℝ)) := by
    filter_upwards [d02TiltedLimitMeasure_ae_off_cut] with y hy
    exact d02CutBandMajorant_tendsto_zero hy
  have ht := tendsto_integral_of_dominated_convergence (fun _ : D01LogSpace => (1:ℝ))
    (fun n => ((d02CutBandMajorant_continuous n).comp
      d02LogCutCoordinate_continuous).stronglyMeasurable.aestronglyMeasurable)
    (integrable_const (1:ℝ))
    (fun n => ae_of_all _ (fun y => by
      change ‖d02CutBandMajorant n (d02LogCutCoordinate y)‖ ≤ 1
      rw [Real.norm_of_nonneg (d02CutBandMajorant_nonneg n _)]
      exact d02CutBandMajorant_le_one n _)) hlim
  simpa using ht

theorem d02TiltedDiagonalMeasure_band_tendsto (n : ℕ) :
    Tendsto (fun L : ℝ => ∫ y,
      d02CutBandMajorant n (d02LogCutCoordinate y) ∂d02TiltedDiagonalMeasure L) atTop
      (𝓝 (∫ y, d02CutBandMajorant n (d02LogCutCoordinate y)
        ∂d02TiltedLimitMeasure)) := by
  let b : D01LogSpace →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => d02CutBandMajorant n (d02LogCutCoordinate y))
    ((d02CutBandMajorant_continuous n).comp d02LogCutCoordinate_continuous) 1
    (fun y => by
      rw [Real.norm_of_nonneg (d02CutBandMajorant_nonneg n _)]
      exact d02CutBandMajorant_le_one n _)
  exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
    d01DiagonalMeasure_tilted_tendsto) b

theorem d02TiltedDiagonalMeasure_mass_tendsto :
    Tendsto (fun L : ℝ => ∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedDiagonalMeasure L) atTop
      (𝓝 (∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedLimitMeasure)) := by
  simpa only [BoundedContinuousFunction.coe_one, Pi.one_apply] using
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
      d01DiagonalMeasure_tilted_tendsto) (1 : D01LogSpace →ᵇ ℝ)

private theorem d02TiltedGaussian_integral_difference_bound
    {L δ c B : ℝ} (hB : 0 ≤ B) (n : ℕ) (hcut : ∀ q,
      |d02GaussianLogWeight L q c - if q ≤ 1 then 1 else 0| ≤
        δ+d02CutBandMajorant n q)
    (f : D01LogSpace → ℂ) (hfm : Measurable f)
    (hfB : ∀ᵐ y ∂d02TiltedDiagonalMeasure L, ‖f y‖ ≤ B) :
    ‖(∫ y, f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)
      ∂d02TiltedDiagonalMeasure L) -
      ∫ y, d02SharpLogTest f y ∂d02TiltedDiagonalMeasure L‖ ≤
        δ*B*(∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedDiagonalMeasure L) +
          B*(∫ y, d02CutBandMajorant n (d02LogCutCoordinate y)
            ∂d02TiltedDiagonalMeasure L) := by
  have hfi : Integrable f (d02TiltedDiagonalMeasure L) :=
    (integrable_const B).mono' hfm.aestronglyMeasurable hfB
  have hgm : Measurable (fun y : D01LogSpace =>
      (d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)) :=
    Complex.measurable_ofReal.comp ((d02GaussianLogWeight_measurable L c).comp
      d02LogCutCoordinate_continuous.measurable)
  have hgi : Integrable (fun y =>
      f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ))
      (d02TiltedDiagonalMeasure L) := by
    apply hfi.norm.mono' (hfm.mul hgm).aestronglyMeasurable
    exact ae_of_all _ (fun y => by
      change ‖f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)‖ ≤ ‖f y‖
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ d02GaussianLogWeight L (d02LogCutCoordinate y) c from
        d02GaussianTail_nonneg _)]
      exact mul_le_of_le_one_right (norm_nonneg _) (d02GaussianTail_le_one _))
  have hsi : Integrable (d02SharpLogTest f) (d02TiltedDiagonalMeasure L) :=
    hfi.indicator d02SharpLogRegion_measurable
  have hbi : Integrable (fun y => d02CutBandMajorant n (d02LogCutCoordinate y))
      (d02TiltedDiagonalMeasure L) := by
    apply (integrable_const (1:ℝ)).mono'
      ((d02CutBandMajorant_continuous n).comp
        d02LogCutCoordinate_continuous).stronglyMeasurable.aestronglyMeasurable
    exact ae_of_all _ (fun y => by
      change ‖d02CutBandMajorant n (d02LogCutCoordinate y)‖ ≤ 1
      rw [Real.norm_of_nonneg (d02CutBandMajorant_nonneg n _)]
      exact d02CutBandMajorant_le_one n _)
  have hdom : ∀ᵐ y ∂d02TiltedDiagonalMeasure L,
      ‖f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) -
        d02SharpLogTest f y‖ ≤
      δ*B+B*d02CutBandMajorant n (d02LogCutCoordinate y) := by
    filter_upwards [hfB] with y hy
    have he : f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) -
        d02SharpLogTest f y = f y*
        ((d02GaussianLogWeight L (d02LogCutCoordinate y) c -
          if d02LogCutCoordinate y ≤ 1 then 1 else 0 : ℝ) : ℂ) := by
      by_cases hq : d02LogCutCoordinate y ≤ 1
      · simp [d02SharpLogTest, d02SharpLogRegion, hq, mul_sub]
      · simp [d02SharpLogTest, d02SharpLogRegion, hq]
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ B*(δ+d02CutBandMajorant n (d02LogCutCoordinate y)) :=
        mul_le_mul hy (hcut _) (abs_nonneg _) hB
      _ = _ := by ring
  rw [← integral_sub hgi hsi]
  calc
    _ ≤ ∫ y, ‖f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) -
        d02SharpLogTest f y‖ ∂d02TiltedDiagonalMeasure L := norm_integral_le_integral_norm _
    _ ≤ ∫ y, δ*B+B*d02CutBandMajorant n (d02LogCutCoordinate y)
        ∂d02TiltedDiagonalMeasure L :=
      integral_mono_ae (hgi.sub hsi).norm ((integrable_const (δ*B)).add
        (hbi.const_mul B)) hdom
    _ = _ := by
      rw [integral_add (integrable_const (δ*B)) (hbi.const_mul B)]
      simp only [integral_const_mul, integral_const, smul_eq_mul, mul_one]
      ring

/-- Uniform over all bounded measurable tests and all bounded physical
height offsets, for the finite actual D01 tilt. -/
theorem d02TiltedDiagonalMeasure_gaussian_sharp_uniform
    {B : ℝ} (hB : 0 < B) (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ (f : D01LogSpace → ℂ) (c : ℝ),
      Measurable f → (∀ᵐ y ∂d02TiltedDiagonalMeasure L, ‖f y‖ ≤ B) → |c| ≤ C →
      ‖(∫ y, f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)
        ∂d02TiltedDiagonalMeasure L) -
        ∫ y, d02SharpLogTest f y ∂d02TiltedDiagonalMeasure L‖ < ε := by
  let A := ∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedLimitMeasure
  have hA0 : 0 ≤ A := integral_nonneg (fun _ => by norm_num)
  obtain ⟨n, hn⟩ := (d02TiltedMeasure_band_mass_tendsto_zero.eventually_lt_const
    (show (0:ℝ) < ε/(4*B) by positivity)).exists
  let δ := ε/(4*B*(A+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hmass := d02TiltedDiagonalMeasure_mass_tendsto.eventually_lt_const
    (show (∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedLimitMeasure) < A+1 by
      dsimp [A]; linarith)
  have hbandmass := (d02TiltedDiagonalMeasure_band_tendsto n).eventually_lt_const
    (show (∫ y, d02CutBandMajorant n (d02LogCutCoordinate y)
      ∂d02TiltedLimitMeasure) < ε/(2*B) by
        have hd : 0 < ε/(4*B) := by positivity
        have he : ε/(2*B) = 2*(ε/(4*B)) := by
          field_simp [hB.ne']
          norm_num
        rw [he]
        linarith)
  filter_upwards [hmass, hbandmass, d02GaussianLogWeight_uniform_band_bound n hδ]
    with L hM hBand hG
  intro f c hfm hfB hc
  have h := d02TiltedGaussian_integral_difference_bound hB.le n
    (fun q => hG q c hc) f hfm hfB
  have hprod : δ*B*(∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedDiagonalMeasure L) < ε/4 := by
    have hm := mul_lt_mul_of_pos_left hM (mul_pos hδ hB)
    have he : δ*B*(A+1) = ε/4 := by
      dsimp [δ]
      field_simp [hB.ne', show A+1 ≠ 0 by positivity]
    rwa [he] at hm
  have hbprod : B*(∫ y, d02CutBandMajorant n (d02LogCutCoordinate y)
      ∂d02TiltedDiagonalMeasure L) < ε/2 := by
    have hm := mul_lt_mul_of_pos_left hBand hB
    have he : B*(ε/(2*B)) = ε/2 := by field_simp [hB.ne']
    rwa [he] at hm
  linarith

end
end Sechstmoment
