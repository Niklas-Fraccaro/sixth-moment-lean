import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Sechstmoment.Denominator.Balanced.GaussianCutBand

/-! A moving Gaussian cutoff for the actual D01 measures.  The convergence
is uniform over bounded height offsets and all measurable tests dominated
by one continuous compact majorant.  The only discontinuity is the already
proved null hyperplane, and the majorant masses come from actual D01.
-/

namespace Sechstmoment
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 0

theorem d02DiagonalMeasure_real_compact_tendsto (H : D01LogSpace → ℝ)
    (hH : Continuous H) (hK : HasCompactSupport H) :
    Tendsto (fun L : ℝ => ∫ y, H y ∂d01DiagonalMeasure L) atTop
      (𝓝 (∫ y, H y ∂d01LimitMeasure)) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuous hH
  have hc : Continuous (fun y => (H y : ℂ)) := Complex.continuous_ofReal.comp hH
  have hKc : HasCompactSupport (fun y => (H y : ℂ)) :=
    hK.comp_left (g := fun t : ℝ => (t:ℂ)) (by simp)
  have h := d01DiagonalMeasure_bounded_compact_tendsto (fun y => (H y : ℂ))
    hc.measurable (ae_of_all _ (fun _ => hc.continuousAt)) hKc
    (fun y => by simpa only [Complex.norm_real] using hB y)
  have hr := (Complex.continuous_re.tendsto _).comp h
  simpa only [Function.comp_def, integral_complex_ofReal, Complex.ofReal_re] using hr

/-- The mass of the continuous shrinking band vanishes for the actual
nine-edge limit. -/
theorem d02LimitMeasure_compact_band_mass_tendsto_zero
    (H : D01LogSpace → ℝ) (hH : Continuous H) (hK : HasCompactSupport H)
    (hH0 : ∀ y, 0 ≤ H y) :
    Tendsto (fun n : ℕ => ∫ y,
      H y*d02CutBandMajorant n (d02LogCutCoordinate y) ∂d01LimitMeasure)
      atTop (𝓝 0) := by
  have hlim : ∀ᵐ y ∂d01LimitMeasure, Tendsto (fun n : ℕ =>
      H y*d02CutBandMajorant n (d02LogCutCoordinate y)) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [d02LimitMeasure_ae_off_cut_boundary] with y hy
    simpa using (d02CutBandMajorant_tendsto_zero hy).const_mul (H y)
  have ht := tendsto_integral_of_dominated_convergence H
    (fun n => ((hH.mul ((d02CutBandMajorant_continuous n).comp
      d02LogCutCoordinate_continuous)).stronglyMeasurable.aestronglyMeasurable))
    (d01LimitMeasure_compact_test_integrable H hH hK)
    (fun n => ae_of_all _ (fun y => by
      change ‖H y*d02CutBandMajorant n (d02LogCutCoordinate y)‖ ≤ H y
      rw [Real.norm_of_nonneg (mul_nonneg (hH0 y)
        (d02CutBandMajorant_nonneg n _))]
      exact mul_le_of_le_one_right (hH0 y) (d02CutBandMajorant_le_one n _))) hlim
  simpa using ht

private theorem d02Gaussian_integral_difference_bound
    (H : D01LogSpace → ℝ) (hH : Continuous H) (hK : HasCompactSupport H)
    (hH0 : ∀ y, 0 ≤ H y) {L δ c : ℝ} (hL : 0 < L)
    (n : ℕ) (hcut : ∀ q,
      |d02GaussianLogWeight L q c - if q ≤ 1 then 1 else 0| ≤
        δ+d02CutBandMajorant n q)
    (f : D01LogSpace → ℂ) (hfm : Measurable f) (hfH : ∀ y, ‖f y‖ ≤ H y) :
    ‖(∫ y, f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)
      ∂d01DiagonalMeasure L) -
      ∫ y, d02SharpLogTest f y ∂d01DiagonalMeasure L‖ ≤
        δ*(∫ y, H y ∂d01DiagonalMeasure L) +
          ∫ y, H y*d02CutBandMajorant n (d02LogCutCoordinate y)
            ∂d01DiagonalMeasure L := by
  have hHi := d01DiagonalMeasure_compact_test_integrable hL H hH hK
  have hfi : Integrable f (d01DiagonalMeasure L) :=
    hHi.mono' hfm.aestronglyMeasurable (ae_of_all _ hfH)
  have hgm : Measurable (fun y : D01LogSpace =>
      (d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)) :=
    Complex.measurable_ofReal.comp ((d02GaussianLogWeight_measurable L c).comp
      d02LogCutCoordinate_continuous.measurable)
  have hgi : Integrable (fun y =>
      f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ))
      (d01DiagonalMeasure L) := by
    apply hfi.norm.mono' (hfm.mul hgm).aestronglyMeasurable
    exact ae_of_all _ (fun y => by
      change ‖f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)‖ ≤ ‖f y‖
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ d02GaussianLogWeight L (d02LogCutCoordinate y) c from
        d02GaussianTail_nonneg _)]
      exact mul_le_of_le_one_right (norm_nonneg _) (d02GaussianTail_le_one _))
  have hsi : Integrable (d02SharpLogTest f) (d01DiagonalMeasure L) :=
    hfi.indicator d02SharpLogRegion_measurable
  have hbi := d01DiagonalMeasure_compact_test_integrable hL
    (fun y => H y*d02CutBandMajorant n (d02LogCutCoordinate y))
    (hH.mul ((d02CutBandMajorant_continuous n).comp d02LogCutCoordinate_continuous))
    hK.mul_right
  have hdom : ∀ y, ‖f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) -
      d02SharpLogTest f y‖ ≤
      δ*H y+H y*d02CutBandMajorant n (d02LogCutCoordinate y) := by
    intro y
    have he : f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) -
        d02SharpLogTest f y = f y*
        ((d02GaussianLogWeight L (d02LogCutCoordinate y) c -
          if d02LogCutCoordinate y ≤ 1 then 1 else 0 : ℝ) : ℂ) := by
      by_cases hy : d02LogCutCoordinate y ≤ 1
      · simp [d02SharpLogTest, d02SharpLogRegion, hy, mul_sub]
      · simp [d02SharpLogTest, d02SharpLogRegion, hy]
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ H y*(δ+d02CutBandMajorant n (d02LogCutCoordinate y)) :=
        mul_le_mul (hfH y) (hcut _) (abs_nonneg _) (hH0 y)
      _ = _ := by ring
  rw [← integral_sub hgi hsi]
  calc
    _ ≤ ∫ y, ‖f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) -
        d02SharpLogTest f y‖ ∂d01DiagonalMeasure L := norm_integral_le_integral_norm _
    _ ≤ ∫ y, δ*H y+H y*d02CutBandMajorant n (d02LogCutCoordinate y)
        ∂d01DiagonalMeasure L :=
      integral_mono (hgi.sub hsi).norm ((hHi.const_mul δ).add hbi) hdom
    _ = _ := by rw [integral_add (hHi.const_mul δ) hbi, integral_const_mul]

/-- Uniform moving-cut convergence for the actual arithmetic D01 measures.
The test may itself vary: one fixed compact majorant controls all tests. -/
theorem d02DiagonalMeasure_gaussian_sharp_compact_uniform
    (H : D01LogSpace → ℝ) (hH : Continuous H) (hK : HasCompactSupport H)
    (hH0 : ∀ y, 0 ≤ H y) (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ (f : D01LogSpace → ℂ) (c : ℝ),
      Measurable f → (∀ y, ‖f y‖ ≤ H y) → |c| ≤ C →
      ‖(∫ y, f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)
        ∂d01DiagonalMeasure L) -
        ∫ y, d02SharpLogTest f y ∂d01DiagonalMeasure L‖ < ε := by
  let A := ∫ y, H y ∂d01LimitMeasure
  have hA0 : 0 ≤ A := integral_nonneg hH0
  have hband := d02LimitMeasure_compact_band_mass_tendsto_zero H hH hK hH0
  obtain ⟨n, hn⟩ := (hband.eventually_lt_const (by linarith : (0:ℝ) < ε/4)).exists
  let δ := ε/(4*(A+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hmass := (d02DiagonalMeasure_real_compact_tendsto H hH hK).eventually_lt_const
    (show (∫ y, H y ∂d01LimitMeasure) < A+1 by dsimp [A]; linarith)
  have hbandmass := (d02DiagonalMeasure_real_compact_tendsto
    (fun y => H y*d02CutBandMajorant n (d02LogCutCoordinate y))
    (hH.mul ((d02CutBandMajorant_continuous n).comp d02LogCutCoordinate_continuous))
    hK.mul_right).eventually_lt_const (show
      (∫ y, H y*d02CutBandMajorant n (d02LogCutCoordinate y) ∂d01LimitMeasure) <
        ε/2 by linarith)
  filter_upwards [hmass, hbandmass, d02GaussianLogWeight_uniform_band_bound n hδ,
    eventually_gt_atTop (0:ℝ)] with L hM hB hG hL
  intro f c hfm hfH hc
  have h := d02Gaussian_integral_difference_bound H hH hK hH0 hL n
    (fun q => hG q c hc) f hfm hfH
  have hprod : δ*(∫ y, H y ∂d01DiagonalMeasure L) < ε/4 := by
    have hm := mul_lt_mul_of_pos_left hM hδ
    have he : δ*(A+1) = ε/4 := by
      dsimp [δ]
      field_simp [show A+1 ≠ 0 by positivity]
    rwa [he] at hm
  linarith

end
end Sechstmoment
