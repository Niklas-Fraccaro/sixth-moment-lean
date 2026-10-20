import Mathlib.Analysis.SpecificLimits.Basic
import SixthMoment.Final.CertificateLimit
import SixthMoment.Final.DyadicLowerBound


namespace SixthMoment
open Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1000000

def f01FiniteDyadicLowerBound (n J : ℕ) (T : ℝ) (Φ : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range J,
    (‖actual250ProjectedMixedMoment n (T/(2 : ℝ)^(j+1)) Φ‖^2/
      actual250ProjectedGramMoment n (T/(2 : ℝ)^(j+1)) Φ)/f01SixthMomentScale T

theorem f01FiniteDyadicLowerBound_tendsto
    (hSource : DivisorProof.Watt41)
    (n : ℕ) (hn : 12 ≤ n) (J : ℕ)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x, 0 ≤ Φ x)
    (hI : 0 < ∫ x : ℝ, Φ x) (hD : 0 < certificateProfileDenominator n) :
    Tendsto (fun T : ℝ => f01FiniteDyadicLowerBound n J T Φ) atTop
      (𝓝 ((∫ x : ℝ, Φ x)*(362880 * certificateProfileNumerator n ^ 2 / certificateProfileDenominator n)*(1-(1/2 : ℝ)^J))) := by
  have hj (j : ℕ) : Tendsto (fun T : ℝ =>
      (‖actual250ProjectedMixedMoment n (T/(2 : ℝ)^(j+1)) Φ‖^2/
        actual250ProjectedGramMoment n (T/(2 : ℝ)^(j+1)) Φ)/f01SixthMomentScale T) atTop
      (𝓝 (((∫ x : ℝ, Φ x)*(362880 * certificateProfileNumerator n ^ 2 / certificateProfileDenominator n))*(1/(2 : ℝ)^(j+1)))) := by
    have hc : 0 < (2 : ℝ)^(j+1) := by positivity
    have ht : Tendsto (fun T : ℝ => T/(2 : ℝ)^(j+1)) atTop atTop :=
      tendsto_id.atTop_div_const hc
    have h := ((f01CertificateLowerBound_tendsto hSource n hn
      Φ hΦ hΦpos hI hD).comp ht).mul (f01ScaleRatio_tendsto hc)
    apply h.congr'
    filter_upwards [ht.eventually (eventually_gt_atTop (1 : ℝ))] with T hT
    have hs := f01SixthMomentScale_pos hT
    simp only [Function.comp_apply, f01CertificateLowerBound]
    field_simp [hs.ne']
  have h := tendsto_finsetSum (Finset.range J) (fun j _ => hj j)
  have he : (∑ j ∈ Finset.range J,
      ((∫ x : ℝ, Φ x)*(362880 * certificateProfileNumerator n ^ 2 / certificateProfileDenominator n))*(1/(2 : ℝ)^(j+1))) =
      (∫ x : ℝ, Φ x)*(362880 * certificateProfileNumerator n ^ 2 / certificateProfileDenominator n)*(1-(1/2 : ℝ)^J) := by
    rw [← Finset.mul_sum, f01DyadicMass]
  rw [he] at h
  exact h

theorem f01FiniteDyadicLowerBound_eventually_le (n : ℕ) (hn : 12 ≤ n) (J : ℕ)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x, 0 ≤ Φ x)
    (hΦle : ∀ x, Φ x ≤ 1) (hI : 0 < ∫ x : ℝ, Φ x)
    (hD : 0 < certificateProfileDenominator n) :
    ∀ᶠ T : ℝ in atTop, f01FiniteDyadicLowerBound n J T Φ ≤ normalizedSixthMoment T := by
  have hg : ∀ᶠ T : ℝ in atTop, ∀ j ∈ Finset.range J,
      0 < actual250ProjectedGramMoment n (T/(2 : ℝ)^(j+1)) Φ := by
    apply (Finset.eventually_all _).mpr
    intro j _
    exact (tendsto_id.atTop_div_const (by positivity : 0 < (2 : ℝ)^(j+1))).eventually
      (f01ActualGram_eventually_pos n hn Φ hΦ hΦpos hI hD)
  filter_upwards [hg, eventually_gt_atTop ((2 : ℝ)^J), eventually_gt_atTop (1 : ℝ)]
    with T hG hT hT1
  have h := actual250ProjectedMixedMoment_finite_dyadic_lower_bound n (by omega) J
    hT Φ hΦ hΦpos hΦle (fun j hj => hG j (Finset.mem_range.mpr hj))
  have hd := div_le_div_of_nonneg_right h (f01SixthMomentScale_pos hT1).le
  simpa only [f01FiniteDyadicLowerBound, normalizedSixthMoment, f01SixthMomentScale,
    Finset.sum_div] using hd

end
end SixthMoment
