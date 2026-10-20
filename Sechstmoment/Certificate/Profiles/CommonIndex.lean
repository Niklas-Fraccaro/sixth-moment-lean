import Sechstmoment.Certificate.Exact.Ratio
import Sechstmoment.Certificate.Profiles.DenominatorLimit


namespace Sechstmoment
open Filter
open scoped Topology
noncomputable section

def certificateProfileRatio (n : ℕ) : ℝ :=
  362880 * certificateProfileNumerator n ^ 2 / certificateProfileDenominator n

theorem certificateProfileRatio_tendsto :
    Tendsto certificateProfileRatio atTop
      (𝓝 (362880 * (finiteNumerator : ℝ)^2 / (Finite.finiteDenominator : ℝ))) := by
  have hd : (Finite.finiteDenominator : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (Finite.finiteDenominator : ℝ) := by
      exact_mod_cast Finite.finite_denominator_pos
    exact hpos.ne'
  exact (tendsto_const_nhds.mul (certificateProfileNumerator_tendsto.pow 2)).div
    certificateProfileDenominator_tendsto hd

theorem certificateProfile_common_stage_eventually :
    ∀ᶠ n : ℕ in atTop, 12 ≤ n ∧
      0 < certificateProfileDenominator n ∧
      (numeratorLower : ℝ) < certificateProfileNumerator n ∧
      certificateProfileDenominator n < (denominatorUpper : ℝ) ∧
      (declaredBound : ℝ) < certificateProfileRatio n := by
  have hn : (numeratorLower : ℝ) < (finiteNumerator : ℝ) := by
    have h : numeratorLower < finiteNumerator := by
      simpa only [numeratorLower] using finite_numerator_gt_lower
    exact_mod_cast h
  have hd : (0 : ℝ) < (Finite.finiteDenominator : ℝ) := by
    exact_mod_cast Finite.finite_denominator_pos
  have hdu : (Finite.finiteDenominator : ℝ) < (denominatorUpper : ℝ) := by
    exact_mod_cast Finite.finite_denominator_lt_upper
  have hr : (declaredBound : ℝ) <
      362880 * (finiteNumerator : ℝ)^2 / (Finite.finiteDenominator : ℝ) := by
    exact_mod_cast finite_certificate_ratio
  have hN := (tendsto_order.mp certificateProfileNumerator_tendsto).1 _ hn
  have hD := (tendsto_order.mp certificateProfileDenominator_tendsto).1 _ hd
  have hDU := (tendsto_order.mp certificateProfileDenominator_tendsto).2 _ hdu
  have hR := (tendsto_order.mp certificateProfileRatio_tendsto).1 _ hr
  filter_upwards [eventually_ge_atTop (12 : ℕ), hD, hN, hDU, hR] with n hs hd' hn' hdu' hr'
  exact ⟨hs, hd', hn', hdu', hr'⟩

theorem certificateProfile_common_stage_exists :
    ∃ n : ℕ, 12 ≤ n ∧
      0 < certificateProfileDenominator n ∧
      (numeratorLower : ℝ) < certificateProfileNumerator n ∧
      certificateProfileDenominator n < (denominatorUpper : ℝ) ∧
      (declaredBound : ℝ) <
        362880 * certificateProfileNumerator n ^ 2 / certificateProfileDenominator n :=
  certificateProfile_common_stage_eventually.exists

end
end Sechstmoment
