import Sechstmoment.Certificate.Exact.Ratio
import Sechstmoment.Certificate.Profiles.DenominatorLimit

/-! The scalar concentration step closes with one common fixed admissible
profile stage. Both exact certificate cutoffs and the strict ratio are retained.
No asymptotic statement about an actual zeta Gram moment is a premise here. -/

namespace Sechstmoment
open Filter
open scoped Topology
noncomputable section

/-- The actual scalar numerator and denominator at a common profile stage. -/
def certificateProfileRatio (n : ℕ) : ℝ :=
  362880 * certificateProfileNumerator n ^ 2 / certificateProfileDenominator n

/-- Concentration of both scalar kernels recovers the exact finite ratio. -/
theorem certificateProfileRatio_tendsto :
    Tendsto certificateProfileRatio atTop
      (𝓝 (362880 * (finiteNumerator : ℝ)^2 / (Finite.finiteDenominator : ℝ))) := by
  have hd : (Finite.finiteDenominator : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (Finite.finiteDenominator : ℝ) := by
      exact_mod_cast Finite.finite_denominator_pos
    exact hpos.ne'
  exact (tendsto_const_nhds.mul (certificateProfileNumerator_tendsto.pow 2)).div
    certificateProfileDenominator_tendsto hd

/-- Eventually every scalar certificate condition holds at the same stage,
including the common V-stage lower bound and the strict declared ratio. -/
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

/-- A single fixed stage meets all original numerical certificate bounds.
The subsequent height limit can therefore be taken with this stage fixed. -/
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
