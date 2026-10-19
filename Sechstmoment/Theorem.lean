import Sechstmoment.Analysis.Dyadic.Weights
import Sechstmoment.Certificate.Profiles.CommonIndex
import Sechstmoment.Final.DyadicAsymptotic
import Sechstmoment.LiteratureAssumption

/-! The original sixth-moment theorem from Watt Proposition 4.1.
The fixed-weight approximate functional equation and the required V limits
are proved internally.
No moment asymptotic, positive Gram condition, or desired conclusion is
an additional premise. The original certificate and main goal are unchanged. -/

namespace Sechstmoment
open Filter MeasureTheory
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

/-- F01 closes with a fixed stage, a fixed weight and a finite dyadic sum. -/
theorem f01NormalizedSixthMoment_eventually_gt_declared
    (hSource : DivisorProof.Watt41) :
    ∀ᶠ T : ℝ in atTop, (declaredBound : ℝ) < normalizedSixthMoment T := by
  obtain ⟨n, hn, hD, _hN, _hDU, hR⟩ := certificateProfile_common_stage_exists
  have hB : 0 < (declaredBound : ℝ) := by norm_num [declaredBound]
  have hRp : 0 < certificateProfileRatio n := hB.trans hR
  have hq0 : 0 < (declaredBound : ℝ)/certificateProfileRatio n := div_pos hB hRp
  have hq1 : (declaredBound : ℝ)/certificateProfileRatio n < 1 :=
    (div_lt_one hRp).mpr hR
  obtain ⟨Φ, hΦ, hΦpos, hΦle, hmass⟩ := exists_smoothDyadicWeight_mass_gt hq0 hq1
  have hI : 0 < ∫ x : ℝ, Φ x := hq0.trans hmass
  have hIR : (declaredBound : ℝ) < (∫ x : ℝ, Φ x)*certificateProfileRatio n :=
    (div_lt_iff₀ hRp).mp hmass
  have hgeom : Tendsto (fun J : ℕ =>
      (∫ x : ℝ, Φ x)*certificateProfileRatio n*(1-(1/2 : ℝ)^J)) atTop
      (𝓝 ((∫ x : ℝ, Φ x)*certificateProfileRatio n)) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (𝓝 (1 : ℝ))).sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1))).const_mul
          ((∫ x : ℝ, Φ x)*certificateProfileRatio n)
  obtain ⟨J, hJ⟩ := ((tendsto_order.mp hgeom).1 _ hIR).exists
  have hl := f01FiniteDyadicLowerBound_tendsto hSource n hn J
    Φ hΦ hΦpos hI hD
  filter_upwards [(tendsto_order.mp hl).1 _ hJ,
    f01FiniteDyadicLowerBound_eventually_le n hn J Φ hΦ hΦpos hΦle hI hD]
      with T hlt hle
  exact hlt.trans_le hle

/-- The requested original EReal liminf conclusion. -/
theorem f01MainClaim
    (hSource : DivisorProof.Watt41) : MainClaim := by
  refine le_liminf_of_le (h := ?_)
  filter_upwards [f01NormalizedSixthMoment_eventually_gt_declared hSource] with T hT
  exact EReal.coe_le_coe_iff.mpr hT.le

/-- Complete original theorem, with only Watt Proposition 4.1. -/
theorem fullProof : LiteratureRelativeGoal := by
  intro hSource
  exact ⟨arithmeticFactor_wellDefined, f01MainClaim hSource⟩

end
end Sechstmoment
