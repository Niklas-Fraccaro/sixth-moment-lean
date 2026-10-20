import Mathlib.Analysis.Normed.Group.Bounded
import Sechstmoment.Numerator.V.DP.DPPolynomialPolarization


namespace Sechstmoment
open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 0

private theorem compact_raw_shifts_eventually_real_small
    (K : Set MomentShifts) (hK : IsCompact K) :
    ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ j, |(rawMomentShifts T σ j).re| < 1/2 := by
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop (2*max B 0+1))] with T hT
  intro σ hσ j
  have hL : 0 < Real.log T := by linarith [le_max_right B 0]
  have hj : |(σ j).re| ≤ max B 0 :=
    ((Complex.abs_re_le_norm _).trans ((norm_le_pi_norm σ j).trans (hB σ hσ))).trans
      (le_max_left B 0)
  simp only [rawMomentShifts, Complex.div_ofReal_re, abs_div, abs_of_pos hL]
  apply (div_lt_iff₀ hL).mpr
  linarith

namespace Source
noncomputable section

def dpRawBilinearMainTerm (T η : ℝ) (P Q : Polynomial ℝ) (Φ : ℝ → ℝ)
    (α : MomentShifts) : ℂ :=
  (1/4:ℂ)*(dpRawMainTerm T η (P+Q) Φ α-dpRawMainTerm T η (P-Q) Φ α)

theorem dpRawBilinearMainTerm_normalized {T : ℝ} (hT : 1 < T) (η : ℝ)
    (P Q : Polynomial ℝ) (Φ : ℝ → ℝ) (σ : MomentShifts) :
    dpRawBilinearMainTerm T η P Q Φ (rawMomentShifts T σ)/
        ((T:ℂ)*(Real.log T:ℂ)^9) =
      (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*(η:ℂ)^6*
        dpNormalizedBilinearFourResidues
          (Real.log (T/(2*Real.pi))/Real.log T) η P Q σ := by
  unfold dpRawBilinearMainTerm
  rw [mul_div_assoc, sub_div, dpRawMainTerm_normalized hT,
    dpRawMainTerm_normalized hT, dpNormalizedBilinearFourResidues_polarization]
  ring

theorem dpActualBilinearMoment_source_error (hsource : DPv2Input)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P Q : Polynomial ℝ)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (K : Set MomentShifts) (hK : IsCompact K) (hsep : ∀ σ ∈ K, DPSeparated σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      ‖chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ-
          dpRawBilinearMainTerm T η P Q Φ (rawMomentShifts T σ)‖ ≤
        C*T*(Real.log T)^8 := by
  obtain ⟨Cp, hCp0, hCp⟩ := hsource η hη hηu (P+Q) Φ hΦ K hK hsep
  obtain ⟨Cm, hCm0, hCm⟩ := hsource η hη hηu (P-Q) Φ hΦ K hK hsep
  refine ⟨(1/4)*(Cp+Cm), by positivity, ?_⟩
  filter_upwards [hCp, hCm, eventually_gt_atTop (1:ℝ),
    compact_raw_shifts_eventually_real_small K hK] with T hp hm hT hα
  intro σ hσ
  have hmoment := chiTwistedFourthMoment_polarization hT η (rawMomentShifts T σ)
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ (hα σ hσ)
    (fun x hx => zeroExtendedPolynomialProfile_zero_above η P x hx)
    (fun x hx => zeroExtendedPolynomialProfile_zero_above η Q x hx) hΦ
  rw [← zeroExtendedPolynomialProfile_add, ← zeroExtendedPolynomialProfile_sub] at hmoment
  have he : chiTwistedFourthMoment T (rawMomentShifts T σ)
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q) Φ-
        dpRawBilinearMainTerm T η P Q Φ (rawMomentShifts T σ) =
      (1/4:ℂ)*((chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η (P+Q)) (zeroExtendedPolynomialProfile η (P+Q)) Φ-
          dpRawMainTerm T η (P+Q) Φ (rawMomentShifts T σ))-
        (chiTwistedFourthMoment T (rawMomentShifts T σ)
          (zeroExtendedPolynomialProfile η (P-Q)) (zeroExtendedPolynomialProfile η (P-Q)) Φ-
            dpRawMainTerm T η (P-Q) Φ (rawMomentShifts T σ))) := by
    rw [hmoment]
    unfold dpRawBilinearMainTerm
    ring
  rw [he, norm_mul]
  have hnorm : ‖(1/4:ℂ)‖ = (1/4:ℝ) := by norm_num
  rw [hnorm]
  calc
    _ ≤ (1/4:ℝ)*(_+_) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ (1/4:ℝ)*(Cp*T*(Real.log T)^8+Cm*T*(Real.log T)^8) := by
      gcongr
      · exact hp σ hσ
      · exact hm σ hσ
    _ = _ := by ring

end
end Source
end Sechstmoment
