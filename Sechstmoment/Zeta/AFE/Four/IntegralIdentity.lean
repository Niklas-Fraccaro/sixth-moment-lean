import Sechstmoment.Zeta.AFE.Four.CompletedExpansion
import Sechstmoment.Zeta.AFE.Four.ContourSplit
import Sechstmoment.Zeta.AFE.Four.VerticalTails

/-! Uniform small-shift approximate functional equation from the finite
contour identity and independently proved edge and tail estimates. -/

namespace Sechstmoment.Source
open Complex MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

theorem fixedAFEHorizontalError_inverse_power_bound
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 16 ≤ t → ∀ α : MomentShifts,
      (∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) →
      ‖fixedAFEHorizontalError G α t‖ ≤ C * t ^ (-(A : ℝ)) := by
  obtain ⟨D, hD, hbound⟩ := bblrExplicitAFEIntegrand_horizontal_inverse_power_bound G hG A
  refine ⟨4 * ‖(1 / (2 * Real.pi) : ℂ)‖ * D, by positivity, ?_⟩
  intro t ht α hα
  have hedge (v : ℝ) (hv : |v| = t / 2) :
      ‖∫ c in (-1 : ℝ)..1,
        fixedAFEMellinIntegrand G α t ((c : ℂ) + (v : ℂ) * I)‖ ≤
        2 * D * t ^ (-(A : ℝ)) := by
    have hb (c : ℝ) (hc : c ∈ uIoc (-1 : ℝ) 1) :
        ‖fixedAFEMellinIntegrand G α t ((c : ℂ) + (v : ℂ) * I)‖ ≤
          D * t ^ (-(A : ℝ)) := by
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hc
      have hcabs : |c| ≤ 1 := abs_le.mpr ⟨hc.1.le, hc.2⟩
      unfold fixedAFEMellinIntegrand
      rw [fixedAFECompletedKernel_div_eq_explicit_on_rectangle G t ht α hα
        (by simpa [fixedAFERectangle, hv] using And.intro hcabs hv.le)]
      exact hbound t c v ht hcabs hv α hα
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have hlen : |(1 : ℝ) - -1| = 2 := by norm_num
    rw [hlen] at hh
    exact hh.trans_eq (by ring)
  have hbottom := hedge (-t / 2) (by rw [neg_div, abs_neg, abs_of_nonneg (by linarith)])
  have htop := hedge (t / 2) (abs_of_nonneg (by linarith))
  unfold fixedAFEHorizontalError
  rw [norm_mul, norm_mul, norm_neg, norm_I, mul_one]
  calc
    _ ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ *
        (‖∫ c in (-1 : ℝ)..1,
          fixedAFEMellinIntegrand G α t ((c : ℂ) + ((-t / 2 : ℝ) : ℂ) * I)‖ +
         ‖∫ c in (-1 : ℝ)..1,
          fixedAFEMellinIntegrand G α t ((c : ℂ) + (t / 2 : ℂ) * I)‖) := by
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ *
        (2 * D * t ^ (-(A : ℝ)) + 2 * D * t ^ (-(A : ℝ))) := by
      gcongr
      simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using htop
    _ = _ := by ring

theorem fixedAFEVerticalTail_inverse_power_bound
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 16 ≤ t → ∀ α : MomentShifts,
      (∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) →
      ‖fixedAFEVerticalTail G α t‖ ≤ C * t ^ (-(A : ℝ)) := by
  obtain ⟨D, hD, hbound⟩ := bblrExplicitAFEIntegral_right_tail G hG A
  refine ⟨D, hD, ?_⟩
  intro t ht α hα
  have he (v : ℝ) : fixedAFEMellinIntegrand G α t (1 + (v : ℂ) * I) =
      bblrExplicitAFEIntegrand G α t (1 + (v : ℂ) * I) :=
    fixedAFECompletedKernel_div_eq_explicit_rightLine G t α hα v
  unfold fixedAFEVerticalTail
  simp_rw [he]
  rw [mul_sub, intervalIntegral.integral_of_le (by linarith : -t / 2 ≤ t / 2),
    ← integral_Icc_eq_integral_Ioc]
  exact hbound t ht α hα

/-- Uniform arbitrary-order AFE on a fixed box of raw shifts. -/
theorem fixedAFE_uniform_smallShifts
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 16 ≤ t → ∀ α : MomentShifts,
      (∀ j : Fin 4, ‖α j‖ ≤ (1 / 4 : ℝ)) →
      ‖bblrAFEDiscrepancy G α t‖ ≤ C * t ^ (-(A : ℝ)) := by
  obtain ⟨H, hH, hhorizontal⟩ := fixedAFEHorizontalError_inverse_power_bound G hG A
  obtain ⟨R, hR, hright⟩ := fixedAFEVerticalTail_inverse_power_bound G hG A
  obtain ⟨L, hL, hdual⟩ := fixedAFEVerticalTail_inverse_power_bound G hG (A + 8)
  obtain ⟨X, hX, hmultiplier⟩ := bblrDualMultiplier_polynomial_bound
  refine ⟨H + R + X * 2 ^ 8 * L, by positivity, ?_⟩
  intro t ht α hα
  have ht0 : 0 < t := by linarith
  have hαdual : ∀ j : Fin 4, ‖bblrSixShifts α 1 j‖ ≤ (1 / 4 : ℝ) := by
    intro j
    fin_cases j
    · simpa [bblrSixShifts] using hα 2
    · simpa [bblrSixShifts] using hα 3
    · simpa [bblrSixShifts] using hα 0
    · simpa [bblrSixShifts] using hα 1
  have hmult : ‖bblrDualMultiplier t α‖ ≤ (X * 2 ^ 8) * t ^ 8 := by
    calc
      _ ≤ X * (1 + t) ^ 8 := hmultiplier t ht α hα
      _ ≤ X * (2 * t) ^ 8 := by gcongr; linarith
      _ = _ := by rw [mul_pow]; ring
  have hpower : t ^ 8 * t ^ (-((A + 8 : ℕ) : ℝ)) = t ^ (-(A : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
    congr 1
    push_cast
    ring
  have hdualtail :
      ‖bblrDualMultiplier t α * fixedAFEVerticalTail G (bblrSixShifts α 1) t‖ ≤
        (X * 2 ^ 8 * L) * t ^ (-(A : ℝ)) := by
    rw [norm_mul]
    calc
      _ ≤ ((X * 2 ^ 8) * t ^ 8) * (L * t ^ (-((A + 8 : ℕ) : ℝ))) := by
        exact mul_le_mul hmult (hdual t ht (bblrSixShifts α 1) hαdual)
          (norm_nonneg (fixedAFEVerticalTail G (bblrSixShifts α 1) t)) (by positivity)
      _ = (X * 2 ^ 8 * L) * (t ^ 8 * t ^ (-((A + 8 : ℕ) : ℝ))) := by ring
      _ = _ := by rw [hpower]
  rw [fixedAFE_discrepancy_eq_three_errors G hG t ht α hα]
  calc
    _ ≤ ‖fixedAFEHorizontalError G α t - fixedAFEVerticalTail G α t‖ +
        ‖bblrDualMultiplier t α * fixedAFEVerticalTail G (bblrSixShifts α 1) t‖ :=
      norm_sub_le _ _
    _ ≤ (‖fixedAFEHorizontalError G α t‖ + ‖fixedAFEVerticalTail G α t‖) +
        ‖bblrDualMultiplier t α * fixedAFEVerticalTail G (bblrSixShifts α 1) t‖ := by
      exact add_le_add
        (norm_sub_le (fixedAFEHorizontalError G α t) (fixedAFEVerticalTail G α t)) (le_refl _)
    _ ≤ (H * t ^ (-(A : ℝ)) + R * t ^ (-(A : ℝ))) +
        (X * 2 ^ 8 * L) * t ^ (-(A : ℝ)) := by
      gcongr
      · exact hhorizontal t ht α hα
      · exact hright t ht α hα
    _ = _ := by ring

end
end Sechstmoment.Source
