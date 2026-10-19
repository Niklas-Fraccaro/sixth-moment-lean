import Sechstmoment.Numerator.V.Chi.KernelDecay
import Sechstmoment.Numerator.V.Chi.KernelMain
import Sechstmoment.Numerator.V.Chi.KernelTruncation

/-! Main and far-frequency estimates for the actual untruncated chi kernel. -/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped FourierTransform
noncomputable section

theorem noDPChiTimeTransform_main_error (h : SchwartzMap ℝ ℂ)
    (hs : tsupport (𝓕⁻ (h:ℝ → ℂ)) ⊆ Icc (1:ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 3 (100*Real.pi) ≤ T →
      ∀ c ∈ Icc (1:ℝ) (15/8), ∀ r : ℝ, 0 < r →
      ‖noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T c 0 r-
        Complex.exp (I*((-2*Real.pi*r:ℝ):ℂ))*𝓕⁻ (h:ℝ → ℂ) (2*Real.pi*r/T)‖ ≤
        C*(r^(-c)/T^2+1/T+r/T^2) := by
  obtain ⟨D,hD,hcut⟩ := noDPChiTimeTransform_cutoff_error h hs
  obtain ⟨E,hE,hmain⟩ := noDPChiBandTransform_main_error h hs
  refine ⟨D+E+1,by positivity,?_⟩
  intro T hT c hc r hr
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ) < 3) ((le_max_left _ _).trans hT)
  have hc0 : 0 < c := by linarith [hc.1]
  have hc2 : |c| ≤ 2 := by rw [abs_of_pos hc0]; linarith [hc.2]
  have Hcut := hcut T hT c ⟨by linarith [hc.1],hc.2⟩ r hr
  have Hmain := hmain T hT0 c hc0 hc2 r hr
  apply (norm_sub_le_norm_sub_add_norm_sub _ (noDPChiBandTransform h T c r) _).trans
  apply (add_le_add Hcut Hmain).trans
  have hp : 0 ≤ r^(-c)/T^2 := by positivity
  have hq : 0 ≤ 1/T+r/T^2 := by positivity
  calc
    _ = D*(r^(-c)/T^2)+E*(1/T+r/T^2) := by ring
    _ ≤ (D+E+1)*(r^(-c)/T^2)+(D+E+1)*(1/T+r/T^2) :=
      add_le_add (mul_le_mul_of_nonneg_right (by linarith) hp)
        (mul_le_mul_of_nonneg_right (by linarith) hq)
    _ = _ := by ring

theorem noDPChiTimeTransform_far_bound (h : SchwartzMap ℝ ℂ)
    (hs : tsupport (𝓕⁻ (h:ℝ → ℂ)) ⊆ Icc (1:ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 3 (100*Real.pi) ≤ T →
      ∀ c ∈ Icc (1:ℝ) (15/8), ∀ r : ℝ, 0 < r →
      ‖noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T c 0 r‖ ≤
        C*(r^(-c)/T^2+T^9/r^8) := by
  obtain ⟨D,hD,hcut⟩ := noDPChiTimeTransform_cutoff_error h hs
  obtain ⟨E,hE,hfar⟩ := noDPChiBandTransform_eighth_decay h
  refine ⟨D+E+1,by positivity,?_⟩
  intro T hT c hc r hr
  have hT1 : 1 ≤ T := le_trans (by norm_num : (1:ℝ) ≤ 3) ((le_max_left _ _).trans hT)
  have Hcut := hcut T hT c ⟨by linarith [hc.1],hc.2⟩ r hr
  have Hfar := hfar T hT1 c ⟨hc.1,by linarith [hc.2]⟩ r hr
  have H := norm_sub_le_norm_sub_add_norm_sub (noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T c 0 r)
    (noDPChiBandTransform h T c r) 0
  simp only [sub_zero] at H
  apply (H.trans (add_le_add Hcut Hfar)).trans
  have hp : 0 ≤ r^(-c)/T^2 := by positivity
  have hq : 0 ≤ T^9/r^8 := by positivity
  calc
    _ = D*(r^(-c)/T^2)+E*(T^9/r^8) := by ring
    _ ≤ (D+E+1)*(r^(-c)/T^2)+(D+E+1)*(T^9/r^8) :=
      add_le_add (mul_le_mul_of_nonneg_right (by linarith) hp)
        (mul_le_mul_of_nonneg_right (by linarith) hq)
    _ = _ := by ring

end
end Sechstmoment.Source
