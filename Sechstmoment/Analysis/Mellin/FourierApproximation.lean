import Sechstmoment.Analysis.Mellin.FourierCutoffDecay

/-! Arbitrary-power uniform approximation by the actual smooth frequency
cutoff. No Fourier approximation theorem is assumed. -/

namespace Sechstmoment.Source
open Complex Real MeasureTheory
open scoped FourierTransform
noncomputable section

theorem noDPFourierCutoff_inverse_error (h : SchwartzMap ℝ ℂ)
    {H : ℝ} (hH : 0 < H) (M : ℕ) (x : ℝ) :
    H^M*‖𝓕⁻ (noDPFourierCutoff h H) x-𝓕⁻ (h:ℝ → ℂ) x‖ ≤
      ∫ ξ : ℝ, |ξ|^M*‖h ξ‖ := by
  let f := noDPFourierCutoffSchwartz h H hH
  let d := f-h
  have hmap : 𝓕 d = 𝓕 f-𝓕 h := (SchwartzMap.fourierTransformCLM ℂ).map_sub f h
  have he : 𝓕 (d:ℝ → ℂ) (-x) = 𝓕 (f:ℝ → ℂ) (-x)-𝓕 (h:ℝ → ℂ) (-x) :=
    congrArg (fun g : SchwartzMap ℝ ℂ => g (-x)) hmap
  simp only [f,noDPFourierCutoffSchwartz_coe] at he
  have hnorm : ‖𝓕 (d:ℝ → ℂ) (-x)‖ ≤ ∫ ξ : ℝ, ‖d ξ‖ := by
    rw [Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans_eq
    simp only [Circle.norm_smul]
  rw [fourierInv_eq_fourier_neg,fourierInv_eq_fourier_neg,← he]
  calc
    _ ≤ H^M*(∫ ξ : ℝ, ‖d ξ‖) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ _ := by
      simpa only [d,sub_apply,f,noDPFourierCutoffSchwartz_coe,pow_zero,one_mul,zero_add] using
        noDPFourierCutoff_weighted_tail_integral h hH 0 M

end
end Sechstmoment.Source
