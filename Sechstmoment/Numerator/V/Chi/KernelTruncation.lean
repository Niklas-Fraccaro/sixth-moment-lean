import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Sechstmoment.Numerator.V.Chi.IntegralTranslation
import Sechstmoment.Numerator.V.Chi.LogBandCosine
import Sechstmoment.Numerator.V.Chi.TimeTruncation


namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped FourierTransform
noncomputable section

theorem schwartz_scaled_square_norm_integrable (ψ : SchwartzMap ℝ ℂ)
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun t : ℝ => t^2*‖ψ (t/T)‖) := by
  have H := ((ψ.integrable_pow_mul volume 2).comp_div hT.ne').const_mul (T^2)
  convert H using 1
  funext t
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hT,div_pow,sq_abs]
  field_simp [hT.ne']

theorem noDPChiBaseIntegrand_mul_schwartz_integrable (ψ : SchwartzMap ℝ ℂ)
    {T c r : ℝ} (hT : 0 < T) (hc : c ∈ Icc (1/8:ℝ) (15/8)) (hr : 0 < r) :
    Integrable (fun t : ℝ => noDPChiBaseIntegrand r c t*ψ (t/T)) := by
  obtain ⟨D,hD,hchi⟩ := chi_positive_strip_global_polynomial_bound
  have hi0 := (ψ.integrable.norm.comp_div hT.ne')
  have hi2 := schwartz_scaled_square_norm_integrable ψ hT
  have hscaled : Continuous (fun t : ℝ => ψ (t/T)) := ψ.continuous.comp (by fun_prop)
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => noDPChiBaseIntegrand r c t*ψ (t/T)) volume :=
    (noDPChiBaseIntegrand_aestronglyMeasurable hr (by linarith [hc.1])).mul
      hscaled.aestronglyMeasurable
  apply ((hi0.add hi2).const_mul (r^(-c)*(2*D))).mono' hmeas
  filter_upwards [volume.ae_ne (0:ℝ)] with t ht
  rw [norm_mul,noDPChiBaseIntegrand_norm hr]
  calc
    _ ≤ (r^(-c)*(D*(1+|t|)^2))*‖ψ (t/T)‖ := by
      gcongr
      exact hchi c hc t ht
    _ ≤ (r^(-c)*(2*D))*(‖ψ (t/T)‖+t^2*‖ψ (t/T)‖) := by
      have H : (1+|t|)^2 ≤ 2*(1+t^2) := by nlinarith [sq_abs t,sq_nonneg (|t|-1)]
      have Hmul := mul_le_mul_of_nonneg_left H
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hr.le (-c)) hD.le) (norm_nonneg (ψ (t/T))))
      nlinarith

theorem noDPChiTimeTransform_cutoff_error (h : SchwartzMap ℝ ℂ)
    (hs : tsupport (𝓕⁻ (h:ℝ → ℂ)) ⊆ Icc (1:ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 3 (100*Real.pi) ≤ T →
      ∀ c ∈ Icc (1/8:ℝ) (15/8), ∀ r : ℝ, 0 < r →
      ‖noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T c 0 r-
        noDPChiBandTransform h T c r‖ ≤ C*r^(-c)/T^2 := by
  obtain ⟨D,hD,hchi⟩ := chi_positive_strip_global_polynomial_bound
  obtain ⟨E,hE,herror⟩ := noDPTimeTruncation_pointwise h hs 2
  refine ⟨D*E,by positivity,?_⟩
  intro T hT c hc r hr
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ) < 3) ((le_max_left _ _).trans hT)
  have hH : 0 < T/(100*Real.pi) := by positivity
  let ψ : SchwartzMap ℝ ℂ := 𝓕⁻ h
  let ψH : SchwartzMap ℝ ℂ := 𝓕⁻ (noDPFourierCutoffSchwartz h (T/(100*Real.pi)) hH)
  have hψ (t : ℝ) : ψ t = 𝓕⁻ (h:ℝ → ℂ) t := congrFun (SchwartzMap.fourierInv_coe h) t
  have hψH (t : ℝ) : ψH t = 𝓕⁻ (noDPFourierCutoff h (T/(100*Real.pi))) t :=
    congrFun (SchwartzMap.fourierInv_coe (noDPFourierCutoffSchwartz h (T/(100*Real.pi)) hH)) t
  have hi := noDPChiBaseIntegrand_mul_schwartz_integrable ψ hT0 hc hr
  have hiH := noDPChiBaseIntegrand_mul_schwartz_integrable ψH hT0 hc hr
  let F : ℝ → ℂ := fun t => noDPChiBaseIntegrand r c t*(ψ (t/T)-ψH (t/T))
  have he : noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T c 0 r-
      noDPChiBandTransform h T c r = (1/(2*Real.pi):ℂ)*(∫ t : ℝ, F t) := by
    unfold noDPChiTimeTransform noDPChiBandTransform
    simp only [add_zero]
    simp_rw [← hψ,← hψH]
    change (1/(2*Real.pi):ℂ)*(∫ t : ℝ, noDPChiBaseIntegrand r c t*ψ (t/T))-
      (1/(2*Real.pi):ℂ)*(∫ t : ℝ, noDPChiBaseIntegrand r c t*ψH (t/T)) = _
    rw [← mul_sub,← integral_sub hi hiH]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [F,noDPChiBaseIntegrand]
    ring
  have hpoint : ∀ᵐ t : ℝ, ‖F t‖ ≤ (r^(-c)*(D*E)/T^2)*(1+t^2)⁻¹ := by
    filter_upwards [volume.ae_ne (0:ℝ)] with t ht
    have hdelta := herror T hT t
    rw [← hψH,← hψ,norm_sub_rev] at hdelta
    dsimp only [F]
    rw [norm_mul,noDPChiBaseIntegrand_norm hr]
    calc
      _ ≤ r^(-c)*(D*(1+|t|)^2)*‖ψ (t/T)-ψH (t/T)‖ := by
        gcongr
        exact hchi c hc t ht
      _ = (r^(-c)*D)*((1+|t|)^2*‖ψ (t/T)-ψH (t/T)‖) := by ring
      _ ≤ (r^(-c)*D)*(E/(T^2*(1+t^2))) :=
        mul_le_mul_of_nonneg_left hdelta (by positivity)
      _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  have H := norm_integral_le_of_norm_le
    (f := F) (integrable_inv_one_add_sq.const_mul (r^(-c)*(D*E)/T^2)) hpoint
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at H
  rw [he,norm_mul]
  have hscale : ‖(1/(2*Real.pi):ℂ)‖ = 1/(2*Real.pi) := by simp
  rw [hscale]
  calc
    _ ≤ (1/(2*Real.pi))*((r^(-c)*(D*E)/T^2)*Real.pi) :=
      mul_le_mul_of_nonneg_left H (by positivity)
    _ ≤ D*E*r^(-c)/T^2 := by
      have heq : (1/(2*Real.pi))*((r^(-c)*(D*E)/T^2)*Real.pi) =
          (D*E*r^(-c)/T^2)/2 := by field_simp
      rw [heq]
      have hp : 0 ≤ D*E*r^(-c)/T^2 := by positivity
      linarith

end
end Sechstmoment.Source
