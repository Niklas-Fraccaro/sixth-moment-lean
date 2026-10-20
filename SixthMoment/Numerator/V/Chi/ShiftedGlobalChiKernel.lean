import SixthMoment.Numerator.V.Chi.GlobalChiKernel


namespace SixthMoment.Source
open Complex Real Set MeasureTheory
open scoped ContDiff FourierTransform
noncomputable section

theorem noDPChiTimeTransform_shifted_global_error (h : SchwartzMap ℝ ℂ)
    (hs : tsupport (𝓕⁻ (h:ℝ → ℂ)) ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 64 (100*Real.pi) ≤ T →
      4*(2*R+2) ≤ Real.log T → ∀ u : ℂ, ‖u‖ ≤ R/Real.log T →
      ∀ r : ℝ, 0 < r →
      ‖noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T (noDPRightLine T R) u r-
        Complex.exp (I*((-2*Real.pi*r:ℝ):ℂ))*
          noDPTimeWeight (𝓕⁻ (h:ℝ → ℂ)) T u (2*Real.pi*r/T)‖ ≤
        C*r^(-noDPRightLine T R)*T^(1/2:ℝ) := by
  have hw : ContDiff ℝ ∞ (𝓕⁻ (h:ℝ → ℂ)) := by
    rw [← SchwartzMap.fourierInv_coe]
    exact (𝓕⁻ h : SchwartzMap ℝ ℂ).smooth'
  obtain ⟨D,hD,htranslate⟩ := noDPChiTimeTransform_translation_error hw hs (2*R+2)
  obtain ⟨E,hE,hbase⟩ := noDPChiTimeTransform_global_weighted_error h hs (2*R+2)
  let C := D*R+E
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro T hT hL u hu r hr
  have hT64 : 64 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hTbase : max 3 (100*Real.pi) ≤ T :=
    max_le (by linarith) ((le_max_right _ _).trans hT)
  have hL1 : 1 ≤ Real.log T := by linarith
  obtain ⟨hc,hsmall,hcline⟩ := noDPRightLine_chi_shift_geometry hR hL hu
  have himR : |u.im| ≤ R := (Complex.abs_im_le_norm u).trans
    (hu.trans (div_le_self hR hL1))
  have himT : |u.im| ≤ T/2 := (Complex.abs_im_le_norm u).trans
    (hsmall.trans (by linarith))
  have Htranslate := htranslate T hT64 (noDPRightLine T R) u
    ⟨by linarith [hc.1],by linarith [hc.2]⟩ hcline himT r hr
  have Hbase := hbase T hTbase (noDPRightLine T R-u.re)
    ⟨hc.1,by linarith [hc.2]⟩ hcline r hr
  have hprefix : ‖(r:ℂ)^(-u)‖ = r^(-u.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr,neg_re]
  have hpower : r^(-u.re)*r^(-(noDPRightLine T R-u.re)) = r^(-noDPRightLine T R) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hdecompose :
      noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T (noDPRightLine T R) u r-
        Complex.exp (I*((-2*Real.pi*r:ℝ):ℂ))*
          noDPTimeWeight (𝓕⁻ (h:ℝ → ℂ)) T u (2*Real.pi*r/T) =
      (noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T (noDPRightLine T R) u r-
        (r:ℂ)^(-u)*noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T
          (noDPRightLine T R-u.re) 0 r)+
      (r:ℂ)^(-u)*(noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T
        (noDPRightLine T R-u.re) 0 r-
        Complex.exp (I*((-2*Real.pi*r:ℝ):ℂ))*𝓕⁻ (h:ℝ → ℂ) (2*Real.pi*r/T)) := by
    rw [noDPTimeWeight_frequency_value _ hT0 hr]
    ring
  rw [hdecompose]
  calc
    _ ≤ ‖noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T (noDPRightLine T R) u r-
        (r:ℂ)^(-u)*noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T
          (noDPRightLine T R-u.re) 0 r‖+
        ‖(r:ℂ)^(-u)*(noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T
          (noDPRightLine T R-u.re) 0 r-
          Complex.exp (I*((-2*Real.pi*r:ℝ):ℂ))*𝓕⁻ (h:ℝ → ℂ) (2*Real.pi*r/T))‖ :=
      norm_add_le _ _
    _ ≤ D*r^(-noDPRightLine T R)*T^(1/2:ℝ)*R+
        r^(-u.re)*(E*r^(-(noDPRightLine T R-u.re))*T^(1/2:ℝ)) := by
      rw [norm_mul,hprefix]
      exact add_le_add (Htranslate.trans
        (mul_le_mul_of_nonneg_left himR (by positivity)))
        (mul_le_mul_of_nonneg_left Hbase (Real.rpow_nonneg hr.le _))
    _ = C*r^(-noDPRightLine T R)*T^(1/2:ℝ) := by
      dsimp only [C]
      linear_combination E*T^(1/2:ℝ)*hpower

theorem smooth_dyadic_shifted_chi_global_error {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 64 (100*Real.pi) ≤ T →
      4*(2*R+2) ≤ Real.log T → ∀ u : ℂ, ‖u‖ ≤ R/Real.log T →
      ∀ r : ℝ, 0 < r →
      ‖noDPChiTimeTransform w T (noDPRightLine T R) u r-
        Complex.exp (I*((-2*Real.pi*r:ℝ):ℂ))*noDPTimeWeight w T u (2*Real.pi*r/T)‖ ≤
        C*r^(-noDPRightLine T R)*T^(1/2:ℝ) := by
  have hK : HasCompactSupport w :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hws
  let wS : SchwartzMap ℝ ℂ := hK.toSchwartzMap hw
  have hcoe : (wS:ℝ → ℂ) = w := rfl
  have hinv : 𝓕⁻ ((𝓕 wS : SchwartzMap ℝ ℂ):ℝ → ℂ) = w := by
    rw [← SchwartzMap.fourierInv_coe,FourierTransform.fourierInv_fourier_eq,hcoe]
  simpa only [hinv] using
    noDPChiTimeTransform_shifted_global_error (𝓕 wS) (by rw [hinv]; exact hws) hR

end
end SixthMoment.Source
