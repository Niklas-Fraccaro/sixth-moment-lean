import Sechstmoment.Analysis.Mellin.FourierCutoffDecay
import Sechstmoment.Numerator.V.Chi.LogBandCosine
import Sechstmoment.Numerator.V.Chi.LogBandFullDerivatives

/-! Arbitrary-order far-frequency decay for the actual chi-band transform.
The constants are obtained from the concrete profile derivative masses. -/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped ContDiff FourierTransform
noncomputable section

theorem smoothed_cosine_twice_fourier (g : ℝ → ℂ) (r : ℝ) :
    2*a03SmoothedCosine g (2*Real.pi*r) = 𝓕 g (-r)+𝓕 g r := by
  have hzero : profileExponentialWeight g 0 = g := by
    funext x
    simp [profileExponentialWeight]
  have h (v : ℝ) : profileLaplaceTransform g ((v:ℂ)*I) = 𝓕 g (-v/(2*Real.pi)) := by
    simpa only [hzero,Complex.ofReal_zero,zero_add] using profileLaplaceTransform_eq_fourier g 0 v
  have hp := h (2*Real.pi*r)
  have hn := h (-(2*Real.pi*r))
  simp only [Complex.ofReal_neg] at hn
  have hep : -(2*Real.pi*r)/(2*Real.pi) = -r := by
    rw [neg_div,mul_div_cancel_left₀ r (by positivity : 2*Real.pi ≠ 0)]
  have hen : -(-(2*Real.pi*r))/(2*Real.pi) = r := by
    rw [neg_neg,mul_div_cancel_left₀ r (by positivity : 2*Real.pi ≠ 0)]
  unfold a03SmoothedCosine
  rw [hp,hn,hep,hen]
  ring

theorem noDPChiBandTransform_power_decay (h : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ c ∈ Icc (1:ℝ) 2, ∀ r : ℝ, 0 < r →
      r^n*‖noDPChiBandTransform h T c r‖ ≤ C*T^(n+1) := by
  obtain ⟨D,hD,hmass⟩ := noDPLogBandProfile_uniform_derivative_mass h n
  refine ⟨2*D,by positivity,?_⟩
  intro T hT c hc r hr
  have hT0 : 0 < T := by linarith
  have hc0 : 0 < c := by linarith [hc.1]
  let g := noDPLogBandProfile h T c
  have hK : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (noDPLogBandProfile_tsupport h T c)
  let gS := hK.toSchwartzMap (noDPLogBandProfile_contDiff h T c)
  have hF (a : ℝ) : |a|^n*‖𝓕 g a‖ ≤ D*T^(n+1) := by
    calc
      _ ≤ (2*Real.pi* |a|)^n*‖𝓕 g a‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply pow_le_pow_left₀ (abs_nonneg _)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (show (1:ℝ) ≤ 2*Real.pi by linarith [Real.two_le_pi]) (abs_nonneg a)
      _ ≤ ∫ u : ℝ, ‖iteratedDeriv n g u‖ := schwartz_fourier_power_norm_bound gS n a
      _ ≤ _ := hmass T hT c hc
  have he : noDPChiBandTransform h T c r = 2*a03SmoothedCosine g (2*Real.pi*r) :=
    noDPLogBandProfile_chi_inverse h hT0 hc0 hr
  rw [he,smoothed_cosine_twice_fourier]
  calc
    _ ≤ r^n*(‖𝓕 g (-r)‖+‖𝓕 g r‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hr.le _)
    _ = r^n*‖𝓕 g (-r)‖+r^n*‖𝓕 g r‖ := by ring
    _ ≤ D*T^(n+1)+D*T^(n+1) := add_le_add
      (by simpa only [abs_neg,abs_of_pos hr] using hF (-r))
      (by simpa only [abs_of_pos hr] using hF r)
    _ = _ := by ring

theorem noDPChiBandTransform_eighth_decay (h : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ c ∈ Icc (1:ℝ) 2, ∀ r : ℝ, 0 < r →
      ‖noDPChiBandTransform h T c r‖ ≤ C*T^9/r^8 := by
  obtain ⟨C,hC,hbound⟩ := noDPChiBandTransform_power_decay h 8
  refine ⟨C,hC,?_⟩
  intro T hT c hc r hr
  have H := hbound T hT c hc r hr
  apply (le_div_iff₀ (pow_pos hr 8)).mpr
  norm_num at H
  nlinarith

end
end Sechstmoment.Source
