import Sechstmoment.Numerator.U.Replacement.DualErrorFourier
import Sechstmoment.Numerator.U.ZeroModes.Mass.ActualSupport

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03GaussianLeadingTimeProfile (Φ : ℝ→ℂ) (T : ℝ) (σ _α : MomentShifts)
    (z : ℂ) : ℝ→ℂ :=
  a03ProfileProduct Φ (fun x => polarPoleKiller T σ z/z*(T*x/2:ℂ)^(2*z)*(Real.pi:ℂ)^(-2*z))

def a03GaussianLeadingFrequencyProfile (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (z : ℂ) (ξ : ℝ) : ℂ :=
  profileLaplaceTransform (a03GaussianLeadingTimeProfile Φ T σ α z) ((ξ:ℂ)*I)

def a03GaussianDualLeadingTimeProfile (Φ : ℝ→ℂ) (T : ℝ) (σ _α : MomentShifts)
    (z : ℂ) : ℝ→ℂ :=
  a03ProfileProduct (a03ProfileProduct Φ (bblrDualLeadingMultiplier T σ))
    (fun x => polarPoleKiller T σ z/z*(T*x/2:ℂ)^(2*z)*(Real.pi:ℂ)^(-2*z))

def a03GaussianDualLeadingFrequencyProfile (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (z : ℂ) (ξ : ℝ) : ℂ :=
  profileLaplaceTransform (a03GaussianDualLeadingTimeProfile Φ T σ α z) ((ξ:ℂ)*I)

def a03LeadingTensorRawKernel (Φ : ℝ→ℂ) (c : ℝ) (p : A03NearTensorData)
    (y : A03SixTensorSpace) : ℂ :=
  a03TensorMellinFactor p.α ((c:ℂ)+(p.v:ℂ)*I) y*
    a03GaussianLeadingFrequencyProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I)
      (-a03RealLogGapSymbol p.T p.r p.s (a03SixGapLinear y))

def a03LeadingDualTensorRawKernel (Φ : ℝ→ℂ) (c : ℝ) (p : A03NearTensorData)
    (y : A03SixTensorSpace) : ℂ :=
  a03TensorMellinFactor p.α ((c:ℂ)+(p.v:ℂ)*I) y*
    a03GaussianDualLeadingFrequencyProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I)
      (-a03RealLogGapSymbol p.T p.r p.s (a03SixGapLinear y))

def a03ReplacementTensorRawKernel (Φ : ℝ→ℂ) (c : ℝ) (p : A03NearTensorData)
    (y : A03SixTensorSpace) : ℂ :=
  a03TensorMellinFactor p.α ((c:ℂ)+(p.v:ℂ)*I) y*
    a03GaussianReplacementFrequencyProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I)
      (-a03RealLogGapSymbol p.T p.r p.s (a03SixGapLinear y))

def a03ReplacementDualTensorRawKernel (Φ : ℝ→ℂ) (c : ℝ) (p : A03NearTensorData)
    (y : A03SixTensorSpace) : ℂ :=
  a03TensorMellinFactor p.α ((c:ℂ)+(p.v:ℂ)*I) y*
    a03GaussianDualReplacementFrequencyProfile Φ p.T p.σ p.σ p.α ((c:ℂ)+(p.v:ℂ)*I)
      (-a03RealLogGapSymbol p.T p.r p.s (a03SixGapLinear y))

theorem a03GaussianLeadingTimeProfile_eq_sub (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts) (z : ℂ) :
    a03GaussianLeadingTimeProfile Φ T σ α z=
      a03GaussianTimeProfile Φ T σ α z-a03GaussianReplacementTimeProfile Φ T σ α z := by
  funext x
  unfold a03GaussianLeadingTimeProfile a03GaussianTimeProfile a03GaussianReplacementTimeProfile
    a03ProfileProduct bblrGaussianTimeAmplitude bblrGaussianTimeReplacementAmplitude
  simp only [Pi.sub_apply]
  ring

theorem a03GaussianDualLeadingTimeProfile_eq_sub (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts) (z : ℂ) :
    a03GaussianDualLeadingTimeProfile Φ T σ α z=
      a03GaussianDualTimeProfile Φ T σ α z-a03GaussianDualReplacementTimeProfile Φ T σ σ α z := by
  funext x
  unfold a03GaussianDualLeadingTimeProfile a03GaussianDualTimeProfile
    a03GaussianDualReplacementTimeProfile a03ProfileProduct bblrGaussianTimeAmplitude
    bblrGaussianDualReplacementAmplitude
  simp only [Pi.sub_apply]
  ring

private theorem laplace_sub (F G : ℝ→ℂ) (hF : Continuous F) (hG : Continuous G)
    (hsF : HasCompactSupport F) (hsG : HasCompactSupport G) (w : ℂ) :
    profileLaplaceTransform (F-G) w=profileLaplaceTransform F w-profileLaplaceTransform G w := by
  have hiF : Integrable (fun x : ℝ => Complex.exp (w*x)*F x) :=
    (by fun_prop : Continuous (fun x : ℝ => Complex.exp (w*x)*F x)).integrable_of_hasCompactSupport hsF.mul_left
  have hiG : Integrable (fun x : ℝ => Complex.exp (w*x)*G x) :=
    (by fun_prop : Continuous (fun x : ℝ => Complex.exp (w*x)*G x)).integrable_of_hasCompactSupport hsG.mul_left
  unfold profileLaplaceTransform
  simp only [Pi.sub_apply,mul_sub]
  exact integral_sub hiF hiG

theorem a03_replacement_tensor_eventually_eq_actual_sub_leading
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hθ : 0≤θ) :
    ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,(∀ j,‖α j‖≤1/4) →
      ∀ v r s : ℝ,|v|≤θ*Real.log T → ∀ y : A03SixTensorSpace,
      let p : A03NearTensorData := ⟨T,σ,α,v,r,s⟩
      a03ReplacementTensorRawKernel Φ c p y=
        a03ActualTensorRawKernel Φ c p y-a03LeadingTensorRawKernel Φ c p y := by
  filter_upwards [bblrGamma_logarithmic_strip_large hc.le hc1 hθ,eventually_ge_atTop (10:ℝ)]
    with T hlarge hT
  intro σ α hα v r s hv y
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hcA : ContDiff ℝ ∞ (a03GaussianTimeProfile Φ T σ α z) :=
    a03_gaussian_time_profile_contDiff hΦ hs (by norm_num : (0:ℝ)≤1/4)
      (by norm_num; exact hT) σ α hα (hlarge v hv)
  have hcE : ContDiff ℝ ∞ (a03GaussianReplacementTimeProfile Φ T σ α z) :=
    a03_profile_product_contDiff hΦ (fun x hx =>
      (bblrGaussianTimeReplacementAmplitude_contDiffAt hT σ α hα (hlarge v hv) (hs hx)).of_le (by simp))
  have hsA : HasCompactSupport (a03GaussianTimeProfile Φ T σ α z) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      ((a03_gaussian_time_profile_tsupport Φ T σ α z).trans hs)
  have hsE : HasCompactSupport (a03GaussianReplacementTimeProfile Φ T σ α z) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      ((a03_profile_product_tsupport _ _).trans hs)
  have he (ξ : ℝ) : a03GaussianLeadingFrequencyProfile Φ T σ α z ξ=
      a03GaussianFrequencyProfile Φ T σ α z ξ-a03GaussianReplacementFrequencyProfile Φ T σ α z ξ := by
    unfold a03GaussianLeadingFrequencyProfile a03GaussianFrequencyProfile a03GaussianReplacementFrequencyProfile
    rw [a03GaussianLeadingTimeProfile_eq_sub]
    exact laplace_sub _ _ hcA.continuous hcE.continuous hsA hsE _
  dsimp only
  unfold a03ReplacementTensorRawKernel a03ActualTensorRawKernel a03LeadingTensorRawKernel
    a03SixGaussianFrequencyKernel
  dsimp only
  rw [he]
  ring

theorem a03_dual_replacement_tensor_eventually_eq_actual_sub_leading
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j,‖α j‖≤1/4) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v r s : ℝ,|v|≤θ*Real.log T → ∀ y : A03SixTensorSpace,
      let p : A03NearTensorData := ⟨T,σ,α,v,r,s⟩
      a03ReplacementDualTensorRawKernel Φ c p y=
        a03ActualDualTensorRawKernel Φ c p y-a03LeadingDualTensorRawKernel Φ c p y := by
  obtain ⟨_C,_hC,hA⟩ := a03_gaussian_dual_frequency_logarithmic_uniform_derivative_bounds
    hΦ hs hc hc1 (by linarith : 2*c<2*c+1) hκ hθ (by norm_num : (0:ℝ)≤1/4) hR
  obtain ⟨_E,_hE,hEd⟩ := bblrGaussianDualReplacementAmplitude_logarithmic_uniform_subpower_derivatives
    hc hc1 (by linarith : 2*c<2*c+1) hκ hθ hR
  filter_upwards [hA,hEd,bblrGamma_logarithmic_strip_large hc.le hc1 hθ,
    eventually_ge_atTop (10:ℝ),eventually_ge_atTop (192*(R+R^2)+8),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hA hE hlarge hT hRT hlog
  intro σ α hσ hα hroot v r s hv y
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hcD : ContDiff ℝ ∞ (a03ProfileProduct Φ (fun x => bblrDualMultiplier (T*x) (rawMomentShifts T σ))) :=
    a03_profile_product_contDiff hΦ (fun x hx =>
      (bblrDualMultiplier_normalizedTime_contDiffAt hR hlog hRT σ hσ (hs hx)).of_le (by simp))
  have hsD : tsupport (a03ProfileProduct Φ (fun x => bblrDualMultiplier (T*x) (rawMomentShifts T σ)))⊆Icc 1 2 :=
    (a03_profile_product_tsupport _ _).trans hs
  have hcA : ContDiff ℝ ∞ (a03GaussianDualTimeProfile Φ T σ α z) :=
    a03_profile_product_contDiff hcD (fun x hx =>
      (bblrGaussianTimeAmplitude_contDiffAt (by norm_num : (0:ℝ)≤1/4) (by norm_num; exact hT)
        σ α hα (hlarge v hv) (hsD hx)).of_le (by simp))
  have hcE : ContDiff ℝ ∞ (a03GaussianDualReplacementTimeProfile Φ T σ σ α z) :=
    a03_profile_product_contDiff hΦ (fun x hx => (hE σ σ α hσ hα hroot v hv x (hs hx)).1)
  have hsA : HasCompactSupport (a03GaussianDualTimeProfile Φ T σ α z) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      ((a03_gaussian_dual_time_profile_tsupport Φ T σ α z).trans hs)
  have hsE : HasCompactSupport (a03GaussianDualReplacementTimeProfile Φ T σ σ α z) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      ((a03_profile_product_tsupport _ _).trans hs)
  have he (ξ : ℝ) : a03GaussianDualLeadingFrequencyProfile Φ T σ α z ξ=
      a03GaussianDualFrequencyProfile Φ T σ α z ξ-a03GaussianDualReplacementFrequencyProfile Φ T σ σ α z ξ := by
    unfold a03GaussianDualLeadingFrequencyProfile a03GaussianDualFrequencyProfile a03GaussianDualReplacementFrequencyProfile
    rw [a03GaussianDualLeadingTimeProfile_eq_sub]
    exact laplace_sub _ _ hcA.continuous hcE.continuous hsA hsE _
  dsimp only
  unfold a03ReplacementDualTensorRawKernel a03ActualDualTensorRawKernel a03LeadingDualTensorRawKernel
    a03SixGaussianDualFrequencyKernel
  dsimp only
  rw [he]
  ring

end
end Sechstmoment
