import Sechstmoment.Numerator.U.MainTerm.PrincipalProfileContours


namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

def actualPrincipalProfileRescaledKernel (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (f g : ℝ → ℂ) (L c d : ℝ) (y : ℝ × ℝ) : ℂ :=
  (profileLaplaceTransform f ((c:ℂ)+(y.1:ℂ)*I)*
    profileLaplaceTransform g ((d:ℂ)+(y.2:ℂ)*I))*
    polarMellinRemovedKernel T σ m (((c:ℂ)+(y.1:ℂ)*I)/(L:ℂ))
      (((d:ℂ)+(y.2:ℂ)*I)/(L:ℂ)) 0

theorem actualPrincipalProfileLineKernel_eq_rescaled (T : ℝ) (σ : MomentShifts)
    (m : Fin 6) (f g : ℝ → ℂ) {L : ℝ} (hL : L ≠ 0) (c d : ℝ) (y : ℝ × ℝ) :
    actualPrincipalProfileLineKernel T σ m f g L (c/L) (d/L) y =
      actualPrincipalProfileRescaledKernel T σ m f g L c d (L*y.1,L*y.2) := by
  have hLc : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hu : (L:ℂ)*(((c/L:ℝ):ℂ)+(y.1:ℂ)*I) =
      (c:ℂ)+((L*y.1:ℝ):ℂ)*I := by
    push_cast
    field_simp [hLc]
  have hv : (L:ℂ)*(((d/L:ℝ):ℂ)+(y.2:ℂ)*I) =
      (d:ℂ)+((L*y.2:ℝ):ℂ)*I := by
    push_cast
    field_simp [hLc]
  have hu' : (((c/L:ℝ):ℂ)+(y.1:ℂ)*I) =
      ((c:ℂ)+((L*y.1:ℝ):ℂ)*I)/(L:ℂ) := by
    rw [← hu,mul_div_cancel_left₀ _ hLc]
  have hv' : (((d/L:ℝ):ℂ)+(y.2:ℂ)*I) =
      ((d:ℂ)+((L*y.2:ℝ):ℂ)*I)/(L:ℂ) := by
    rw [← hv,mul_div_cancel_left₀ _ hLc]
  dsimp [actualPrincipalProfileLineKernel,actualPrincipalProfileRescaledKernel,actualProfileTransformLine]
  rw [hu,hv,hu',hv']

theorem actualPrincipalProfileRescaledKernel_integrable
    (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L ε c d : ℝ} (_hL : 0 < L) (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4)
    (hc : ε ≤ c/L) (hd : ε ≤ d/L) :
    Integrable (actualPrincipalProfileRescaledKernel T σ m f g L c d)
      (volume.prod volume) := by
  have hp := (actualProfileTransformLine_integrable hf hfs (by norm_num : (0:ℝ)<1) c).mul_prod
    (actualProfileTransformLine_integrable hg hgs (by norm_num : (0:ℝ)<1) d)
  have hcont := (polarMellinRemovedKernel_principal_jointline_continuous
    T σ m hε hε1 hα hc hd).comp
    (show Continuous (fun y : ℝ × ℝ => (y.1/L,y.2/L)) by fun_prop)
  have heq (q : ℝ) (y : ℝ) : ((q/L:ℝ):ℂ)+((y/L:ℝ):ℂ)*I =
      ((q:ℂ)+(y:ℂ)*I)/(L:ℂ) := by
    push_cast
    ring
  change Continuous (fun y : ℝ × ℝ => polarMellinRemovedKernel T σ m
    (((c/L:ℝ):ℂ)+((y.1/L:ℝ):ℂ)*I) (((d/L:ℝ):ℂ)+((y.2/L:ℝ):ℂ)*I) 0) at hcont
  simp_rw [heq] at hcont
  have hi := hp.bdd_mul hcont.aestronglyMeasurable
    (c := actualPrincipalArithmeticMajorant T σ m ε)
    (Eventually.of_forall (fun y : ℝ × ℝ =>
      polarMellinRemovedKernel_principal_norm_bound T σ m hε hε1 hα
        (by simpa using hc) (by simpa using hd)))
  convert hi using 1
  funext y
  dsimp [actualPrincipalProfileRescaledKernel,actualProfileTransformLine]
  simp only [one_mul]
  ring

theorem actualPrincipalProfileIntegral_log_rescaling
    (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L ε c d : ℝ} (hL : 0 < L) (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4)
    (hc : ε ≤ c/L) (hd : ε ≤ d/L) :
    ((L:ℂ)/(2*π))^2*actualPrincipalProfileIntegral T σ m f g L (c/L) (d/L) =
      (1/(2*π):ℂ)^2*∫ y : ℝ × ℝ,
        actualPrincipalProfileRescaledKernel T σ m f g L c d y ∂(volume.prod volume) := by
  have hLc : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hi := actualPrincipalProfileLineKernel_integrable T σ m hf hfs hg hgs
    hL hε hε1 hα hc hd
  have hr := actualPrincipalProfileRescaledKernel_integrable T σ m hf hfs hg hgs
    hL hε hε1 hα hc hd
  let K := actualPrincipalProfileRescaledKernel T σ m f g L c d
  have hscale (x : ℝ) : (∫ y : ℝ, K (x,L*y)) =
      (L⁻¹:ℝ) • ∫ y : ℝ, K (x,y) := by
    simpa only [abs_of_pos (inv_pos.mpr hL)] using
      Measure.integral_comp_mul_left (fun y : ℝ => K (x,y)) L
  have hscale' : (∫ x : ℝ, ∫ y : ℝ, K (L*x,L*y)) =
      (L⁻¹:ℝ) • ((L⁻¹:ℝ) • ∫ x : ℝ, ∫ y : ℝ, K (x,y)) := by
    simp_rw [hscale]
    rw [integral_smul]
    congr 1
    simpa only [abs_of_pos (inv_pos.mpr hL)] using
      Measure.integral_comp_mul_left (fun x : ℝ => ∫ y : ℝ, K (x,y)) L
  unfold actualPrincipalProfileIntegral
  rw [integral_prod _ hi]
  simp_rw [actualPrincipalProfileLineKernel_eq_rescaled T σ m f g hL.ne' c d]
  change ((L:ℂ)/(2*π))^2*(∫ x : ℝ, ∫ y : ℝ, K (L*x,L*y)) = _
  rw [hscale',real_smul,real_smul,Complex.ofReal_inv,
    integral_prod _ hr]
  dsimp [K]
  field_simp [hLc]

end
end Sechstmoment
