import Sechstmoment.Numerator.U.Diagonal.PrincipalArithmeticLines
import Sechstmoment.Numerator.U.Diagonal.ProfileContourShift

/-!
# A04: the actual two principal profile contours

Both amplifier contours of the genuine principal Mellin kernel can move
from a fixed positive line to any smaller positive line on which the raw
shifts satisfy the explicit bound. All joint integrability and horizontal
boundary decay follow from the actual profiles and arithmetic kernel.
This module does not assert the subsequent polar limit or A04 completion.
-/

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

def actualPrincipalProfileLineKernel (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (f g : ℝ → ℂ) (L c d : ℝ) (y : ℝ × ℝ) : ℂ :=
  (actualProfileTransformLine f L c y.1*actualProfileTransformLine g L d y.2)*
    polarMellinRemovedKernel T σ m ((c:ℂ)+(y.1:ℂ)*I) ((d:ℂ)+(y.2:ℂ)*I) 0

def actualPrincipalProfileIntegral (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (f g : ℝ → ℂ) (L c d : ℝ) : ℂ :=
  ∫ y : ℝ × ℝ, actualPrincipalProfileLineKernel T σ m f g L c d y
    ∂(volume.prod volume)

theorem actualPrincipalProfileLineKernel_integrable
    (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L ε c d : ℝ} (hL : 0 < L) (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4)
    (hc : ε ≤ c) (hd : ε ≤ d) :
    Integrable (actualPrincipalProfileLineKernel T σ m f g L c d)
      (volume.prod volume) := by
  have hp := (actualProfileTransformLine_integrable hf hfs hL c).mul_prod
    (actualProfileTransformLine_integrable hg hgs hL d)
  have hcont := polarMellinRemovedKernel_principal_jointline_continuous T σ m hε hε1 hα hc hd
  have hi := hp.bdd_mul hcont.aestronglyMeasurable
    (c := actualPrincipalArithmeticMajorant T σ m ε)
    (Eventually.of_forall (fun y : ℝ × ℝ =>
      polarMellinRemovedKernel_principal_norm_bound T σ m hε hε1 hα
        (by simpa using hc) (by simpa using hd)))
  convert hi using 1
  funext y
  dsimp [actualPrincipalProfileLineKernel]
  ring

private theorem actualPrincipalProfile_single_line_shift
    (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {f : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    {L ε c d : ℝ} {v : ℂ} (hL : 0 < L) (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4)
    (hc : ε ≤ c) (hcd : c ≤ d) (hv : ε ≤ v.re) :
    (∫ y : ℝ, actualProfileTransformLine f L d y*
      polarMellinRemovedKernel T σ m ((d:ℂ)+(y:ℂ)*I) v 0) =
    (∫ y : ℝ, actualProfileTransformLine f L c y*
      polarMellinRemovedKernel T σ m ((c:ℂ)+(y:ℂ)*I) v 0) := by
  have hs := profileMultiplier_verticalIntegral_shift hf hfs hL
    (fun u => polarMellinRemovedKernel T σ m u v 0)
    (polarMellinRemovedKernel_principal_differentiableOn_left T σ m hε hε1 hα hv)
    hcd (actualPrincipalArithmeticMajorant_nonneg T σ m ε)
    (fun z hzc _ => by
      change ε/2 < z.re
      linarith)
    (fun z hzc _ => polarMellinRemovedKernel_principal_norm_bound T σ m
      hε hε1 hα (hc.trans hzc) hv)
  unfold Source.verticalIntegral at hs
  apply mul_left_cancel₀ (show (1/(2*π):ℂ) ≠ 0 by simp [Real.pi_ne_zero])
  simpa only [actualProfileTransformLine] using hs

private theorem actualPrincipalProfile_single_right_line_shift
    (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L ε c d : ℝ} {u : ℂ} (hL : 0 < L) (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4)
    (hc : ε ≤ c) (hcd : c ≤ d) (hu : ε ≤ u.re) :
    (∫ y : ℝ, actualProfileTransformLine g L d y*
      polarMellinRemovedKernel T σ m u ((d:ℂ)+(y:ℂ)*I) 0) =
    (∫ y : ℝ, actualProfileTransformLine g L c y*
      polarMellinRemovedKernel T σ m u ((c:ℂ)+(y:ℂ)*I) 0) := by
  have hs := profileMultiplier_verticalIntegral_shift hg hgs hL
    (fun v => polarMellinRemovedKernel T σ m u v 0)
    (polarMellinRemovedKernel_principal_differentiableOn_right T σ m hε hε1 hα hu)
    hcd (actualPrincipalArithmeticMajorant_nonneg T σ m ε)
    (fun z hzc _ => by
      change ε/2 < z.re
      linarith)
    (fun z hzc _ => polarMellinRemovedKernel_principal_norm_bound T σ m
      hε hε1 hα hu (hc.trans hzc))
  unfold Source.verticalIntegral at hs
  apply mul_left_cancel₀ (show (1/(2*π):ℂ) ≠ 0 by simp [Real.pi_ne_zero])
  simpa only [actualProfileTransformLine] using hs

theorem actualPrincipalProfileIntegral_left_shift
    (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L ε c d e : ℝ} (hL : 0 < L) (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4)
    (hc : ε ≤ c) (hcd : c ≤ d) (he : ε ≤ e) :
    actualPrincipalProfileIntegral T σ m f g L d e =
      actualPrincipalProfileIntegral T σ m f g L c e := by
  unfold actualPrincipalProfileIntegral
  rw [integral_prod_symm _ (actualPrincipalProfileLineKernel_integrable
    T σ m hf hfs hg hgs hL hε hε1 hα (hc.trans hcd) he),
    integral_prod_symm _ (actualPrincipalProfileLineKernel_integrable
      T σ m hf hfs hg hgs hL hε hε1 hα hc he)]
  apply integral_congr_ae
  filter_upwards [] with y
  have hinner (q : ℝ) : (∫ x : ℝ,
      actualPrincipalProfileLineKernel T σ m f g L q e (x,y)) =
      actualProfileTransformLine g L e y * ∫ x : ℝ,
        actualProfileTransformLine f L q x *
          polarMellinRemovedKernel T σ m ((q:ℂ)+(x:ℂ)*I) ((e:ℂ)+(y:ℂ)*I) 0 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [actualPrincipalProfileLineKernel]
    ring
  rw [hinner d,hinner c,actualPrincipalProfile_single_line_shift T σ m hf hfs
    hL hε hε1 hα hc hcd (by simpa using he)]

theorem actualPrincipalProfileIntegral_right_shift
    (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L ε c d e : ℝ} (hL : 0 < L) (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4)
    (hc : ε ≤ c) (hcd : c ≤ d) (he : ε ≤ e) :
    actualPrincipalProfileIntegral T σ m f g L e d =
      actualPrincipalProfileIntegral T σ m f g L e c := by
  unfold actualPrincipalProfileIntegral
  rw [integral_prod _ (actualPrincipalProfileLineKernel_integrable
    T σ m hf hfs hg hgs hL hε hε1 hα he (hc.trans hcd)),
    integral_prod _ (actualPrincipalProfileLineKernel_integrable
      T σ m hf hfs hg hgs hL hε hε1 hα he hc)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hinner (q : ℝ) : (∫ y : ℝ,
      actualPrincipalProfileLineKernel T σ m f g L e q (x,y)) =
      actualProfileTransformLine f L e x * ∫ y : ℝ,
        actualProfileTransformLine g L q y *
          polarMellinRemovedKernel T σ m ((e:ℂ)+(x:ℂ)*I) ((q:ℂ)+(y:ℂ)*I) 0 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [actualPrincipalProfileLineKernel]
    ring
  rw [hinner d,hinner c,actualPrincipalProfile_single_right_line_shift T σ m hg hgs
    hL hε hε1 hα hc hcd (by simpa using he)]

/-- The two actual principal contours move together, with no poles crossed
and no additional integrability or horizontal-boundary assumptions. -/
theorem actualPrincipalProfileIntegral_double_shift
    (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L ε δ : ℝ} (hL : 0 < L) (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4)
    (hεδ : ε ≤ δ) :
    actualPrincipalProfileIntegral T σ m f g L δ δ =
      actualPrincipalProfileIntegral T σ m f g L ε ε := by
  rw [actualPrincipalProfileIntegral_left_shift T σ m hf hfs hg hgs hL hε hε1
    hα le_rfl hεδ hεδ,
    actualPrincipalProfileIntegral_right_shift T σ m hf hfs hg hgs hL hε hε1
      hα le_rfl hεδ le_rfl]

end
end Sechstmoment
