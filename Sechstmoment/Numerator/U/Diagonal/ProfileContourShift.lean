import Sechstmoment.Analysis.Complex.ContourShift
import Sechstmoment.Numerator.U.Diagonal.ActualProfileMellin
import Sechstmoment.Numerator.U.Diagonal.ProfileStripDecay

/-! Actual contour movement for a profile multiplied by a bounded holomorphic
factor. Vertical integrability and horizontal decay are consequences, not inputs. -/

namespace Sechstmoment
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

private theorem actualProfileMultiplier_line_integrable {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) {L : ℝ} (hL : 0 < L)
    (H : ℂ → ℂ) {U : Set ℂ} (hH : DifferentiableOn ℂ H U) {a b c C : ℝ}
    (hc : c ∈ Icc a b) (hstrip : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ∈ U)
    (hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖H z‖ ≤ C) :
    Integrable (fun y : ℝ => profileLaplaceTransform f ((L:ℂ)*((c:ℂ)+(y:ℂ)*I))*
      H ((c:ℂ)+(y:ℂ)*I)) := by
  have hcont : Continuous (fun y : ℝ => H ((c:ℂ)+(y:ℂ)*I)) := by
    apply continuousOn_univ.mp
    apply hH.continuousOn.comp (by fun_prop : ContinuousOn (fun y : ℝ => (c:ℂ)+(y:ℂ)*I) univ)
    intro y hy
    exact hstrip _ (by simpa using hc.1) (by simpa using hc.2)
  have hi := (actualProfileTransformLine_integrable hf hfs hL c).bdd_mul hcont.aestronglyMeasurable
    (Eventually.of_forall (fun y => hbound ((c:ℂ)+(y:ℂ)*I) (by simpa using hc.1) (by simpa using hc.2)))
  simpa only [actualProfileTransformLine,mul_comm] using hi

theorem profileMultiplier_horizontal_integral_tendsto_zero {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) {L : ℝ} (hL : 0 < L)
    (H : ℂ → ℂ) {a b C : ℝ} (hab : a ≤ b) (_hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖H z‖ ≤ C) :
    Tendsto (fun y : ℝ => ∫ c in a..b,
      profileLaplaceTransform f ((L:ℂ)*((c:ℂ)+(y:ℂ)*I))*H ((c:ℂ)+(y:ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨K,hK,hfreq⟩ := profileLaplaceTransform_strip_frequency_bound hf hfs (L*a) (L*b)
  have hv : Tendsto (fun y : ℝ => |y|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hlim : Tendsto (fun y : ℝ => (K*C*|b-a|/L)*|y|⁻¹) (cocompact ℝ) (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using
      (tendsto_inv_atTop_zero.comp hv).const_mul (K*C*|b-a|/L)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hv.eventually (eventually_ge_atTop (1:ℝ))] with y hy
  have hyp : 0 < |y| := (by norm_num : (0:ℝ)<1).trans_le hy
  have hbnd (c : ℝ) (hc : c ∈ uIoc a b) :
      ‖profileLaplaceTransform f ((L:ℂ)*((c:ℂ)+(y:ℂ)*I))*H ((c:ℂ)+(y:ℂ)*I)‖ ≤
        K/(L*|y|)*C := by
    rw [uIoc_of_le hab] at hc
    have hLc : L*c ∈ Icc (L*a) (L*b) :=
      ⟨mul_le_mul_of_nonneg_left hc.1.le hL.le,mul_le_mul_of_nonneg_left hc.2 hL.le⟩
    have hs := hfreq (L*c) hLc (L*y)
    have he : ((L*c:ℝ):ℂ)+(L*y:ℝ)*I=(L:ℂ)*((c:ℂ)+(y:ℂ)*I) := by push_cast; ring
    rw [he,abs_mul,abs_of_pos hL] at hs
    have hp : ‖profileLaplaceTransform f ((L:ℂ)*((c:ℂ)+(y:ℂ)*I))‖ ≤ K/(L*|y|) :=
      (le_div_iff₀ (mul_pos hL hyp)).mpr (by simpa only [mul_comm] using hs)
    rw [norm_mul]
    exact mul_le_mul hp (hbound _ (by simpa using hc.1.le) (by simpa using hc.2))
      (norm_nonneg _) (div_nonneg hK (mul_nonneg hL.le (abs_nonneg _)))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun c : ℝ => profileLaplaceTransform f ((L:ℂ)*((c:ℂ)+(y:ℂ)*I))*
      H ((c:ℂ)+(y:ℂ)*I)) (a := a) (b := b) (C := K/(L*|y|)*C) hbnd
  exact h.trans_eq (by field_simp)

theorem profileMultiplier_verticalIntegral_shift {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) {L : ℝ} (hL : 0 < L)
    (H : ℂ → ℂ) {U : Set ℂ} (hH : DifferentiableOn ℂ H U) {a b C : ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C)
    (hstrip : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ∈ U)
    (hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖H z‖ ≤ C) :
    Source.verticalIntegral b (fun z => profileLaplaceTransform f ((L:ℂ)*z)*H z) =
      Source.verticalIntegral a (fun z => profileLaplaceTransform f ((L:ℂ)*z)*H z) := by
  have hF : DifferentiableOn ℂ (fun z => profileLaplaceTransform f ((L:ℂ)*z)*H z) U := by
    simpa only [Function.comp_apply,id_eq,Pi.mul_apply] using!
      ((profileLaplaceTransform_differentiable hf hfs.continuous).comp
        (differentiable_id.const_mul (L:ℂ))).differentiableOn.mul hH
  apply bblrRectangle_verticalIntegral_shift _ hF hab hstrip
  · exact actualProfileMultiplier_line_integrable (a := a) (b := b) hf hfs hL H hH ⟨le_rfl,hab⟩ hstrip hbound
  · exact actualProfileMultiplier_line_integrable (a := a) (b := b) hf hfs hL H hH ⟨hab,le_rfl⟩ hstrip hbound
  · exact profileMultiplier_horizontal_integral_tendsto_zero hf hfs hL H hab hC hbound

end
end Sechstmoment
