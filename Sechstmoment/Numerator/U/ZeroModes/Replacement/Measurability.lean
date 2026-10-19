import Sechstmoment.Numerator.U.Separation.ActualTensorMellinIntegrability
import Sechstmoment.Numerator.U.Separation.DualLeadingRegularity
import Sechstmoment.Numerator.U.ZeroModes.PhysicalReplacement

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 300000

theorem a03FrequencyProfile_joint_stronglyMeasurable (F : ℝ→ℝ→ℂ)
    (hF : StronglyMeasurable (fun p : ℝ×ℝ => F p.1 p.2)) :
    StronglyMeasurable (fun p : ℝ×ℝ => profileLaplaceTransform (F p.1) ((p.2:ℂ)*I)) := by
  have hf : StronglyMeasurable (fun p : (ℝ×ℝ)×ℝ => F p.1.1 p.2) := hF.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have he : StronglyMeasurable (fun p : (ℝ×ℝ)×ℝ => Complex.exp (((p.1.2:ℂ)*I)*(p.2:ℂ))) :=
    (by fun_prop : Continuous (fun p : (ℝ×ℝ)×ℝ => Complex.exp (((p.1.2:ℂ)*I)*(p.2:ℂ)))).stronglyMeasurable
  exact (he.mul hf).integral_prod_right'

theorem a03GaussianLeadingTimeProfile_mellin_joint_measurable
    (Φ : ℝ→ℂ) (hΦ : Measurable Φ) (T c : ℝ) (σ α : MomentShifts) :
    Measurable (fun p : ℝ×ℝ => a03GaussianLeadingTimeProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) := by
  unfold a03GaussianLeadingTimeProfile a03ProfileProduct
  have hG : Measurable (fun p : ℝ×ℝ => polarPoleKiller T σ ((c:ℂ)+(p.1:ℂ)*I)) :=
    (polarPoleKiller_differentiable T σ).continuous.measurable.comp (by fun_prop)
  have hz : Measurable (fun p : ℝ×ℝ => (c:ℂ)+(p.1:ℂ)*I) := by fun_prop
  have hp : Measurable (fun p : ℝ×ℝ => (T*p.2/2:ℂ)^(2*((c:ℂ)+(p.1:ℂ)*I))) :=
    (by fun_prop : Measurable (fun p : ℝ×ℝ => (T*p.2/2:ℂ))).pow (hz.const_mul 2)
  have hπ : Measurable (fun p : ℝ×ℝ => (Real.pi:ℂ)^(-2*((c:ℂ)+(p.1:ℂ)*I))) :=
    measurable_const.pow (hz.const_mul (-2))
  exact (hΦ.comp measurable_snd).mul (((hG.div hz).mul hp).mul hπ)

theorem a03GaussianDualLeadingTimeProfile_mellin_joint_measurable
    (Φ : ℝ→ℂ) (hΦ : Measurable Φ) (T c : ℝ) (σ α : MomentShifts) :
    Measurable (fun p : ℝ×ℝ => a03GaussianDualLeadingTimeProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) := by
  have hL := a03GaussianLeadingTimeProfile_mellin_joint_measurable Φ hΦ T c σ α
  have hD : Measurable (fun p : ℝ×ℝ => bblrDualLeadingMultiplier T σ p.2) :=
    (bblrDualLeadingMultiplier_measurable T σ).comp measurable_snd
  convert hD.mul hL using 1
  funext p
  simp only [Pi.mul_apply]
  unfold a03GaussianDualLeadingTimeProfile a03GaussianLeadingTimeProfile a03ProfileProduct
  ring

theorem a03_zero_leading_kernel_joint_stronglyMeasurable (dual : Bool)
    (Φ : ℝ→ℂ) (hΦ : Measurable Φ) (T c r s : ℝ) (σ α : MomentShifts) :
    StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
      a03ZeroModeLeadingKernel dual Φ c ⟨T,σ,α,p.1,r,s⟩ p.2) := by
  have hgap : Measurable (fun y : A03SixTensorSpace => -a03RealLogGapSymbol T r s (a03SixGapLinear y)) :=
    ((a03RealLogGapSymbol_measurable T r s).comp a03SixGapLinear.continuous.measurable).neg
  have hM := (a03TensorMellinFactor_joint_continuous α c).stronglyMeasurable
  cases dual
  · have hfreq : StronglyMeasurable (fun p : ℝ×ℝ =>
        a03GaussianLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) :=
      a03FrequencyProfile_joint_stronglyMeasurable (fun v => a03GaussianLeadingTimeProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I))
        (a03GaussianLeadingTimeProfile_mellin_joint_measurable Φ hΦ T c σ α).stronglyMeasurable
    have hcomp : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
        a03GaussianLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I)
          (-a03RealLogGapSymbol T r s (a03SixGapLinear p.2))) := by
      simpa only [Function.comp_def] using hfreq.comp_measurable (measurable_fst.prodMk (hgap.comp measurable_snd))
    exact hM.mul hcomp
  · have hfreq : StronglyMeasurable (fun p : ℝ×ℝ =>
        a03GaussianDualLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) :=
      a03FrequencyProfile_joint_stronglyMeasurable (fun v => a03GaussianDualLeadingTimeProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I))
        (a03GaussianDualLeadingTimeProfile_mellin_joint_measurable Φ hΦ T c σ α).stronglyMeasurable
    have hcomp : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
        a03GaussianDualLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I)
          (-a03RealLogGapSymbol T r s (a03SixGapLinear p.2))) := by
      simpa only [Function.comp_def] using hfreq.comp_measurable (measurable_fst.prodMk (hgap.comp measurable_snd))
    exact hM.mul hcomp

theorem a03_zero_replacement_kernel_joint_stronglyMeasurable (dual : Bool)
    {c : ℝ} (hc : 0<c) (Φ : ℝ→ℂ) (hΦ : Continuous Φ) (T r s : ℝ)
    (σ α : MomentShifts) (hα : ∀ j,‖α j‖≤1/4) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) :
    StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
      a03ZeroModeReplacementKernel dual Φ c ⟨T,σ,α,p.1,r,s⟩ p.2) := by
  have hgap : Measurable (fun y : A03SixTensorSpace => -a03RealLogGapSymbol T r s (a03SixGapLinear y)) :=
    ((a03RealLogGapSymbol_measurable T r s).comp a03SixGapLinear.continuous.measurable).neg
  have hM := (a03TensorMellinFactor_joint_continuous α c).stronglyMeasurable
  have hΓ := a03GaussianTimeAmplitude_mellin_joint_continuous hc T σ α hα
  have hA : Measurable (fun p : ℝ×ℝ => a03GaussianTimeProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) :=
    (hΦ.measurable.comp measurable_snd).mul hΓ.measurable
  have hL := a03GaussianLeadingTimeProfile_mellin_joint_measurable Φ hΦ.measurable T c σ α
  have hE : Measurable (fun p : ℝ×ℝ => a03GaussianReplacementTimeProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) := by
    convert hA.sub hL using 1
    funext p
    simp only [Pi.sub_apply]
    rw [a03GaussianLeadingTimeProfile_eq_sub]
    simp
  cases dual
  · have hfreq : StronglyMeasurable (fun p : ℝ×ℝ =>
        a03GaussianReplacementFrequencyProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) :=
      a03FrequencyProfile_joint_stronglyMeasurable (fun v => a03GaussianReplacementTimeProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)) hE.stronglyMeasurable
    have hcomp : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
        a03GaussianReplacementFrequencyProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I)
          (-a03RealLogGapSymbol T r s (a03SixGapLinear p.2))) := by
      simpa only [Function.comp_def] using hfreq.comp_measurable (measurable_fst.prodMk (hgap.comp measurable_snd))
    exact hM.mul hcomp
  · have hr : ∀ j, |(rawMomentShifts T σ j).re|<1/2 := fun j =>
      ((Complex.abs_re_le_norm _).trans (hσ j)).trans_lt (by norm_num)
    have hD : Measurable (fun p : ℝ×ℝ => bblrDualMultiplier (T*p.2) (rawMomentShifts T σ)) :=
      (rectangular_dual_multiplier_continuous _ hr).measurable.comp (by fun_prop)
    have hLA := a03GaussianDualLeadingTimeProfile_mellin_joint_measurable Φ hΦ.measurable T c σ α
    have hAE : Measurable (fun p : ℝ×ℝ => a03GaussianDualReplacementTimeProfile Φ T σ σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) := by
      convert (hD.mul hA).sub hLA using 1
      funext p
      simp only [Pi.sub_apply,Pi.mul_apply]
      rw [a03GaussianDualLeadingTimeProfile_eq_sub]
      unfold a03GaussianDualTimeProfile a03GaussianTimeProfile a03ProfileProduct
      simp only [Pi.sub_apply]
      ring
    have hfreq : StronglyMeasurable (fun p : ℝ×ℝ =>
        a03GaussianDualReplacementFrequencyProfile Φ T σ σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) :=
      a03FrequencyProfile_joint_stronglyMeasurable (fun v => a03GaussianDualReplacementTimeProfile Φ T σ σ α ((c:ℂ)+(v:ℂ)*I)) hAE.stronglyMeasurable
    have hcomp : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
        a03GaussianDualReplacementFrequencyProfile Φ T σ σ α ((c:ℂ)+(p.1:ℂ)*I)
          (-a03RealLogGapSymbol T r s (a03SixGapLinear p.2))) := by
      simpa only [Function.comp_def] using hfreq.comp_measurable (measurable_fst.prodMk (hgap.comp measurable_snd))
    exact hM.mul hcomp

end
end Sechstmoment
