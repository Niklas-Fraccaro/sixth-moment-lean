import SixthMoment.Numerator.U.ZeroModes.Linearization.Kernels
import SixthMoment.Numerator.U.ZeroModes.Replacement.Measurability

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 300000

theorem a03_zero_linear_kernel_joint_stronglyMeasurable (dual : Bool)
    (Φ : ℝ→ℂ) (hΦ : Measurable Φ) (T c r s : ℝ) (σ α : MomentShifts) :
    StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
      a03ZeroModeLinearKernel dual Φ c ⟨T,σ,α,p.1,r,s⟩ p.2) := by
  have hgap : Measurable (fun y : A03SixTensorSpace => -T*s*r*Real.exp (a03SixGapLinear y)) :=
    (by fun_prop : Continuous (fun y : A03SixTensorSpace => -T*s*r*Real.exp (a03SixGapLinear y))).measurable
  have hM := (a03TensorMellinFactor_joint_continuous α c).stronglyMeasurable
  cases dual
  · have hfreq : StronglyMeasurable (fun p : ℝ×ℝ =>
        a03GaussianLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) :=
      a03FrequencyProfile_joint_stronglyMeasurable (fun v => a03GaussianLeadingTimeProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I))
        (a03GaussianLeadingTimeProfile_mellin_joint_measurable Φ hΦ T c σ α).stronglyMeasurable
    have hcomp : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
        a03GaussianLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I)
          (-T*s*r*Real.exp (a03SixGapLinear p.2))) := by
      simpa only [Function.comp_def] using hfreq.comp_measurable (measurable_fst.prodMk (hgap.comp measurable_snd))
    exact hM.mul hcomp
  · have hfreq : StronglyMeasurable (fun p : ℝ×ℝ =>
        a03GaussianDualLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) :=
      a03FrequencyProfile_joint_stronglyMeasurable (fun v => a03GaussianDualLeadingTimeProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I))
        (a03GaussianDualLeadingTimeProfile_mellin_joint_measurable Φ hΦ T c σ α).stronglyMeasurable
    have hcomp : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
        a03GaussianDualLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I)
          (-T*s*r*Real.exp (a03SixGapLinear p.2))) := by
      simpa only [Function.comp_def] using hfreq.comp_measurable (measurable_fst.prodMk (hgap.comp measurable_snd))
    exact hM.mul hcomp


end
end SixthMoment
