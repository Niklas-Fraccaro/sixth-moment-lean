import SixthMoment.Numerator.U.ZeroModes.GCDMellin.CountableJoint
import SixthMoment.Numerator.U.ZeroModes.GCDMellin.FrontHeightFubini
import SixthMoment.Numerator.U.ZeroModes.GCDMellin.InitialEtaJoin

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeGCDInitialDensity_joint_integrable_s_outer
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (hab : a.Coprime b) (A B : ℕ→ℂ) :
    Integrable (fun p : ℝ×(ℝ×(ℝ×ℝ)) =>
      a03ZeroModeGCDInitialDensity Φ T σ α g a b A B p.2.1
        ((ε:ℂ)+(p.2.2.1:ℂ)*I) ((ε:ℂ)+(p.2.2.2:ℂ)*I) (((1+ε:ℝ):ℂ)+(p.1:ℂ)*I))
      (volume.prod ((volume.restrict (Ioi 0)).prod (volume.prod volume))) := by
  have hJoint := a03ZeroModeGCDInitialKernel_joint_integrable_s_outer hΦ hSupp hT hε hε1
    σ α hα (Nat.mul_pos hg ha) (Nat.mul_pos hg hb) A B
  have hPos : ∀ᵐ p : ℝ×(ℝ×(ℝ×ℝ))
      ∂(volume.prod ((volume.restrict (Ioi 0)).prod (volume.prod volume))),0<p.2.1 :=
    Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually
      (Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually
        (ae_restrict_mem measurableSet_Ioi))
  apply hJoint.congr
  filter_upwards [hPos] with p hp
  apply a03ZeroModeGCDInitialKernel_commonAmplifier_eq_etaDensity Φ T σ α
    hg ha hb hab A B hp _ _ _ hρ
  · have h0 := (abs_le.mp ((Complex.abs_re_le_norm (α 0)).trans (hα 0))).1
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm (α 1)).trans (hα 1))).2
    norm_num [Complex.add_re,Complex.sub_re,Complex.mul_re]
    linarith
  · have h2 := (abs_le.mp ((Complex.abs_re_le_norm (α 2)).trans (hα 2))).1
    have h3 := (abs_le.mp ((Complex.abs_re_le_norm (α 3)).trans (hα 3))).2
    norm_num [Complex.add_re,Complex.sub_re,Complex.mul_re]
    linarith
  · norm_num [Complex.add_re,Complex.mul_re]
    linarith

theorem a03ZeroModeGCDEtaFrontBlock_height_integrable
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (hab : a.Coprime b) (A B : ℕ→ℂ) :
    Integrable (fun y : ℝ => a03ZeroModeRatioDoubleIntegral ε ε
      (fun u v => a03ZeroModeGCDEtaFrontBlock Φ T σ α g a b A B u v
        (((1+ε:ℝ):ℂ)+(y:ℂ)*I))) :=
  a03ZeroModeGCDEtaFrontBlock_height_integrable_of_joint Φ T σ α g a b A B ε ε (1+ε)
    (a03ZeroModeGCDInitialDensity_joint_integrable_s_outer hΦ hSupp hT hε hε1 σ α hα hρ hg ha hb hab A B)

end
end SixthMoment.Source
