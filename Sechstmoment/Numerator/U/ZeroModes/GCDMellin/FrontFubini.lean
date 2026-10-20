import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.InitialJoint

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeRatioDoubleIntegral_eq_product (c d : ℝ) (F : ℂ→ℂ→ℂ)
    (hF : Integrable (fun p : ℝ×ℝ => F ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I)) (volume.prod volume)) :
    a03ZeroModeRatioDoubleIntegral c d F=(1/(2*Real.pi):ℂ)^2*
      ∫p : ℝ×ℝ,F ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I) ∂(volume.prod volume) := by
  unfold a03ZeroModeRatioDoubleIntegral verticalIntegral
  rw [integral_const_mul,integral_prod _ hF]
  ring

theorem a03ZeroModeGCDEtaFrontBlock_initial_fubini
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {s : ℂ} (hs : s.re=1+ε) :
    a03ZeroModeRatioDoubleIntegral ε ε (fun u v => a03ZeroModeGCDEtaFrontBlock Φ T σ α g a b A B u v s)=
      ∫x : ℝ in Ioi 0,(x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
        a03ZeroModeRatioDoubleIntegral ε ε (fun u v => a03ZeroModeRatioPhysicalKernel α g a b A B x u v s) := by
  let F : ℝ×(ℝ×ℝ)→ℂ := fun p => a03ZeroModeGCDInitialDensity Φ T σ α g a b A B p.1
    ((ε:ℂ)+(p.2.1:ℂ)*I) ((ε:ℂ)+(p.2.2:ℂ)*I) s
  have hJoint : Integrable F ((volume.restrict (Ioi 0)).prod (volume.prod volume)) :=
    a03ZeroModeGCDInitialDensity_joint_integrable hΦ hSupp hT hε hε1 σ α hα hρ hg ha hb A B hs
  have hAfter : Integrable (fun p : ℝ×ℝ => a03ZeroModeGCDEtaFrontBlock Φ T σ α g a b A B
      ((ε:ℂ)+(p.1:ℂ)*I) ((ε:ℂ)+(p.2:ℂ)*I) s) (volume.prod volume) := hJoint.swap.integral_prod_left
  have hInner (x : ℝ) (hx : 0<x) : Integrable (fun p : ℝ×ℝ => a03ZeroModeGCDInitialDensity Φ T σ α g a b A B x
      ((ε:ℂ)+(p.1:ℂ)*I) ((ε:ℂ)+(p.2:ℂ)*I) s) (volume.prod volume) := by
    have hpε : a03ZeroModeRatioPrimaryLine ε≤ε := by unfold a03ZeroModeRatioPrimaryLine; linarith
    have hεabs : |ε|≤1 := by rw [abs_of_pos hε]; linarith
    have hεsep : ε≤|ε| := by rw [abs_of_pos hε]
    have hi := a03ZeroModeRatioWeightedKernel_joint_integrable_primary
      (a03ZeroModeRatioPhysicalLogLeft g a x) (a03ZeroModeRatioPhysicalLogRight g b x)
        hε hε1 hε α hα hρ ha.ne' hb.ne' (by linarith : 1+ε≤s.re)
        hpε hpε hεabs hεabs hεsep hεsep
    apply (hi.const_mul ((x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
      a03ZeroModeRatioPhysicalPrefactor α g a b A B x s)).congr
    apply ae_of_all
    intro p
    unfold a03ZeroModeGCDInitialDensity
    dsimp only []
    rw [a03ZeroModeRatioPhysicalKernel_eq_weighted α hg ha hb A B hx]
    ring
  rw [a03ZeroModeRatioDoubleIntegral_eq_product ε ε _ hAfter]
  change (1/(2*Real.pi):ℂ)^2*(∫p : ℝ×ℝ,(∫x : ℝ in Ioi 0,F (x,p)) ∂(volume.prod volume))=_
  rw [←integral_integral_swap hJoint,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change (1/(2*Real.pi):ℂ)^2*(∫p : ℝ×ℝ,
    a03ZeroModeGCDInitialDensity Φ T σ α g a b A B x ((ε:ℂ)+(p.1:ℂ)*I) ((ε:ℂ)+(p.2:ℂ)*I) s
      ∂(volume.prod volume))=_
  rw [←a03ZeroModeRatioDoubleIntegral_eq_product ε ε
    (fun u v => a03ZeroModeGCDInitialDensity Φ T σ α g a b A B x u v s) (hInner x hx)]
  dsimp only []
  unfold a03ZeroModeGCDInitialDensity
  rw [a03ZeroModeRatioDoubleIntegral_const_mul]

end
end Sechstmoment.Source
