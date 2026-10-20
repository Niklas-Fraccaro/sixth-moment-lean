import SixthMoment.Numerator.U.ZeroModes.Ratio.SecondaryShift


namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioDoubleIntegral (c d : ℝ) (F : ℂ→ℂ→ℂ) : ℂ :=
  verticalIntegral c (fun u => verticalIntegral d (F u))

theorem a03ZeroModeRatioDoubleIntegral_fubini (c d : ℝ) (F : ℂ→ℂ→ℂ)
    (hF : Integrable (fun p : ℝ×ℝ => F ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I))
      (volume.prod volume)) :
    a03ZeroModeRatioDoubleIntegral c d F=
      a03ZeroModeRatioDoubleIntegral d c (fun v u => F u v) := by
  unfold a03ZeroModeRatioDoubleIntegral verticalIntegral
  simp only [integral_const_mul]
  rw [integral_integral_swap hF]

theorem a03ZeroModeRatioRightResidueKernel_line_integrable
    {ε δ c : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hc : a03ZeroModeRatioSecondaryLine ε≤c) (hcabs : |c|≤1) (hcsep : ε≤|c|) :
    Integrable (fun y : ℝ => a03ZeroModeRatioRightResidueKernel α a b s ((c:ℂ)+(y:ℂ)*I)) := by
  have he : a03ZeroModeRatioLeftResidueKernel (a03ZeroModeRatioSideSwap α) b a s=
      a03ZeroModeRatioRightResidueKernel α a b s := by
    funext u
    unfold a03ZeroModeRatioLeftResidueKernel a03ZeroModeRatioRightResidueKernel
    rw [a03ZeroModeRatioArithmeticNumerator_sideSwap]
  simpa only [he] using
    a03ZeroModeRatioLeftResidueKernel_line_integrable hε hε1 hδ (a03ZeroModeRatioSideSwap α)
      (a03ZeroModeRatioSideSwap_small hα) (a03ZeroModeRatioSideSwap_roots_nonzero hρ)
        hb ha hs hc hcabs hcsep

theorem a03ZeroModeRatioArithmeticKernel_joint_integrable_primary
    {ε δ c d : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hc : a03ZeroModeRatioPrimaryLine ε≤c) (hd : a03ZeroModeRatioPrimaryLine ε≤d)
    (hcabs : |c|≤1) (hdabs : |d|≤1) (hcsep : ε≤|c|) (hdsep : ε≤|d|) :
    Integrable (fun p : ℝ×ℝ => a03ZeroModeRatioArithmeticKernel α a b
      ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I) s) (volume.prod volume) := by
  apply a03ZeroModeRatioArithmeticKernel_boundary_joint_integrable hε hδ α hα hρ ha hb hs
    _ _ _ hcabs hdabs hcsep hdsep
  · unfold a03ZeroModeRatioPrimaryLine at hc
    unfold a03ZeroModeRatioSecondaryLine
    linarith
  · unfold a03ZeroModeRatioPrimaryLine at hd
    unfold a03ZeroModeRatioSecondaryLine
    linarith
  · unfold a03ZeroModeRatioPrimaryLine at hc hd
    unfold a03ZeroModeRatioSecondaryLine
    linarith

theorem a03ZeroModeRatioArithmeticKernel_double_shift
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re) :
    a03ZeroModeRatioDoubleIntegral ε ε (fun u v => a03ZeroModeRatioArithmeticKernel α a b u v s)=
      a03ZeroModeRatioDoubleIntegral (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioPrimaryLine ε)
        (fun u v => a03ZeroModeRatioArithmeticKernel α a b u v s)+
      verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioLeftResidueKernel α a b s)+
      verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioRightResidueKernel α a b s)+
        a03ZeroModeRatioArithmeticNumerator α a b 0 0 s := by
  let F : ℂ→ℂ→ℂ := fun u v => a03ZeroModeRatioArithmeticKernel α a b u v s
  let p : ℝ := a03ZeroModeRatioPrimaryLine ε
  have hpε : p≤ε := by dsimp [p,a03ZeroModeRatioPrimaryLine]; linarith
  have hpabs : |p|≤1 := (a03ZeroModeRatioLine_abs_bounds hε hε1 1).2
  have hpsep : ε≤|p| := (a03ZeroModeRatioLine_abs_bounds hε hε1 1).1
  have hεabs : |ε|≤1 := by rw [abs_of_pos hε]; linarith
  have hεsep : ε≤|ε| := by rw [abs_of_pos hε]
  have hep := a03ZeroModeRatioArithmeticKernel_joint_integrable_primary hε hε1 hδ α hα hρ
    ha hb hs hpε le_rfl hεabs hpabs hεsep hpsep
  have hpp := a03ZeroModeRatioArithmeticKernel_joint_integrable_primary hε hε1 hδ α hα hρ
    ha hb hs (c := p) (d := p) le_rfl le_rfl hpabs hpabs hpsep hpsep
  have hinnerEP : Integrable (fun y : ℝ => verticalIntegral p (F ((ε:ℂ)+(y:ℂ)*I))) := by
    simpa only [verticalIntegral,F] using hep.integral_prod_left.const_mul (1/(2*Real.pi):ℂ)
  have hinnerPPswap : Integrable (fun z : ℝ =>
      verticalIntegral p (fun u => F u ((p:ℂ)+(z:ℂ)*I))) := by
    simpa only [verticalIntegral,F,Function.comp_apply,Prod.swap] using
      hpp.swap.integral_prod_left.const_mul (1/(2*Real.pi):ℂ)
  have hresR := a03ZeroModeRatioRightResidueKernel_line_integrable hε hε1 hδ α hα hρ
    ha hb hs (c := ε) (by unfold a03ZeroModeRatioSecondaryLine; linarith) hεabs hεsep
  have hresL := a03ZeroModeRatioLeftResidueKernel_line_integrable hε hε1 hδ α hα hρ
    ha hb hs (c := p) (by dsimp [p,a03ZeroModeRatioPrimaryLine,a03ZeroModeRatioSecondaryLine]; linarith)
      hpabs hpsep
  have hfirst : a03ZeroModeRatioDoubleIntegral ε ε F=
      a03ZeroModeRatioDoubleIntegral ε p F+verticalIntegral ε (a03ZeroModeRatioRightResidueKernel α a b s) := by
    unfold a03ZeroModeRatioDoubleIntegral
    have hpoint (y : ℝ) : verticalIntegral ε (F ((ε:ℂ)+(y:ℂ)*I))=
        verticalIntegral p (F ((ε:ℂ)+(y:ℂ)*I))+
          a03ZeroModeRatioRightResidueKernel α a b s ((ε:ℂ)+(y:ℂ)*I) :=
      a03ZeroModeRatioArithmeticKernel_primary_right_shift hε hε1 hδ α hα hρ ha hb hs
        hpε hεabs hεsep y
    change (1/(2*Real.pi):ℂ)*(∫ y : ℝ,verticalIntegral ε (F ((ε:ℂ)+(y:ℂ)*I)))=_
    simp_rw [hpoint]
    rw [integral_add hinnerEP hresR,mul_add]
    rfl
  have hsecond : a03ZeroModeRatioDoubleIntegral ε p F=
      a03ZeroModeRatioDoubleIntegral p p F+verticalIntegral p (a03ZeroModeRatioLeftResidueKernel α a b s) := by
    rw [a03ZeroModeRatioDoubleIntegral_fubini ε p F hep]
    have hpoint (z : ℝ) : verticalIntegral ε (fun u => F u ((p:ℂ)+(z:ℂ)*I))=
        verticalIntegral p (fun u => F u ((p:ℂ)+(z:ℂ)*I))+
          a03ZeroModeRatioLeftResidueKernel α a b s ((p:ℂ)+(z:ℂ)*I) :=
      a03ZeroModeRatioArithmeticKernel_primary_left_shift hε hε1 hδ α hα hρ ha hb hs
        le_rfl hpabs hpsep z
    have he : a03ZeroModeRatioDoubleIntegral p ε (fun v u => F u v)=
        a03ZeroModeRatioDoubleIntegral p p (fun v u => F u v)+
          verticalIntegral p (a03ZeroModeRatioLeftResidueKernel α a b s) := by
      unfold a03ZeroModeRatioDoubleIntegral
      change (1/(2*Real.pi):ℂ)*(∫ z : ℝ,verticalIntegral ε (fun u => F u ((p:ℂ)+(z:ℂ)*I)))=_
      simp_rw [hpoint]
      rw [integral_add hinnerPPswap hresL,mul_add]
      rfl
    rw [he,←a03ZeroModeRatioDoubleIntegral_fubini p p F hpp]
  change a03ZeroModeRatioDoubleIntegral ε ε F=_
  rw [hfirst,hsecond,a03ZeroModeRatioLeftResidueKernel_secondary_shift hε hε1 hδ α hα hρ ha hb hs,
    a03ZeroModeRatioRightResidueKernel_positive_shift hε hε1 hδ α hα hρ ha hb hs]
  ring

theorem a03ZeroModeRatioArithmeticNumerator_double_residue (α : MomentShifts)
    (a b : ℕ) (s : ℂ) (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) :
    a03ZeroModeRatioArithmeticNumerator α a b 0 0 s=
      riemannZeta (1+α 0-α 1)*riemannZeta (1+α 2-α 3)*riemannZeta s*
        riemannZeta (1+α 0-α 1+α 2-α 3+s)/riemannZeta (2+α 0-α 1+α 2-α 3)*
          a03ZeroModeRatioEtaPair α a b 0 0 s := by
  unfold a03ZeroModeRatioArithmeticNumerator
  rw [a03ZeroModeRatioRemovedPair_zero α hρ]
  have he : a03ZeroModeRatioEulerArgument α 0 0-1+s=1+α 0-α 1+α 2-α 3+s := by
    unfold a03ZeroModeRatioEulerArgument
    ring
  rw [he]
  simp only [a03ZeroModeRatioEulerArgument,mul_zero,add_zero]

end
end SixthMoment.Source
