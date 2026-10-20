import Sechstmoment.Numerator.U.ZeroModes.Ratio.DoubleShift
import Sechstmoment.Numerator.U.ZeroModes.Ratio.WeightedSecondaryShift

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeRatioWeightedKernel_joint_integrable_primary
    (L M : ℝ) {ε δ c d : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hc : a03ZeroModeRatioPrimaryLine ε≤c) (hd : a03ZeroModeRatioPrimaryLine ε≤d)
    (hcabs : |c|≤1) (hdabs : |d|≤1) (hcsep : ε≤|c|) (hdsep : ε≤|d|) :
    Integrable (fun p : ℝ×ℝ => a03ZeroModeRatioWeightedKernel L M α a b
      ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I) s) (volume.prod volume) :=
  a03RatioExponentialPair_joint_integrable L M c d
    (fun u v => a03ZeroModeRatioArithmeticKernel α a b u v s)
    (a03ZeroModeRatioArithmeticKernel_joint_integrable_primary hε hε1 hδ α hα hρ
      ha hb hs hc hd hcabs hdabs hcsep hdsep)

theorem a03ZeroModeRatioWeightedKernel_double_shift
    (L M : ℝ)
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re) :
    a03ZeroModeRatioDoubleIntegral ε ε (fun u v => a03ZeroModeRatioWeightedKernel L M α a b u v s)=
      a03ZeroModeRatioDoubleIntegral (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioPrimaryLine ε)
        (fun u v => a03ZeroModeRatioWeightedKernel L M α a b u v s)+
      verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioWeightedLeftResidue L M α a b s)+
      verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioWeightedRightResidue L M α a b s)+
        a03ZeroModeRatioArithmeticNumerator α a b 0 0 s := by
  let F : ℂ→ℂ→ℂ := fun u v => a03ZeroModeRatioWeightedKernel L M α a b u v s
  let p : ℝ := a03ZeroModeRatioPrimaryLine ε
  have hpε : p≤ε := by dsimp [p,a03ZeroModeRatioPrimaryLine]; linarith
  have hpabs : |p|≤1 := (a03ZeroModeRatioLine_abs_bounds hε hε1 1).2
  have hpsep : ε≤|p| := (a03ZeroModeRatioLine_abs_bounds hε hε1 1).1
  have hεabs : |ε|≤1 := by rw [abs_of_pos hε]; linarith
  have hεsep : ε≤|ε| := by rw [abs_of_pos hε]
  have hep := a03ZeroModeRatioWeightedKernel_joint_integrable_primary L M hε hε1 hδ α hα hρ
    ha hb hs hpε le_rfl hεabs hpabs hεsep hpsep
  have hpp := a03ZeroModeRatioWeightedKernel_joint_integrable_primary L M hε hε1 hδ α hα hρ
    ha hb hs (c := p) (d := p) le_rfl le_rfl hpabs hpabs hpsep hpsep
  have hinnerEP : Integrable (fun y : ℝ => verticalIntegral p (F ((ε:ℂ)+(y:ℂ)*I))) := by
    simpa only [verticalIntegral,F] using hep.integral_prod_left.const_mul (1/(2*Real.pi):ℂ)
  have hinnerPPswap : Integrable (fun z : ℝ =>
      verticalIntegral p (fun u => F u ((p:ℂ)+(z:ℂ)*I))) := by
    simpa only [verticalIntegral,F,Function.comp_apply,Prod.swap] using
      hpp.swap.integral_prod_left.const_mul (1/(2*Real.pi):ℂ)
  have hresR := a03ZeroModeRatioWeightedRightResidue_line_integrable L M hε hε1 hδ α hα hρ
    ha hb hs (c := ε) (by unfold a03ZeroModeRatioSecondaryLine; linarith) hεabs hεsep
  have hresL := a03ZeroModeRatioWeightedLeftResidue_line_integrable L M hε hε1 hδ α hα hρ
    ha hb hs (c := p) (by dsimp [p,a03ZeroModeRatioPrimaryLine,a03ZeroModeRatioSecondaryLine]; linarith)
      hpabs hpsep
  have hfirst : a03ZeroModeRatioDoubleIntegral ε ε F=
      a03ZeroModeRatioDoubleIntegral ε p F+verticalIntegral ε (a03ZeroModeRatioWeightedRightResidue L M α a b s) := by
    unfold a03ZeroModeRatioDoubleIntegral
    have hpoint (y : ℝ) : verticalIntegral ε (F ((ε:ℂ)+(y:ℂ)*I))=
        verticalIntegral p (F ((ε:ℂ)+(y:ℂ)*I))+
          a03ZeroModeRatioWeightedRightResidue L M α a b s ((ε:ℂ)+(y:ℂ)*I) :=
      a03ZeroModeRatioWeightedKernel_primary_right_shift L M hε hε1 hδ α hα hρ ha hb hs
        hpε hεabs hεsep y
    change (1/(2*Real.pi):ℂ)*(∫ y : ℝ,verticalIntegral ε (F ((ε:ℂ)+(y:ℂ)*I)))=_
    simp_rw [hpoint]
    rw [integral_add hinnerEP hresR,mul_add]
    rfl
  have hsecond : a03ZeroModeRatioDoubleIntegral ε p F=
      a03ZeroModeRatioDoubleIntegral p p F+verticalIntegral p (a03ZeroModeRatioWeightedLeftResidue L M α a b s) := by
    rw [a03ZeroModeRatioDoubleIntegral_fubini ε p F hep]
    have hpoint (z : ℝ) : verticalIntegral ε (fun u => F u ((p:ℂ)+(z:ℂ)*I))=
        verticalIntegral p (fun u => F u ((p:ℂ)+(z:ℂ)*I))+
          a03ZeroModeRatioWeightedLeftResidue L M α a b s ((p:ℂ)+(z:ℂ)*I) :=
      a03ZeroModeRatioWeightedKernel_primary_left_shift L M hε hε1 hδ α hα hρ ha hb hs
        le_rfl hpabs hpsep z
    have he : a03ZeroModeRatioDoubleIntegral p ε (fun v u => F u v)=
        a03ZeroModeRatioDoubleIntegral p p (fun v u => F u v)+
          verticalIntegral p (a03ZeroModeRatioWeightedLeftResidue L M α a b s) := by
      unfold a03ZeroModeRatioDoubleIntegral
      change (1/(2*Real.pi):ℂ)*(∫ z : ℝ,verticalIntegral ε (fun u => F u ((p:ℂ)+(z:ℂ)*I)))=_
      simp_rw [hpoint]
      rw [integral_add hinnerPPswap hresL,mul_add]
      rfl
    rw [he,←a03ZeroModeRatioDoubleIntegral_fubini p p F hpp]
  change a03ZeroModeRatioDoubleIntegral ε ε F=_
  rw [hfirst,hsecond,a03ZeroModeRatioWeightedLeftResidue_secondary_shift L M hε hε1 hδ α hα hρ ha hb hs,
    a03ZeroModeRatioWeightedRightResidue_positive_shift L M hε hε1 hδ α hα hρ ha hb hs]
  ring


end
end Sechstmoment.Source
