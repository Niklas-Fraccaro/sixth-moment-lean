import Mathlib.MeasureTheory.Integral.Prod
import Sechstmoment.Numerator.U.ZeroModes.Ratio.ContourBounds


namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeRatioArithmeticKernel_differentiableAt_comp (α : MomentShifts)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1≤s.re)
    {U V : E→ℂ} {z : E}
    (hU : DifferentiableAt ℂ U z) (hV : DifferentiableAt ℂ V z)
    (hden : 1<(a03ZeroModeRatioEulerArgument α (U z) (V z)).re)
    (hu : U z≠0) (hv : V z≠0) :
    DifferentiableAt ℂ
      (fun y => a03ZeroModeRatioArithmeticKernel α a b (U y) (V y) s) z := by
  have hnum := a03ZeroModeRatioArithmeticNumerator_differentiableAt_comp α ha hb hs hU hV hden
  have hi := (differentiableAt_inv (mul_ne_zero hu hv)).comp z (hU.mul hV)
  convert hnum.mul hi using 1
  funext y
  exact div_eq_mul_inv _ _

theorem a03ZeroModeRatioArithmeticKernel_continuous_boundary
    {ε c d : ℝ} (hε : 0<ε) (α : MomentShifts)
    (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1≤s.re)
    (hc : a03ZeroModeRatioSecondaryLine ε≤c)
    (hd : a03ZeroModeRatioSecondaryLine ε≤d)
    (hcd : a03ZeroModeRatioSecondaryLine ε≤c+d)
    (hc0 : c≠0) (hd0 : d≠0) :
    Continuous (fun p : ℝ×ℝ => a03ZeroModeRatioArithmeticKernel α a b
      ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I) s) := by
  let F : (ℂ × ℂ) → ℂ := fun p => a03ZeroModeRatioArithmeticKernel α a b p.1 p.2 s
  let S : Set (ℂ × ℂ) := {p | 1<(a03ZeroModeRatioEulerArgument α p.1 p.2).re ∧ p.1≠0 ∧ p.2≠0}
  have hF : ContinuousOn F S := by
    intro p hp
    exact (a03ZeroModeRatioArithmeticKernel_differentiableAt_comp α ha hb hs
      (U := Prod.fst) (V := Prod.snd) (z := p) (by fun_prop) (by fun_prop)
        hp.1 hp.2.1 hp.2.2).continuousAt.continuousWithinAt
  apply hF.comp_continuous (by fun_prop : Continuous (fun p : ℝ×ℝ =>
    (((c:ℂ)+(p.1:ℂ)*I),((d:ℂ)+(p.2:ℂ)*I))))
  intro p
  have hreg : A03ZeroModeRatioContourRegion ε
      ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I) := by
    simpa only [A03ZeroModeRatioContourRegion,add_re,ofReal_re,mul_re,ofReal_im,
      I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero] using ⟨hc,hd,hcd⟩
  have hA := (a03ZeroModeRatio_contour_arguments_lower hε hα hreg).2.2
  refine ⟨by linarith,?_,?_⟩
  · intro he
    exact hc0 (by simpa using congrArg Complex.re he)
  · intro he
    exact hd0 (by simpa using congrArg Complex.re he)

theorem a03ZeroModeRatioArithmeticKernel_boundary_majorant
    {ε δ c d : ℝ} (hε : 0<ε) (hδ : 0<δ) (α : MomentShifts)
    (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hc : a03ZeroModeRatioSecondaryLine ε≤c)
    (hd : a03ZeroModeRatioSecondaryLine ε≤d)
    (hcd : a03ZeroModeRatioSecondaryLine ε≤c+d)
    (hcabs : |c|≤1) (hdabs : |d|≤1) (hcsep : ε≤|c|) (hdsep : ε≤|d|) :
    ∃ C : ℝ,0≤C ∧ ∀ y z : ℝ,
      ‖a03ZeroModeRatioArithmeticKernel α a b ((c:ℂ)+(y:ℂ)*I) ((d:ℂ)+(z:ℂ)*I) s‖≤
        C*((1+|y|)^4*Real.exp (Real.pi*|y|-y^2))*
          ((1+|z|)^4*Real.exp (Real.pi*|z|-z^2)) := by
  obtain ⟨D,hD,hbnd⟩ := a03ZeroModeRatioArithmeticKernel_gaussian_majorant hε hδ
  let C : ℝ := D*(a03ZeroModeRatioGaussianConstant α 1)^2*(a:ℝ)^δ*(b:ℝ)^δ*ε⁻¹*ε⁻¹
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro y z
  let u : ℂ := (c:ℂ)+(y:ℂ)*I
  let v : ℂ := (d:ℂ)+(z:ℂ)*I
  have hreg : A03ZeroModeRatioContourRegion ε u v := by
    simpa only [u,v,A03ZeroModeRatioContourRegion,add_re,ofReal_re,mul_re,ofReal_im,
      I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero] using ⟨hc,hd,hcd⟩
  have hiu : ‖u‖⁻¹≤ε⁻¹ := inv_anti₀ hε
    (hcsep.trans (by simpa [u] using Complex.abs_re_le_norm u))
  have hiv : ‖v‖⁻¹≤ε⁻¹ := inv_anti₀ hε
    (hdsep.trans (by simpa [v] using Complex.abs_re_le_norm v))
  have hm := hbnd α hα hρ a b ha hb u v s hs (by simpa [u] using hcabs)
    (by simpa [v] using hdabs) hreg
    (a03ZeroModeRatioDifferenceArgument_line_separation hε hα hcsep y 0)
    (a03ZeroModeRatioDifferenceArgument_line_separation hε hα hdsep z 1)
  calc
    _ ≤ D*(a03ZeroModeRatioGaussianConstant α 1)^2*(a:ℝ)^δ*(b:ℝ)^δ*ε⁻¹*ε⁻¹*
        (1+|y|)^4*(1+|z|)^4*Real.exp (Real.pi*(|y|+|z|)-y^2-z^2) := by
      apply hm.trans
      simp only [u,v,add_im,ofReal_im,mul_im,ofReal_re,I_re,I_im,mul_zero,mul_one,
        zero_add,add_zero]
      gcongr
    _ = _ := by
      rw [show Real.pi*(|y|+|z|)-y^2-z^2=(Real.pi*|y|-y^2)+(Real.pi*|z|-z^2) by ring,
        Real.exp_add]
      dsimp [C]
      ring

theorem a03ZeroModeRatioArithmeticKernel_boundary_joint_integrable
    {ε δ c d : ℝ} (hε : 0<ε) (hδ : 0<δ) (α : MomentShifts)
    (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hc : a03ZeroModeRatioSecondaryLine ε≤c)
    (hd : a03ZeroModeRatioSecondaryLine ε≤d)
    (hcd : a03ZeroModeRatioSecondaryLine ε≤c+d)
    (hcabs : |c|≤1) (hdabs : |d|≤1) (hcsep : ε≤|c|) (hdsep : ε≤|d|) :
    Integrable (fun p : ℝ×ℝ => a03ZeroModeRatioArithmeticKernel α a b
      ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I) s) (volume.prod volume) := by
  obtain ⟨C,_hC,hbnd⟩ := a03ZeroModeRatioArithmeticKernel_boundary_majorant hε hδ α hα hρ
    ha hb hs hc hd hcd hcabs hdabs hcsep hdsep
  have hc0 : c≠0 := by intro he; simp [he] at hcsep; linarith
  have hd0 : d≠0 := by intro he; simp [he] at hdsep; linarith
  have hcont := a03ZeroModeRatioArithmeticKernel_continuous_boundary hε α hα ha hb
    (by linarith : 1≤s.re) hc hd hcd hc0 hd0
  have hg := Sechstmoment.gaussianPolynomialExponential_integrable 4 Real.pi
  apply ((hg.mul_prod hg).const_mul C).mono' hcont.aestronglyMeasurable
  exact Eventually.of_forall (fun p => by simpa [mul_assoc] using hbnd p.1 p.2)

theorem a03ZeroModeRatioArithmeticKernel_boundary_left_integrable
    {ε δ c d : ℝ} (hε : 0<ε) (hδ : 0<δ) (α : MomentShifts)
    (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hc : a03ZeroModeRatioSecondaryLine ε≤c)
    (hd : a03ZeroModeRatioSecondaryLine ε≤d)
    (hcd : a03ZeroModeRatioSecondaryLine ε≤c+d)
    (hcabs : |c|≤1) (hdabs : |d|≤1) (hcsep : ε≤|c|) (hdsep : ε≤|d|)
    (z : ℝ) :
    Integrable (fun y : ℝ => a03ZeroModeRatioArithmeticKernel α a b
      ((c:ℂ)+(y:ℂ)*I) ((d:ℂ)+(z:ℂ)*I) s) := by
  obtain ⟨C,_hC,hbnd⟩ := a03ZeroModeRatioArithmeticKernel_boundary_majorant hε hδ α hα hρ
    ha hb hs hc hd hcd hcabs hdabs hcsep hdsep
  have hc0 : c≠0 := by intro he; simp [he] at hcsep; linarith
  have hd0 : d≠0 := by intro he; simp [he] at hdsep; linarith
  have hcont := (a03ZeroModeRatioArithmeticKernel_continuous_boundary hε α hα ha hb
    (by linarith : 1≤s.re) hc hd hcd hc0 hd0).comp
      (by fun_prop : Continuous (fun y : ℝ => (y,z)))
  apply ((Sechstmoment.gaussianPolynomialExponential_integrable 4 Real.pi).const_mul
    (C*((1+|z|)^4*Real.exp (Real.pi*|z|-z^2)))).mono' hcont.aestronglyMeasurable
  exact Eventually.of_forall (fun y => (hbnd y z).trans_eq (by ring))

end
end Sechstmoment.Source
