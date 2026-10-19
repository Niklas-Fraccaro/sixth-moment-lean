import Sechstmoment.Analysis.Complex.ContourShift
import Sechstmoment.Numerator.U.ZeroModes.Ratio.PrimaryShift

/-! Actual single-residue ratio contours. The remaining variable is moved
to -1/2+ε with the genuine arithmetic numerator retained throughout. -/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioLeftResidueKernel (α : MomentShifts) (a b : ℕ) (s v : ℂ) : ℂ :=
  a03ZeroModeRatioArithmeticNumerator α a b 0 v s/v

def a03ZeroModeRatioRightResidueKernel (α : MomentShifts) (a b : ℕ) (s u : ℂ) : ℂ :=
  a03ZeroModeRatioArithmeticNumerator α a b u 0 s/u

theorem a03ZeroModeRatioLeftResidueKernel_eq (α : MomentShifts) (a b : ℕ) (s : ℂ)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) {v : ℂ}
    (hv : v≠a03ZeroModeRatioRoot α 1) :
    a03ZeroModeRatioLeftResidueKernel α a b s v=
      riemannZeta (1+α 0-α 1)*(a03ZeroModeRatioWeight α v/v)*
        riemannZeta (1+α 2-α 3+2*v)*riemannZeta s*
          riemannZeta (a03ZeroModeRatioEulerArgument α 0 v-1+s)/
            riemannZeta (a03ZeroModeRatioEulerArgument α 0 v)*
              a03ZeroModeRatioEtaPair α a b 0 v s := by
  unfold a03ZeroModeRatioLeftResidueKernel a03ZeroModeRatioArithmeticNumerator
    a03ZeroModeRatioRemovedPair
  rw [a03ZeroModeRatioRemovedDifference_zero α 0 (hρ 0),
    a03ZeroModeRatioRemovedDifference_eq α 1 (hρ 1) hv,
    a03ZeroModeRatioDifferenceArgument_zero,a03ZeroModeRatioDifferenceArgument_one]
  simp only [mul_zero,add_zero]
  ring

theorem a03ZeroModeRatioLeftResidueKernel_uniform_gaussian_majorant
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    : ∃ C : ℝ,0≤C ∧ ∀ α : MomentShifts,
      (∀ j : Fin 4,‖α j‖≤ε/8) → (∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) →
      ∀ a b : ℕ,a≠0 → b≠0 → ∀ v s : ℂ,
      1+ε≤s.re → |v.re|≤1 → a03ZeroModeRatioSecondaryLine ε≤v.re →
      ε≤‖1-a03ZeroModeRatioDifferenceArgument α 1 v‖ →
      ‖a03ZeroModeRatioLeftResidueKernel α a b s v‖≤
        C*‖riemannZeta (1+α 0-α 1)‖*a03ZeroModeRatioGaussianConstant α 1*
          (a:ℝ)^δ*(b:ℝ)^δ*‖v‖⁻¹*(1+|v.im|)^4*
          Real.exp (Real.pi*|v.im|-v.im^2) := by
  obtain ⟨D,hD,hEta⟩ := a03ZeroModeRatioEtaPair_subpower_bound hδ
  obtain ⟨E,hE,hZeta⟩ := Sechstmoment.riemannZeta_norm_le_exp_halfPlane hε hε
  let Z : ℝ := Sechstmoment.zetaDirichletMajorant (1+ε)
  have hZ : 0≤Z := Sechstmoment.zetaDirichletMajorant_nonneg _
  let C : ℝ := E*Real.exp (Real.pi*(ε/8))*Z^3*D
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro α hα hρ a b ha hb v s hs hv hc hsep
  let B : ℝ := a03ZeroModeRatioGaussianConstant α 1
  have hB : 0≤B := a03ZeroModeRatioGaussianConstant_nonneg _ _
  have hreg := a03ZeroModeRatio_single_residue_left_region hε (by linarith) hc
  have hl := a03ZeroModeRatio_contour_arguments_lower hε hα hreg
  have hroot : v≠a03ZeroModeRatioRoot α 1 := by
    intro he
    rw [a03ZeroModeRatioDifferenceArgument_norm_distance,he,sub_self,norm_zero] at hsep
    linarith
  have hg := a03ZeroModeRatioWeight_gaussian_bound α (by norm_num : (0:ℝ)≤1) hv
  have hz : ‖riemannZeta (1+α 2-α 3+2*v)‖≤E*Real.exp (Real.pi*(|v.im|+ε/8)) := by
    have him : |(a03ZeroModeRatioDifferenceArgument α 1 v).im|≤2*(|v.im|+ε/8) := by
      rw [a03ZeroModeRatioDifferenceArgument_im_abs]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
      exact (abs_sub _ _).trans (add_le_add le_rfl
        ((Complex.abs_im_le_norm _).trans (a03ZeroModeRatioRoot_norm_le hα 1)))
    rw [←a03ZeroModeRatioDifferenceArgument_one]
    exact (hZeta _ hl.2.1 hsep).trans (by gcongr; nlinarith [Real.pi_pos])
  have hzs : ‖riemannZeta s‖≤Z :=
    Sechstmoment.riemannZeta_norm_le_dirichlet (by linarith : 1<1+ε) hs
  have hzm : ‖riemannZeta (a03ZeroModeRatioEulerArgument α 0 v-1+s)‖≤Z := by
    apply Sechstmoment.riemannZeta_norm_le_dirichlet (by linarith : 1<1+ε)
    simp only [add_re,sub_re,one_re]
    linarith [hl.2.2]
  have hzi : ‖riemannZeta (a03ZeroModeRatioEulerArgument α 0 v)‖⁻¹≤Z := by
    simpa only [norm_inv] using Sechstmoment.riemannZeta_inv_norm_le_dirichlet
      (by linarith : 1<1+ε) hl.2.2
  have het := hEta α a b ha hb 0 v s (by linarith : 1≤s.re)
    (hε.le.trans hl.1) (hε.le.trans hl.2.1) (by linarith [hl.2.2])
  rw [a03ZeroModeRatioLeftResidueKernel_eq α a b s hρ hroot]
  simp only [norm_mul,div_eq_mul_inv,norm_inv]
  calc
    _ ≤ ‖riemannZeta (1+α 0-α 1)‖*(B*(1+|v.im|)^4*Real.exp (-v.im^2)*‖v‖⁻¹)*
        (E*Real.exp (Real.pi*(|v.im|+ε/8)))*Z*Z*Z*(D*(a:ℝ)^δ*(b:ℝ)^δ) := by gcongr
    _ = _ := by
      have he : Real.exp (-v.im^2)*Real.exp (Real.pi*(|v.im|+ε/8))=
          Real.exp (Real.pi*(ε/8))*Real.exp (Real.pi*|v.im|-v.im^2) := by
        rw [←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      calc
        _ = ‖riemannZeta (1+α 0-α 1)‖*B*E*Z^3*D*(a:ℝ)^δ*(b:ℝ)^δ*‖v‖⁻¹*
            (1+|v.im|)^4*(Real.exp (-v.im^2)*Real.exp (Real.pi*(|v.im|+ε/8))) := by ring
        _ = _ := by rw [he]; dsimp [C,B]; ring


theorem a03ZeroModeRatioLeftResidueKernel_gaussian_majorant
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) :
    ∃ C : ℝ,0≤C ∧ ∀ a b : ℕ,a≠0 → b≠0 → ∀ v s : ℂ,
      1+ε≤s.re → |v.re|≤1 → a03ZeroModeRatioSecondaryLine ε≤v.re →
      ε≤‖1-a03ZeroModeRatioDifferenceArgument α 1 v‖ →
      ‖a03ZeroModeRatioLeftResidueKernel α a b s v‖≤
        C*(a:ℝ)^δ*(b:ℝ)^δ*‖v‖⁻¹*(1+|v.im|)^4*
          Real.exp (Real.pi*|v.im|-v.im^2) := by
  obtain ⟨D,hD,hbnd⟩ := a03ZeroModeRatioLeftResidueKernel_uniform_gaussian_majorant hε hε1 hδ
  refine ⟨D*‖riemannZeta (1+α 0-α 1)‖*a03ZeroModeRatioGaussianConstant α 1,
    mul_nonneg (mul_nonneg hD (norm_nonneg _)) (a03ZeroModeRatioGaussianConstant_nonneg _ _),?_⟩
  intro a b ha hb v s hs hv hc hsep
  exact hbnd α hα hρ a b ha hb v s hs hv hc hsep

theorem a03ZeroModeRatioLeftResidueKernel_line_integrable
    {ε δ c : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hc : a03ZeroModeRatioSecondaryLine ε≤c) (hcabs : |c|≤1) (hcsep : ε≤|c|) :
    Integrable (fun y : ℝ => a03ZeroModeRatioLeftResidueKernel α a b s ((c:ℂ)+(y:ℂ)*I)) := by
  obtain ⟨C,hC,hbnd⟩ := a03ZeroModeRatioLeftResidueKernel_gaussian_majorant hε hε1 hδ α hα hρ
  have hcont : Continuous (fun y : ℝ => a03ZeroModeRatioLeftResidueKernel α a b s ((c:ℂ)+(y:ℂ)*I)) := by
    rw [continuous_iff_continuousAt]
    intro y
    let v : ℂ := (c:ℂ)+(y:ℂ)*I
    have hreg := a03ZeroModeRatio_single_residue_left_region hε (by linarith) (v := v)
      (by simpa [v] using hc)
    have hA := (a03ZeroModeRatio_contour_arguments_lower hε hα hreg).2.2
    have hv0 : v≠0 := by
      intro he
      have hre := congrArg Complex.re he
      simp [v] at hre
      rw [hre,abs_zero] at hcsep
      linarith
    have hnum := a03ZeroModeRatioArithmeticNumerator_differentiableAt_comp α ha hb
      (by linarith : 1≤s.re) (U := fun _ : ℂ => 0) (V := id) (z := v)
        (by fun_prop) (by fun_prop) (by linarith : 1<(a03ZeroModeRatioEulerArgument α 0 v).re)
    have hquot : ContinuousAt (a03ZeroModeRatioLeftResidueKernel α a b s) v :=
      (hnum.div differentiableAt_id hv0).continuousAt
    exact hquot.comp_of_eq
      (by fun_prop : ContinuousAt (fun y : ℝ => (c:ℂ)+(y:ℂ)*I) y) rfl
  apply ((Sechstmoment.gaussianPolynomialExponential_integrable 4 Real.pi).const_mul
    (C*(a:ℝ)^δ*(b:ℝ)^δ*ε⁻¹)).mono' hcont.aestronglyMeasurable
  exact Eventually.of_forall (fun y => by
    have hi : ‖(c:ℂ)+(y:ℂ)*I‖⁻¹≤ε⁻¹ := inv_anti₀ hε
      (hcsep.trans (by simpa using Complex.abs_re_le_norm ((c:ℂ)+(y:ℂ)*I)))
    have h := hbnd a b ha hb ((c:ℂ)+(y:ℂ)*I) s hs (by simpa using hcabs)
      (by simpa using hc) (a03ZeroModeRatioDifferenceArgument_line_separation hε hα hcsep y 1)
    apply h.trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_re,I_im,mul_zero,mul_one,zero_add,add_zero]
    have hp : 0≤C*(a:ℝ)^δ*(b:ℝ)^δ := by positivity
    convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hp)
      (show 0≤(1+|y|)^4*Real.exp (Real.pi*|y|-y^2) by positivity) using 1
    ring)

theorem a03ZeroModeRatioLeftResidueKernel_horizontal_tendsto_zero
    {ε δ l r : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hl : a03ZeroModeRatioSecondaryLine ε≤l) (hr : r≤1) (hlr : l≤r) :
    Tendsto (fun y : ℝ => ∫ c in l..r,
      a03ZeroModeRatioLeftResidueKernel α a b s ((c:ℂ)+(y:ℂ)*I))
        (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C,hC,hbnd⟩ := a03ZeroModeRatioLeftResidueKernel_gaussian_majorant hε hε1 hδ α hα hρ
  let Q : ℝ := C*(a:ℝ)^δ*(b:ℝ)^δ
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hyv : Tendsto (fun y : ℝ => |y|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hlim := (Sechstmoment.gaussianPolynomialExponential_tendsto_zero 4 Real.pi).const_mul (|r-l| * Q)
  simp only [mul_zero] at hlim
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hyv.eventually (eventually_ge_atTop (1:ℝ))] with y hy
  have hnorm (c : ℝ) (hc : c∈uIoc l r) :
      ‖a03ZeroModeRatioLeftResidueKernel α a b s ((c:ℂ)+(y:ℂ)*I)‖≤
        Q*((1+|y|)^4*Real.exp (Real.pi*|y|-y^2)) := by
    rw [uIoc_of_le hlr] at hc
    have hcsec : a03ZeroModeRatioSecondaryLine ε≤c := hl.trans hc.1.le
    have hcabs : |c|≤1 := by
      apply abs_le.mpr
      unfold a03ZeroModeRatioSecondaryLine at hl
      constructor <;> linarith [hc.1,hc.2]
    have hi : ‖(c:ℂ)+(y:ℂ)*I‖⁻¹≤1 := inv_le_one_of_one_le₀
      (hy.trans (by simpa using Complex.abs_im_le_norm ((c:ℂ)+(y:ℂ)*I)))
    have h := hbnd a b ha hb ((c:ℂ)+(y:ℂ)*I) s hs (by simpa using hcabs)
      (by simpa using hcsec)
      (a03ZeroModeRatioDifferenceArgument_horizontal_separation hε hε1 hα hy c 1)
    apply h.trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_re,I_im,mul_zero,mul_one,zero_add,add_zero]
    dsimp [Q]
    have hp : 0≤C*(a:ℝ)^δ*(b:ℝ)^δ := by positivity
    convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hp)
      (show 0≤(1+|y|)^4*Real.exp (Real.pi*|y|-y^2) by positivity) using 1 <;> ring
  exact (intervalIntegral.norm_integral_le_of_norm_le_const hnorm).trans_eq (by ring)

theorem a03ZeroModeRatioLeftResidueKernel_secondary_shift
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re) :
    verticalIntegral (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioLeftResidueKernel α a b s)=
      verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioLeftResidueKernel α a b s) := by
  let U : Set ℂ := {v | 1<(a03ZeroModeRatioEulerArgument α 0 v).re ∧ v.re<0}
  have hF : DifferentiableOn ℂ (a03ZeroModeRatioLeftResidueKernel α a b s) U := by
    intro v hv
    have hv0 : v≠0 := by
      intro he
      have hh := hv.2
      rw [he,zero_re] at hh
      linarith
    exact ((a03ZeroModeRatioArithmeticNumerator_differentiableAt_comp α ha hb
      (by linarith : 1≤s.re) (U := fun _ : ℂ => 0) (V := id) (z := v)
        (by fun_prop) (by fun_prop) hv.1).div differentiableAt_id hv0).differentiableWithinAt
  have hstrip : ∀ v : ℂ,a03ZeroModeRatioSecondaryLine ε≤v.re →
      v.re≤a03ZeroModeRatioPrimaryLine ε → v∈U := by
    intro v hl hr
    have hreg := a03ZeroModeRatio_single_residue_left_region hε (by linarith) hl
    have hA := (a03ZeroModeRatio_contour_arguments_lower hε hα hreg).2.2
    exact ⟨by linarith,by unfold a03ZeroModeRatioPrimaryLine at hr; linarith⟩
  exact Sechstmoment.bblrRectangle_verticalIntegral_shift _ hF
    (by unfold a03ZeroModeRatioPrimaryLine a03ZeroModeRatioSecondaryLine; linarith) hstrip
    (a03ZeroModeRatioLeftResidueKernel_line_integrable hε hε1 hδ α hα hρ ha hb hs le_rfl
      (a03ZeroModeRatioLine_abs_bounds hε hε1 2).2 (a03ZeroModeRatioLine_abs_bounds hε hε1 2).1)
    (a03ZeroModeRatioLeftResidueKernel_line_integrable hε hε1 hδ α hα hρ ha hb hs
      (by unfold a03ZeroModeRatioPrimaryLine a03ZeroModeRatioSecondaryLine; linarith)
        (a03ZeroModeRatioLine_abs_bounds hε hε1 1).2 (a03ZeroModeRatioLine_abs_bounds hε hε1 1).1)
    (a03ZeroModeRatioLeftResidueKernel_horizontal_tendsto_zero hε hε1 hδ α hα hρ ha hb hs le_rfl
      (by unfold a03ZeroModeRatioPrimaryLine; linarith)
        (by unfold a03ZeroModeRatioPrimaryLine a03ZeroModeRatioSecondaryLine; linarith))

theorem a03ZeroModeRatioLeftResidueKernel_positive_shift
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re) :
    verticalIntegral ε (a03ZeroModeRatioLeftResidueKernel α a b s)=
      verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioLeftResidueKernel α a b s)+
        a03ZeroModeRatioArithmeticNumerator α a b 0 0 s := by
  let H : ℂ→ℂ := fun v => a03ZeroModeRatioArithmeticNumerator α a b 0 v s
  let U : Set ℂ := {v | 1<(a03ZeroModeRatioEulerArgument α 0 v).re}
  have hU : IsOpen U := by
    apply isOpen_lt continuous_const
    unfold a03ZeroModeRatioEulerArgument
    fun_prop
  have hH : DifferentiableOn ℂ H U := by
    intro v hv
    exact (a03ZeroModeRatioArithmeticNumerator_differentiableAt_comp α ha hb
      (by linarith : 1≤s.re) (U := fun _ : ℂ => 0) (V := id) (z := v)
        (by fun_prop) (by fun_prop) hv).differentiableWithinAt
  have hstrip : ∀ v : ℂ,a03ZeroModeRatioPrimaryLine ε≤v.re → v.re≤ε → v∈U := by
    intro v hv _
    have hvs : a03ZeroModeRatioSecondaryLine ε≤v.re := by
      unfold a03ZeroModeRatioPrimaryLine at hv
      unfold a03ZeroModeRatioSecondaryLine
      linarith
    have hreg := a03ZeroModeRatio_single_residue_left_region hε (by linarith) hvs
    have hA := (a03ZeroModeRatio_contour_arguments_lower hε hα hreg).2.2
    exact lt_of_lt_of_le (by linarith : 1<1+ε) hA
  have hrect := Sechstmoment.mellinRectangle_simplePole_shift H hU hH
    (by unfold a03ZeroModeRatioPrimaryLine; linarith) hε hstrip
    (a03ZeroModeRatioLeftResidueKernel_line_integrable hε hε1 hδ α hα hρ ha hb hs
      (by unfold a03ZeroModeRatioPrimaryLine a03ZeroModeRatioSecondaryLine; linarith)
        (a03ZeroModeRatioLine_abs_bounds hε hε1 1).2 (a03ZeroModeRatioLine_abs_bounds hε hε1 1).1)
    (a03ZeroModeRatioLeftResidueKernel_line_integrable hε hε1 hδ α hα hρ ha hb hs
      (by unfold a03ZeroModeRatioSecondaryLine; linarith) (by rw [abs_of_pos hε]; linarith)
        (by rw [abs_of_pos hε]))
    (a03ZeroModeRatioLeftResidueKernel_horizontal_tendsto_zero hε hε1 hδ α hα hρ ha hb hs
      (by unfold a03ZeroModeRatioPrimaryLine a03ZeroModeRatioSecondaryLine; linarith)
        (by linarith) (by unfold a03ZeroModeRatioPrimaryLine; linarith))
  have hshift : verticalIntegral ε (a03ZeroModeRatioLeftResidueKernel α a b s)=
      verticalIntegral (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioLeftResidueKernel α a b s)+H 0 := by
    unfold verticalIntegral
    change (1/(2*Real.pi):ℂ)*(∫ y : ℝ,H ((ε:ℂ)+(y:ℂ)*I)/((ε:ℂ)+(y:ℂ)*I))=_
    rw [hrect,mul_add]
    have hπ : (2*Real.pi:ℂ)≠0 := by exact_mod_cast (show 2*Real.pi≠0 by positivity)
    rw [←mul_assoc,one_div,inv_mul_cancel₀ hπ,one_mul]
    rfl
  exact hshift.trans (by rw [a03ZeroModeRatioLeftResidueKernel_secondary_shift hε hε1 hδ α hα hρ ha hb hs])

theorem a03ZeroModeRatioRightResidueKernel_secondary_shift
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re) :
    verticalIntegral (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioRightResidueKernel α a b s)=
      verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioRightResidueKernel α a b s) := by
  have he : a03ZeroModeRatioLeftResidueKernel (a03ZeroModeRatioSideSwap α) b a s=
      a03ZeroModeRatioRightResidueKernel α a b s := by
    funext u
    unfold a03ZeroModeRatioLeftResidueKernel a03ZeroModeRatioRightResidueKernel
    rw [a03ZeroModeRatioArithmeticNumerator_sideSwap]
  simpa only [he] using
    a03ZeroModeRatioLeftResidueKernel_secondary_shift hε hε1 hδ (a03ZeroModeRatioSideSwap α)
      (a03ZeroModeRatioSideSwap_small hα) (a03ZeroModeRatioSideSwap_roots_nonzero hρ) hb ha hs

theorem a03ZeroModeRatioRightResidueKernel_positive_shift
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re) :
    verticalIntegral ε (a03ZeroModeRatioRightResidueKernel α a b s)=
      verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioRightResidueKernel α a b s)+
        a03ZeroModeRatioArithmeticNumerator α a b 0 0 s := by
  have he : a03ZeroModeRatioLeftResidueKernel (a03ZeroModeRatioSideSwap α) b a s=
      a03ZeroModeRatioRightResidueKernel α a b s := by
    funext u
    unfold a03ZeroModeRatioLeftResidueKernel a03ZeroModeRatioRightResidueKernel
    rw [a03ZeroModeRatioArithmeticNumerator_sideSwap]
  simpa only [he,a03ZeroModeRatioArithmeticNumerator_sideSwap] using
    a03ZeroModeRatioLeftResidueKernel_positive_shift hε hε1 hδ (a03ZeroModeRatioSideSwap α)
      (a03ZeroModeRatioSideSwap_small hα) (a03ZeroModeRatioSideSwap_roots_nonzero hρ) hb ha hs

end
end Sechstmoment.Source
