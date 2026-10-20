import Sechstmoment.Numerator.U.ZeroModes.Ratio.SecondaryShift

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeRatioArithmeticKernel_primary_horizontal_majorant
    {ε δ d : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hd : a03ZeroModeRatioPrimaryLine ε≤d)
    (hdabs : |d|≤1) (hdsep : ε≤|d|) (z : ℝ) :
    ∃ Q : ℝ,0≤Q ∧ ∀ y : ℝ,1≤|y| → ∀ c∈Icc (a03ZeroModeRatioPrimaryLine ε) ε,
      ‖a03ZeroModeRatioArithmeticKernel α a b ((c:ℂ)+(y:ℂ)*I) ((d:ℂ)+(z:ℂ)*I) s‖≤
        Q*((1+|y|)^4*Real.exp (Real.pi*|y|-y^2)) := by
  obtain ⟨D,hD,hbnd⟩ := a03ZeroModeRatioArithmeticKernel_gaussian_majorant hε hδ
  let Q : ℝ := D*(a03ZeroModeRatioGaussianConstant α 1)^2*(a:ℝ)^δ*(b:ℝ)^δ*ε⁻¹*
    ((1+|z|)^4*Real.exp (Real.pi*|z|-z^2))
  have hQ : 0≤Q := by dsimp [Q]; positivity
  refine ⟨Q,hQ,?_⟩
  intro y hy c hc
  let u : ℂ := (c:ℂ)+(y:ℂ)*I
  let v : ℂ := (d:ℂ)+(z:ℂ)*I
  have huabs : |u.re|≤1 := by
    simp only [u,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero]
    apply abs_le.mpr
    unfold a03ZeroModeRatioPrimaryLine at hc
    constructor <;> linarith [hc.1, hc.2]
  have hreg : A03ZeroModeRatioContourRegion ε u v :=
    a03ZeroModeRatio_primary_rectangle_region hε (by linarith)
      (by simpa [u] using hc.1) (by simpa [v] using hd)
  have hiu : ‖u‖⁻¹≤1 := inv_le_one_of_one_le₀
    (hy.trans (by simpa [u] using Complex.abs_im_le_norm u))
  have hiv : ‖v‖⁻¹≤ε⁻¹ := inv_anti₀ hε
    (hdsep.trans (by simpa [v] using Complex.abs_re_le_norm v))
  have hm := hbnd α hα hρ a b ha hb u v s hs huabs (by simpa [v] using hdabs) hreg
    (a03ZeroModeRatioDifferenceArgument_horizontal_separation hε hε1 hα hy c 0)
    (a03ZeroModeRatioDifferenceArgument_line_separation hε hα hdsep z 1)
  have hi : ‖u‖⁻¹*‖v‖⁻¹≤ε⁻¹ := by
    exact (mul_le_mul hiu hiv (inv_nonneg.mpr (norm_nonneg _)) (by norm_num)).trans_eq
      (one_mul _)
  have hmi : D*(a03ZeroModeRatioGaussianConstant α 1)^2*(a:ℝ)^δ*(b:ℝ)^δ*
      ‖u‖⁻¹*‖v‖⁻¹*(1+|u.im|)^4*(1+|v.im|)^4*
        Real.exp (Real.pi*(|u.im|+|v.im|)-u.im^2-v.im^2)≤
    D*(a03ZeroModeRatioGaussianConstant α 1)^2*(a:ℝ)^δ*(b:ℝ)^δ*ε⁻¹*
      (1+|u.im|)^4*(1+|v.im|)^4*
        Real.exp (Real.pi*(|u.im|+|v.im|)-u.im^2-v.im^2) := by
    convert mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hi (show 0≤D*(a03ZeroModeRatioGaussianConstant α 1)^2*
        (a:ℝ)^δ*(b:ℝ)^δ by positivity))
      (show 0≤(1+|u.im|)^4*(1+|v.im|)^4*
        Real.exp (Real.pi*(|u.im|+|v.im|)-u.im^2-v.im^2) by positivity) using 1 <;> ring
  calc
    _ ≤ D*(a03ZeroModeRatioGaussianConstant α 1)^2*(a:ℝ)^δ*(b:ℝ)^δ*1*ε⁻¹*
        (1+|y|)^4*(1+|z|)^4*Real.exp (Real.pi*(|y|+|z|)-y^2-z^2) := by
      exact (hm.trans hmi).trans_eq (by simp [u,v])
    _ = _ := by
      rw [show Real.pi*(|y|+|z|)-y^2-z^2=(Real.pi*|y|-y^2)+(Real.pi*|z|-z^2) by ring,
        Real.exp_add]
      dsimp [Q]
      ring

theorem a03ZeroModeRatioLeftResidueKernel_horizontal_majorant
    {ε δ l r : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hl : a03ZeroModeRatioSecondaryLine ε≤l) (hr : r≤1) (_hlr : l≤r) :
    ∃ Q : ℝ,0≤Q ∧ ∀ y : ℝ,1≤|y| → ∀ c∈Icc l r,
      ‖a03ZeroModeRatioLeftResidueKernel α a b s ((c:ℂ)+(y:ℂ)*I)‖≤
        Q*((1+|y|)^4*Real.exp (Real.pi*|y|-y^2)) := by
  obtain ⟨C,hC,hbnd⟩ := a03ZeroModeRatioLeftResidueKernel_gaussian_majorant hε hε1 hδ α hα hρ
  let Q : ℝ := C*(a:ℝ)^δ*(b:ℝ)^δ
  have hQ : 0≤Q := by dsimp [Q]; positivity
  refine ⟨Q,hQ,?_⟩
  intro y hy c hc
  have hcsec : a03ZeroModeRatioSecondaryLine ε≤c := hl.trans hc.1
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

end
end Sechstmoment.Source
