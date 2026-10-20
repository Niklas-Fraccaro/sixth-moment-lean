import SixthMoment.Analysis.Complex.SimplePole
import SixthMoment.Analysis.Gaussian.Decay
import SixthMoment.Numerator.U.ZeroModes.Ratio.ContourIntegrability
import SixthMoment.Numerator.U.ZeroModes.Ratio.SideSwap


namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeRatioArithmeticKernel_primary_horizontal_tendsto_zero
    {ε δ d : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hd : a03ZeroModeRatioPrimaryLine ε≤d)
    (hdabs : |d|≤1) (hdsep : ε≤|d|) (z : ℝ) :
    Tendsto (fun y : ℝ => ∫ c in (a03ZeroModeRatioPrimaryLine ε)..ε,
      a03ZeroModeRatioArithmeticKernel α a b ((c:ℂ)+(y:ℂ)*I) ((d:ℂ)+(z:ℂ)*I) s)
        (cocompact ℝ) (𝓝 0) := by
  obtain ⟨D,hD,hbnd⟩ := a03ZeroModeRatioArithmeticKernel_gaussian_majorant hε hδ
  let Q : ℝ := D*(a03ZeroModeRatioGaussianConstant α 1)^2*(a:ℝ)^δ*(b:ℝ)^δ*ε⁻¹*
    ((1+|z|)^4*Real.exp (Real.pi*|z|-z^2))
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hyv : Tendsto (fun y : ℝ => |y|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hlim := (SixthMoment.gaussianPolynomialExponential_tendsto_zero 4 Real.pi).const_mul
    (|ε-a03ZeroModeRatioPrimaryLine ε| * Q)
  simp only [mul_zero] at hlim
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hyv.eventually (eventually_ge_atTop (1:ℝ))] with y hy
  have hnorm (c : ℝ) (hc : c∈uIoc (a03ZeroModeRatioPrimaryLine ε) ε) :
      ‖a03ZeroModeRatioArithmeticKernel α a b ((c:ℂ)+(y:ℂ)*I) ((d:ℂ)+(z:ℂ)*I) s‖≤
        Q*((1+|y|)^4*Real.exp (Real.pi*|y|-y^2)) := by
    have horder : a03ZeroModeRatioPrimaryLine ε≤ε := by
      unfold a03ZeroModeRatioPrimaryLine
      linarith
    rw [uIoc_of_le horder] at hc
    let u : ℂ := (c:ℂ)+(y:ℂ)*I
    let v : ℂ := (d:ℂ)+(z:ℂ)*I
    have huabs : |u.re|≤1 := by
      simp only [u,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero]
      apply abs_le.mpr
      unfold a03ZeroModeRatioPrimaryLine at hc
      constructor <;> linarith [hc.1, hc.2]
    have hreg : A03ZeroModeRatioContourRegion ε u v :=
      a03ZeroModeRatio_primary_rectangle_region hε (by linarith)
        (by simpa [u] using hc.1.le) (by simpa [v] using hd)
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
  exact (intervalIntegral.norm_integral_le_of_norm_le_const hnorm).trans_eq (by ring)

theorem a03ZeroModeRatioArithmeticKernel_primary_left_shift
    {ε δ d : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hd : a03ZeroModeRatioPrimaryLine ε≤d)
    (hdabs : |d|≤1) (hdsep : ε≤|d|) (z : ℝ) :
    verticalIntegral ε (fun u => a03ZeroModeRatioArithmeticKernel α a b
      u ((d:ℂ)+(z:ℂ)*I) s)=
        verticalIntegral (a03ZeroModeRatioPrimaryLine ε)
          (fun u => a03ZeroModeRatioArithmeticKernel α a b u ((d:ℂ)+(z:ℂ)*I) s)+
            a03ZeroModeRatioArithmeticNumerator α a b 0 ((d:ℂ)+(z:ℂ)*I) s/
              ((d:ℂ)+(z:ℂ)*I) := by
  let v : ℂ := (d:ℂ)+(z:ℂ)*I
  let H : ℂ→ℂ := fun u => a03ZeroModeRatioArithmeticNumerator α a b u v s/v
  let U : Set ℂ := {u | 1<(a03ZeroModeRatioEulerArgument α u v).re}
  have hU : IsOpen U := by
    apply isOpen_lt continuous_const
    unfold a03ZeroModeRatioEulerArgument
    fun_prop
  have hH : DifferentiableOn ℂ H U := by
    intro u hu
    exact ((a03ZeroModeRatioArithmeticNumerator_differentiableAt_comp α ha hb
      (by linarith : 1≤s.re) (U := id) (V := fun _ : ℂ => v)
        (by fun_prop) (by fun_prop) hu).div_const v).differentiableWithinAt
  have hstrip : ∀ u : ℂ,a03ZeroModeRatioPrimaryLine ε≤u.re → u.re≤ε → u∈U := by
    intro u hu _
    have hreg : A03ZeroModeRatioContourRegion ε u v :=
      a03ZeroModeRatio_primary_rectangle_region hε (by linarith) hu (by simpa [v] using hd)
    have hA := (a03ZeroModeRatio_contour_arguments_lower hε hα hreg).2.2
    exact lt_of_lt_of_le (by linarith : 1<1+ε) hA
  have he (u : ℂ) : H u/u=a03ZeroModeRatioArithmeticKernel α a b u ((d:ℂ)+(z:ℂ)*I) s := by
    dsimp [H,v,a03ZeroModeRatioArithmeticKernel]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hsecD : a03ZeroModeRatioSecondaryLine ε≤d := by
    unfold a03ZeroModeRatioPrimaryLine at hd
    unfold a03ZeroModeRatioSecondaryLine
    linarith
  have hregLines (c : ℝ) (hc : a03ZeroModeRatioPrimaryLine ε≤c) :
      a03ZeroModeRatioSecondaryLine ε≤c ∧ a03ZeroModeRatioSecondaryLine ε≤c+d := by
    unfold a03ZeroModeRatioPrimaryLine at hc hd
    unfold a03ZeroModeRatioSecondaryLine
    constructor <;> linarith
  have hleft := a03ZeroModeRatioArithmeticKernel_boundary_left_integrable hε hδ α hα hρ
    ha hb hs (hregLines _ le_rfl).1 hsecD (hregLines _ le_rfl).2
    (a03ZeroModeRatioLine_abs_bounds hε hε1 1).2 hdabs
    (a03ZeroModeRatioLine_abs_bounds hε hε1 1).1 hdsep z
  have hright := a03ZeroModeRatioArithmeticKernel_boundary_left_integrable hε hδ α hα hρ
    ha hb hs (hregLines ε (by unfold a03ZeroModeRatioPrimaryLine; linarith)).1 hsecD
    (hregLines ε (by unfold a03ZeroModeRatioPrimaryLine; linarith)).2
    (by rw [abs_of_pos hε]; linarith) hdabs (by rw [abs_of_pos hε]) hdsep z
  have hedge := a03ZeroModeRatioArithmeticKernel_primary_horizontal_tendsto_zero
    hε hε1 hδ α hα hρ ha hb hs hd hdabs hdsep z
  simp_rw [←he] at hleft hright hedge
  have hrect := SixthMoment.mellinRectangle_simplePole_shift H hU hH
    (by unfold a03ZeroModeRatioPrimaryLine; linarith) hε hstrip hleft hright hedge
  unfold verticalIntegral
  simp_rw [he] at hrect
  rw [hrect,mul_add]
  have hπ : (2*Real.pi:ℂ)≠0 := by exact_mod_cast (show 2*Real.pi≠0 by positivity)
  rw [←mul_assoc,one_div,inv_mul_cancel₀ hπ,one_mul]

theorem a03ZeroModeRatioArithmeticKernel_primary_right_shift
    {ε δ c : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hc : a03ZeroModeRatioPrimaryLine ε≤c)
    (hcabs : |c|≤1) (hcsep : ε≤|c|) (y : ℝ) :
    verticalIntegral ε (fun v => a03ZeroModeRatioArithmeticKernel α a b
      ((c:ℂ)+(y:ℂ)*I) v s)=
        verticalIntegral (a03ZeroModeRatioPrimaryLine ε)
          (fun v => a03ZeroModeRatioArithmeticKernel α a b ((c:ℂ)+(y:ℂ)*I) v s)+
            a03ZeroModeRatioArithmeticNumerator α a b ((c:ℂ)+(y:ℂ)*I) 0 s/
              ((c:ℂ)+(y:ℂ)*I) := by
  simpa only [a03ZeroModeRatioArithmeticKernel_sideSwap,
    a03ZeroModeRatioArithmeticNumerator_sideSwap] using
      a03ZeroModeRatioArithmeticKernel_primary_left_shift hε hε1 hδ
        (a03ZeroModeRatioSideSwap α) (a03ZeroModeRatioSideSwap_small hα)
          (a03ZeroModeRatioSideSwap_roots_nonzero hρ) hb ha hs hc hcabs hcsep y

end
end SixthMoment.Source
