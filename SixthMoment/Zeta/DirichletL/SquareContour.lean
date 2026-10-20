import SixthMoment.Analysis.Complex.SimplePole
import SixthMoment.Analysis.Gaussian.Decay
import SixthMoment.Arithmetic.QuadraticDivisor.Definitions
import SixthMoment.Zeta.DirichletL.CompletedFunction


namespace SixthMoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

def dirichletSquareContour {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s z : ℂ) : ℂ :=
  Complex.exp (z^2) * (conductorCompletedL χ (s+z))^2

theorem dirichletSquareContour_differentiable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    Differentiable ℂ (dirichletSquareContour χ s) := by
  unfold dirichletSquareContour
  exact (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (z^2))).mul
    (((conductorCompletedL_differentiable χ hχ).comp (differentiable_id.const_add s)).pow 2)

theorem dirichletSquareContour_strip_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ 2 →
      ‖dirichletSquareContour χ s z‖ ≤ C*Real.exp (-z.im^2) := by
  obtain ⟨B, hB, hb⟩ := conductorCompletedL_strip_bound χ hχ (s.re-2) (s.re+2)
  refine ⟨Real.exp 4*B^2, by positivity, ?_⟩
  intro z hz
  have hL : ‖conductorCompletedL χ (s+z)‖ ≤ B :=
    hb (s+z) (by simp only [add_re]; linarith [(abs_le.mp hz).1])
      (by simp only [add_re]; linarith [(abs_le.mp hz).2])
  have he : ‖Complex.exp (z^2)‖ ≤ Real.exp 4*Real.exp (-z.im^2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hzsq : z.re^2 ≤ 4 := by nlinarith [(abs_le.mp hz).1, (abs_le.mp hz).2]
    norm_num only [pow_two, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    nlinarith [sq_nonneg z.im]
  rw [dirichletSquareContour, norm_mul, norm_pow]
  calc
    _ ≤ (Real.exp 4*Real.exp (-z.im^2))*B^2 := by gcongr
    _ = _ := by ring

theorem dirichletSquareContour_vertical_integrable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) (c : ℝ)
    (hc : |c| ≤ 2) (hc0 : c ≠ 0) :
    Integrable (fun v : ℝ =>
      dirichletSquareContour χ s ((c : ℂ)+(v : ℂ)*I)/((c : ℂ)+(v : ℂ)*I)) := by
  obtain ⟨C, hC, hb⟩ := dirichletSquareContour_strip_bound χ hχ s
  have hgauss : Integrable (fun v : ℝ => Real.exp (-v^2)) := by
    simpa using gaussianPolynomialExponential_integrable 0 0
  apply (hgauss.const_mul (C/|c|)).mono'
  · have hden (v : ℝ) : (c : ℂ)+(v : ℂ)*I ≠ 0 := by
      intro hv
      exact hc0 (by simpa using congrArg Complex.re hv)
    exact (((dirichletSquareContour_differentiable χ hχ s).continuous.comp
      (by fun_prop)).div (by fun_prop) hden).aestronglyMeasurable
  · apply Eventually.of_forall
    intro v
    have hp : 0 < |c| := abs_pos.mpr hc0
    have hn : |c| ≤ ‖(c : ℂ)+(v : ℂ)*I‖ := by
      simpa using Complex.abs_re_le_norm ((c : ℂ)+(v : ℂ)*I)
    rw [norm_div]
    have h := hb ((c : ℂ)+(v : ℂ)*I) (by simpa using hc)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_add] at h
    calc
      _ ≤ (C*Real.exp (-v^2))/|c| := div_le_div₀ (by positivity) h hp hn
      _ = _ := by ring

theorem dirichletSquareContour_horizontal_tendsto_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    Tendsto (fun v : ℝ => ∫ c in (-2 : ℝ)..2,
      dirichletSquareContour χ s ((c : ℂ)+(v : ℂ)*I)/((c : ℂ)+(v : ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := dirichletSquareContour_strip_bound χ hχ s
  have habs : Tendsto (fun v : ℝ => |v|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hlim : Tendsto (fun v : ℝ => 4*C*Real.exp (-v^2)) (cocompact ℝ) (𝓝 0) := by
    simpa using (gaussianPolynomialExponential_tendsto_zero 0 0).const_mul (4*C)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [habs.eventually (eventually_ge_atTop (1 : ℝ))] with v hv
  have hpoint (c : ℝ) (hc : c ∈ uIoc (-2 : ℝ) 2) :
      ‖dirichletSquareContour χ s ((c : ℂ)+(v : ℂ)*I)/((c : ℂ)+(v : ℂ)*I)‖ ≤
        C*Real.exp (-v^2) := by
    rw [uIoc_of_le (by norm_num)] at hc
    have hn : 1 ≤ ‖(c : ℂ)+(v : ℂ)*I‖ :=
      hv.trans (by simpa using Complex.abs_im_le_norm ((c : ℂ)+(v : ℂ)*I))
    rw [norm_div]
    apply (div_le_self (norm_nonneg _) hn).trans
    simpa using hb ((c : ℂ)+(v : ℂ)*I) (by simp; exact abs_le.mpr ⟨hc.1.le, hc.2⟩)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  convert h using 1
  ring_nf

theorem dirichletSquareContour_reflection {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive) (s z : ℂ) :
    dirichletSquareContour χ s (-z) =
      χ.rootNumber^2 * dirichletSquareContour χ⁻¹ (1-s) z := by
  have h := conductorCompletedL_one_sub χ hprim (1-s+z)
  rw [show 1-(1-s+z) = s + -z by ring] at h
  unfold dirichletSquareContour
  rw [neg_sq, h, mul_pow]
  ring

theorem dirichletSquareContour_split {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (s : ℂ) :
    (∫ v : ℝ, dirichletSquareContour χ s (2+(v : ℂ)*I)/(2+(v : ℂ)*I)) +
      χ.rootNumber^2 *
        (∫ v : ℝ, dirichletSquareContour χ⁻¹ (1-s) (2+(v : ℂ)*I)/(2+(v : ℂ)*I)) =
      (2*Real.pi : ℂ) * (conductorCompletedL χ s)^2 := by
  have h := mellinRectangle_simplePole_shift (dirichletSquareContour χ s)
    isOpen_univ (dirichletSquareContour_differentiable χ hχ s).differentiableOn
    (a := -2) (b := 2) (by norm_num) (by norm_num)
    (fun _ _ _ => mem_univ _)
    (dirichletSquareContour_vertical_integrable χ hχ s (-2) (by norm_num) (by norm_num))
    (dirichletSquareContour_vertical_integrable χ hχ s 2 (by norm_num) (by norm_num))
    (dirichletSquareContour_horizontal_tendsto_zero χ hχ s)
  have hleft : (∫ v : ℝ, dirichletSquareContour χ s (-2+(v : ℂ)*I)/(-2+(v : ℂ)*I)) =
      -(χ.rootNumber^2 *
        (∫ v : ℝ, dirichletSquareContour χ⁻¹ (1-s) (2+(v : ℂ)*I)/(2+(v : ℂ)*I))) := by
    have hneg : (∫ v : ℝ, dirichletSquareContour χ s (-2+((-v : ℝ) : ℂ)*I)/
        (-2+((-v : ℝ) : ℂ)*I)) =
        ∫ v : ℝ, dirichletSquareContour χ s (-2+(v : ℂ)*I)/(-2+(v : ℂ)*I) := by
      simpa only [neg_one_mul, inv_neg, abs_neg, abs_one, inv_one, one_smul] using
        Measure.integral_comp_mul_left (fun v : ℝ =>
          dirichletSquareContour χ s (-2+(v : ℂ)*I)/(-2+(v : ℂ)*I)) (-1)
    rw [← hneg]
    calc
      _ = ∫ v : ℝ, -(χ.rootNumber^2 *
          (dirichletSquareContour χ⁻¹ (1-s) (2+(v : ℂ)*I)/(2+(v : ℂ)*I))) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun v => by
          dsimp only
          have he : (-2 : ℂ)+((-v : ℝ) : ℂ)*I = -(2+(v : ℂ)*I) := by push_cast; ring
          rw [he, dirichletSquareContour_reflection χ hprim, div_neg]
          ring
      _ = _ := by rw [integral_neg, integral_const_mul]
  norm_num only [Complex.ofReal_ofNat, Complex.ofReal_neg] at h
  rw [hleft] at h
  simpa only [dirichletSquareContour, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Complex.exp_zero, add_zero, one_mul] using (by linear_combination h :
      (∫ v : ℝ, dirichletSquareContour χ s (2+(v : ℂ)*I)/(2+(v : ℂ)*I)) +
        χ.rootNumber^2 *
          (∫ v : ℝ, dirichletSquareContour χ⁻¹ (1-s) (2+(v : ℂ)*I)/(2+(v : ℂ)*I)) =
        (2*Real.pi : ℂ) * dirichletSquareContour χ s 0)

def dirichletSquareCompletedIntegral {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (∫ v : ℝ, dirichletSquareContour χ s (2+(v : ℂ)*I)/(2+(v : ℂ)*I))/(2*Real.pi : ℂ)

theorem dirichletCompletedL_square_smooth_decomposition {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (s : ℂ) :
    (conductorCompletedL χ s)^2 =
      dirichletSquareCompletedIntegral χ s +
        χ.rootNumber^2 * dirichletSquareCompletedIntegral χ⁻¹ (1-s) := by
  have h := dirichletSquareContour_split χ hχ hprim s
  have hp : (2*Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  unfold dirichletSquareCompletedIntegral
  field_simp
  simp only [mul_comm I] at h ⊢
  linear_combination h.symm

end
end SixthMoment.Source
