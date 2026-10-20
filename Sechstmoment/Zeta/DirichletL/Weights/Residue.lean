import Sechstmoment.Zeta.DirichletL.Weights.Shift


namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

theorem squareSmoothGammaContour_differentiableAt (s : ℂ) (a : ℕ) (x : ℝ)
    (hx : 0 < x) {w : ℂ} (hw : 0 < (s+(a : ℂ)+w).re) :
    DifferentiableAt ℂ (squareSmoothGammaContour s a x) w := by
  have hΓ : DifferentiableAt ℂ Complex.Gamma ((s+(a : ℂ)+w)/2) := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have h := congrArg Complex.re hn
    simp only [Complex.div_ofNat_re, neg_re, natCast_re] at h
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hΓcomp : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma ((s+(a : ℂ)+z)/2)) w :=
    DifferentiableAt.comp (f := fun z : ℂ => (s+(a : ℂ)+z)/2) (g := Complex.Gamma)
      w hΓ (by fun_prop)
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hp : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ)^(-z)) w :=
    (differentiable_neg.const_cpow (Or.inl hxne)).differentiableAt
  unfold squareSmoothGammaContour
  exact ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (z^2)) w).mul
    ((hΓcomp.div_const _).pow 2)).mul hp

theorem squareSmoothGammaContour_strip_bound (s : ℂ) (a : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hu : 0 < s.re+(a : ℝ)+u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, u ≤ w.re → w.re ≤ v →
      ‖squareSmoothGammaContour s a x w‖ ≤ C*Real.exp (-w.im^2) := by
  obtain ⟨B,hB,hbound⟩ := realGamma_norm_bounded_on_positive_interval
    (a := (s.re+(a : ℝ)+u)/2) (b := (s.re+(a : ℝ)+v)/2) (by linarith)
  let D := ‖Complex.Gamma ((s+(a : ℂ))/2)‖
  let P := x^(-u)+x^(-v)
  let L := |u|+|v|
  refine ⟨Real.exp (L^2)*(B/D)^2*P, by dsimp [P]; positivity, ?_⟩
  intro w hwu hwv
  have hΓ : ‖Complex.Gamma ((s+(a : ℂ)+w)/2)‖ ≤ B := by
    apply (gamma_norm_le_realGamma_re (s := (s+(a : ℂ)+w)/2) ?_).trans
    · apply hbound
      simp only [Complex.div_ofNat_re, add_re, natCast_re]
      constructor <;> linarith
    · simp only [Complex.div_ofNat_re, add_re, natCast_re]
      linarith
  have he : ‖Complex.exp (w^2)‖ ≤ Real.exp (L^2)*Real.exp (-w.im^2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlo : -L ≤ w.re := by dsimp [L]; linarith [neg_le_abs u, abs_nonneg v]
    have hhi : w.re ≤ L := by dsimp [L]; linarith [le_abs_self v, abs_nonneg u]
    have hp := mul_nonneg (sub_nonneg.mpr hhi) (by linarith : 0 ≤ L+w.re)
    norm_num only [pow_two, mul_re]
    nlinarith
  have hp : ‖(x : ℂ)^(-w)‖ ≤ P := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, neg_re]
    dsimp [P]
    by_cases hx1 : 1 ≤ x
    · have h := Real.rpow_le_rpow_of_exponent_le hx1 (show -w.re ≤ -u by linarith)
      exact h.trans (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
    · have h := Real.rpow_le_rpow_of_exponent_ge hx (le_of_not_ge hx1)
        (show -v ≤ -w.re by linarith)
      exact h.trans (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))
  rw [squareSmoothGammaContour, norm_mul, norm_mul, norm_pow, norm_div]
  calc
    _ ≤ (Real.exp (L^2)*Real.exp (-w.im^2))*(B/D)^2*P := by
      dsimp only [D]
      gcongr
    _ = _ := by ring

theorem squareSmoothGammaContour_vertical_integrable (s : ℂ) (a : ℕ) (x c : ℝ)
    (hx : 0 < x) (hc : 0 < s.re+(a : ℝ)+c) (hc0 : c ≠ 0) :
    Integrable (fun y : ℝ => squareSmoothGammaContour s a x ((c : ℂ)+(y : ℂ)*I)/
      ((c : ℂ)+(y : ℂ)*I)) := by
  obtain ⟨B,hB,hbound⟩ := squareSmoothGammaContour_strip_bound s a x c c hx hc
  have hcont : Continuous (fun y : ℝ => squareSmoothGammaContour s a x ((c : ℂ)+(y : ℂ)*I)/
      ((c : ℂ)+(y : ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have harg : 0 < (s+(a : ℂ)+((c : ℂ)+(y : ℂ)*I)).re := by simpa using hc
    have hH := (squareSmoothGammaContour_differentiableAt s a x hx harg).continuousAt
    exact (ContinuousAt.comp (f := fun y : ℝ => (c : ℂ)+(y : ℂ)*I)
      (g := squareSmoothGammaContour s a x) hH (by fun_prop)).div (by fun_prop) (by
        intro h; exact hc0 (by simpa using congrArg Complex.re h))
  apply vertical_integrable_of_gaussian_bound
    (fun w : ℂ => squareSmoothGammaContour s a x w/w) c (B/|c|) hcont
  intro y
  have hden : |c| ≤ ‖(c : ℂ)+(y : ℂ)*I‖ := by
    simpa using Complex.abs_re_le_norm ((c : ℂ)+(y : ℂ)*I)
  rw [norm_div]
  have hnum : ‖squareSmoothGammaContour s a x ((c : ℂ)+(y : ℂ)*I)‖ ≤ B*Real.exp (-y^2) := by
    simpa using hbound ((c : ℂ)+(y : ℂ)*I) (by simp) (by simp)
  calc
    _ ≤ (B*Real.exp (-y^2))/|c| :=
      div_le_div₀ (by positivity) hnum (abs_pos.mpr hc0) hden
    _ = _ := by ring

theorem squareSmoothGammaContour_horizontal_tendsto_zero (s : ℂ) (a : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hu : 0 < s.re+(a : ℝ)+u) (huv : u ≤ v) :
    Tendsto (fun y : ℝ => ∫ c in u..v,
      squareSmoothGammaContour s a x ((c : ℂ)+(y : ℂ)*I)/((c : ℂ)+(y : ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨B,hB,hbound⟩ := squareSmoothGammaContour_strip_bound s a x u v hx hu
  have habs : Tendsto (fun y : ℝ => |y|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hlim : Tendsto (fun y : ℝ => (v-u)*B*Real.exp (-y^2)) (cocompact ℝ) (𝓝 0) := by
    simpa using (gaussianPolynomialExponential_tendsto_zero 0 0).const_mul ((v-u)*B)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [habs.eventually (eventually_ge_atTop (1 : ℝ))] with y hy
  have hpoint (c : ℝ) (hc : c ∈ uIoc u v) :
      ‖squareSmoothGammaContour s a x ((c : ℂ)+(y : ℂ)*I)/((c : ℂ)+(y : ℂ)*I)‖ ≤
        B*Real.exp (-y^2) := by
    rw [uIoc_of_le huv] at hc
    have hden : 1 ≤ ‖(c : ℂ)+(y : ℂ)*I‖ :=
      hy.trans (by simpa using Complex.abs_im_le_norm ((c : ℂ)+(y : ℂ)*I))
    rw [norm_div]
    apply (div_le_self (norm_nonneg _) hden).trans
    simpa using hbound ((c : ℂ)+(y : ℂ)*I) (by simpa using hc.1.le) (by simpa using hc.2)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [abs_of_nonneg (sub_nonneg.mpr huv)] at h
  convert h using 1
  ring

theorem squareSmoothWeight_eq_residue_left (s : ℂ) (a : ℕ) (x r : ℝ)
    (hx : 0 < x) (hr : 0 < r) (hr' : r < s.re+(a : ℝ)) :
    squareSmoothWeight s a x = 1+
      (∫ y : ℝ, squareSmoothGammaContour s a x ((-r : ℝ)+(y : ℂ)*I)/
        ((-r : ℝ)+(y : ℂ)*I))/(2*Real.pi : ℂ) := by
  let U : Set ℂ := {w | 0 < (s+(a : ℂ)+w).re}
  have hU : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hH : DifferentiableOn ℂ (squareSmoothGammaContour s a x) U := fun w hw =>
    (squareSmoothGammaContour_differentiableAt s a x hx hw).differentiableWithinAt
  have harg : 0 < s.re+(a : ℝ)+(-r) := by linarith
  have h := mellinRectangle_simplePole_shift (squareSmoothGammaContour s a x) hU hH
    (a := -r) (b := 2) (by linarith) (by norm_num)
    (fun w hw _ => by change 0 < s.re+(a : ℝ)+w.re; linarith)
    (squareSmoothGammaContour_vertical_integrable s a x (-r) hx harg (by linarith))
    (squareSmoothGammaContour_vertical_integrable s a x 2 hx (by
      have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      linarith) (by norm_num))
    (squareSmoothGammaContour_horizontal_tendsto_zero s a x (-r) 2 hx harg (by linarith))
  have hΓ : Complex.Gamma ((s+(a : ℂ))/2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.div_ofNat_re, add_re, natCast_re]
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  have h0 : squareSmoothGammaContour s a x 0 = 1 := by
    simp [squareSmoothGammaContour,hΓ]
  rw [h0, mul_one] at h
  norm_num only [Complex.ofReal_ofNat] at h
  unfold squareSmoothWeight
  rw [h]
  have hp : (2*Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  field_simp
  simp only [mul_comm I]
  ring

end
end Sechstmoment.Source
