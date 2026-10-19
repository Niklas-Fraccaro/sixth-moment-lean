import Sechstmoment.Analysis.Mellin.VerticalShift
import Sechstmoment.Zeta.DirichletL.Weights.Definitions

/-! The smooth-square Gamma weight can be evaluated on every positive
vertical line. All contour, boundary and convergence conditions are proved.
-/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

theorem squareSmoothGammaContour_div_differentiableAt (s : ℂ) (a : ℕ) (x : ℝ)
    (hs : 0 < s.re) (hx : 0 < x) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (fun z : ℂ => squareSmoothGammaContour s a x z/z) w := by
  have harg : 0 < ((s+(a : ℂ)+w)/2).re := by
    simp only [Complex.div_ofNat_re, add_re, natCast_re]
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  have hΓ : DifferentiableAt ℂ Complex.Gamma ((s+(a : ℂ)+w)/2) := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have h := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at h
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hΓcomp : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma ((s+(a : ℂ)+z)/2)) w :=
    DifferentiableAt.comp (f := fun z : ℂ => (s+(a : ℂ)+z)/2) (g := Complex.Gamma)
      w hΓ (by fun_prop)
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hp : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ)^(-z)) w :=
    (differentiable_neg.const_cpow (Or.inl hxne)).differentiableAt
  have hwne : w ≠ 0 := by intro h; simp [h] at hw
  unfold squareSmoothGammaContour
  exact (((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (z^2)) w).mul
    ((hΓcomp.div_const _).pow 2)).mul hp).div (by fun_prop) hwne

theorem squareSmoothGammaContour_div_strip_bound (s : ℂ) (a : ℕ) (x u v : ℝ)
    (hs : 0 < s.re) (hx : 0 < x) (hu : 0 < u) (huv : u ≤ v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, u ≤ w.re → w.re ≤ v →
      ‖squareSmoothGammaContour s a x w/w‖ ≤ C*Real.exp (-w.im^2) := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  obtain ⟨B,hB,hbound⟩ := realGamma_norm_bounded_on_positive_interval
    (a := (s.re+(a : ℝ)+u)/2) (b := (s.re+(a : ℝ)+v)/2) (by linarith)
  let D := ‖Complex.Gamma ((s+(a : ℂ))/2)‖
  let P := x^(-u)+x^(-v)
  refine ⟨Real.exp (v^2)*(B/D)^2*P/u, by dsimp [P]; positivity, ?_⟩
  intro w hwu hwv
  have hΓ : ‖Complex.Gamma ((s+(a : ℂ)+w)/2)‖ ≤ B := by
    apply (gamma_norm_le_realGamma_re (s := (s+(a : ℂ)+w)/2) ?_).trans
    · apply hbound
      simp only [Complex.div_ofNat_re, add_re, natCast_re]
      constructor <;> linarith
    · simp only [Complex.div_ofNat_re, add_re, natCast_re]
      linarith
  have he : ‖Complex.exp (w^2)‖ ≤ Real.exp (v^2)*Real.exp (-w.im^2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc : w.re^2 ≤ v^2 := by nlinarith
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
  have hden : u ≤ ‖w‖ := hwu.trans (Complex.re_le_norm w)
  rw [norm_div, squareSmoothGammaContour, norm_mul, norm_mul, norm_pow, norm_div]
  calc
    _ ≤ ((Real.exp (v^2)*Real.exp (-w.im^2))*(B/D)^2*P)/u := by
      dsimp only [D]
      gcongr
    _ = _ := by dsimp only [D]; ring

theorem squareSmoothGammaContour_positive_lines_eq (s : ℂ) (a : ℕ) (x : ℝ)
    (hs : 0 < s.re) (hx : 0 < x) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (∫ y : ℝ, squareSmoothGammaContour s a x ((v : ℂ)+(y : ℂ)*I)/((v : ℂ)+(y : ℂ)*I)) =
      ∫ y : ℝ, squareSmoothGammaContour s a x ((u : ℂ)+(y : ℂ)*I)/((u : ℂ)+(y : ℂ)*I) := by
  let F : ℂ → ℂ := fun w => squareSmoothGammaContour s a x w/w
  obtain ⟨C,_,hbound⟩ := squareSmoothGammaContour_div_strip_bound s a x u v hs hx hu huv
  have hF (w : ℂ) (hwu : u ≤ w.re) (_ : w.re ≤ v) : DifferentiableAt ℂ F w :=
    squareSmoothGammaContour_div_differentiableAt s a x hs hx (hu.trans_le hwu)
  have hcont (c : ℝ) (hc : c ∈ Icc u v) : Continuous (fun y : ℝ => F ((c : ℂ)+(y : ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact ContinuousAt.comp (f := fun y : ℝ => (c : ℂ)+(y : ℂ)*I) (g := F)
      (hF _ (by simpa using hc.1) (by simpa using hc.2)).continuousAt (by fun_prop)
  have hint (c : ℝ) (hc : c ∈ Icc u v) : Integrable (fun y : ℝ => F ((c : ℂ)+(y : ℂ)*I)) := by
    apply vertical_integrable_of_gaussian_bound F c C (hcont c hc)
    intro y
    simpa [F] using hbound ((c : ℂ)+(y : ℂ)*I) (by simpa using hc.1) (by simpa using hc.2)
  exact vertical_integrals_eq_of_holomorphic F huv hF
    (hint u ⟨le_rfl,huv⟩) (hint v ⟨huv,le_rfl⟩)
    (horizontal_tendsto_zero_of_gaussian_strip_bound F huv hbound)

theorem squareSmoothWeight_eq_vertical_integral (s : ℂ) (a : ℕ) (x c : ℝ)
    (hs : 0 < s.re) (hx : 0 < x) (hc : 0 < c) :
    squareSmoothWeight s a x =
      (∫ y : ℝ, squareSmoothGammaContour s a x ((c : ℂ)+(y : ℂ)*I)/((c : ℂ)+(y : ℂ)*I))/
        (2*Real.pi : ℂ) := by
  unfold squareSmoothWeight
  congr 1
  rcases le_total c 2 with hc2 | hc2
  · simpa using squareSmoothGammaContour_positive_lines_eq s a x hs hx hc hc2
  · exact (squareSmoothGammaContour_positive_lines_eq s a x hs hx (by norm_num) hc2).symm

end
end Sechstmoment.Source
