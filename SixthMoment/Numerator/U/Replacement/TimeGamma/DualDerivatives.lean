import SixthMoment.Numerator.U.Replacement.TimeGamma.DualComplex

namespace SixthMoment.Source
open SixthMoment Complex Set Metric Filter
open scoped BigOperators Topology ContDiff ComplexConjugate
noncomputable section
set_option maxHeartbeats 1000000

theorem bblrTimeDualMultiplier_differentiableAt {T R : ℝ} (hR : 0 ≤ R)
    (hL : 1 ≤ Real.log T) (hT : 192*(R+R^2)+8 ≤ T)
    (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖ ≤ R)
    {y : ℂ} (hyre : y.re ∈ Icc (3/4 : ℝ) (9/4)) :
    DifferentiableAt ℂ (bblrTimeDualMultiplier T σ) y := by
  have hL0 : 0 < Real.log T := by linarith
  have hT0 : 0 < T := by nlinarith [sq_nonneg R]
  unfold bblrTimeDualMultiplier
  apply DifferentiableAt.fun_finsetProd
  intro j _
  have hn : ‖σ j/(Real.log T : ℂ)‖ ≤ R := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
    apply (div_le_iff₀ hL0).mpr
    nlinarith [hσ j]
  have hi := abs_le.mp ((Complex.abs_im_le_norm (σ j/(Real.log T : ℂ))).trans hn)
  have hp : (bblrTimeDualBase T y j+σ j/(Real.log T : ℂ)).im ≠ 0 := by
    unfold bblrTimeDualBase
    split_ifs <;> simp only [Complex.add_im,Complex.sub_im,Complex.one_im,
      complexHeightPoint_im]
    · exact ne_of_gt (by nlinarith [hyre.1])
    · exact ne_of_lt (by nlinarith [hyre.1])
  have hd : DifferentiableAt ℂ (fun x => bblrTimeDualBase T x j+σ j/(Real.log T : ℂ)) y := by
    unfold bblrTimeDualBase
    split_ifs <;> unfold complexHeightPoint <;> fun_prop
  exact (zetaChi_analyticAt_nonreal hp).differentiableAt.comp y hd

theorem bblrTimeDualMultiplier_uniform_complex_bound {R : ℝ} (_hR : 0 ≤ R) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts, (∀ j, ‖σ j‖ ≤ R) → ∀ y : ℂ,
      y.re ∈ Icc (3/4 : ℝ) (9/4) → |y.im| ≤ 1/4 →
      ‖bblrTimeDualMultiplier T σ y‖ ≤ 16*Real.exp (4*R) := by
  filter_upwards [centeringFactorAt_uniform_complex_height_bound R,
    lowerCenteringFactor_uniform_complex_height_bound R,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (centeringUniformConstant R))),
    eventually_gt_atTop (0 : ℝ)] with T hupper hlower hlog hT
  intro σ hσ y hyre hyim
  have hL0 : 0 < Real.log T := by linarith [(le_max_left (1 : ℝ) _).trans hlog]
  have hC : centeringUniformConstant R/Real.log T ≤ 1 :=
    (div_le_one hL0).mpr ((le_max_right _ _).trans hlog)
  have hpoint : (complexHeightPoint T y).im ≠ 0 := by
    rw [complexHeightPoint_im]
    exact ne_of_gt (mul_pos hT (by linarith [hyre.1]))
  have hcenter (j : Fin 4) : ‖centeringFactorAt T (bblrTimeDualBase T y j) (σ j)‖ ≤ 2 := by
    have hh : ‖centeringFactorAt T (bblrTimeDualBase T y j) (σ j)-1‖ ≤ 1 := by
      unfold bblrTimeDualBase
      split_ifs
      · exact (hupper y (σ j) hyre hyim (hσ j)).trans hC
      · exact (hlower y (σ j) hyre hyim (hσ j)).trans hC
    have hn := norm_add_le (centeringFactorAt T (bblrTimeDualBase T y j) (σ j)-1) (1 : ℂ)
    rw [sub_add_cancel,norm_one] at hn
    linarith
  have hsum : ‖∑ j : Fin 4, σ j‖ ≤ 4*R := by
    calc
      _ ≤ ∑ j : Fin 4, ‖σ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 4, R := Finset.sum_le_sum (fun j _ => hσ j)
      _ = _ := by simp
  have he : ‖Complex.exp (-∑ j : Fin 4, σ j)‖ ≤ Real.exp (4*R) := by
    rw [Complex.norm_exp,Complex.neg_re]
    exact Real.exp_le_exp.mpr ((neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hsum))
  have hp : ‖∏ j : Fin 4, centeringFactorAt T (bblrTimeDualBase T y j) (σ j)‖ ≤ 16 := by
    calc
      _ ≤ ∏ j : Fin 4, ‖centeringFactorAt T (bblrTimeDualBase T y j) (σ j)‖ :=
        Finset.norm_prod_le _ _
      _ ≤ ∏ _j : Fin 4, (2 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hcenter j)
      _ = _ := by norm_num
  rw [bblrTimeDualMultiplier_centering_eq σ hpoint,norm_mul]
  exact (mul_le_mul he hp (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by ring)

theorem bblrDualMultiplier_normalizedTime_contDiffAt {T R : ℝ} (hR : 0 ≤ R)
    (hL : 1 ≤ Real.log T) (hT : 192*(R+R^2)+8 ≤ T)
    (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖ ≤ R)
    {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    ContDiffAt ℝ ⊤ (fun y : ℝ => bblrDualMultiplier (T*y) (rawMomentShifts T σ)) x := by
  have ha : AnalyticAt ℂ (bblrTimeDualMultiplier T σ) (x : ℂ) := by
    apply DifferentiableOn.analyticAt _
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1/4)))
    intro y hy
    have hw := bblrTimeGamma_closedBall_window hx (ball_subset_closedBall hy)
    exact (bblrTimeDualMultiplier_differentiableAt hR hL hT σ hσ hw.1).differentiableWithinAt
  have hc : ContDiffAt ℝ ⊤ (bblrTimeDualMultiplier T σ) (x : ℂ) := ha.contDiffAt.restrict_scalars ℝ
  have he : (fun y : ℝ => bblrTimeDualMultiplier T σ (y : ℂ)) =
      (fun y : ℝ => bblrDualMultiplier (T*y) (rawMomentShifts T σ)) := by
    funext y
    exact bblrTimeDualMultiplier_ofReal T σ y
  rw [← he]
  exact hc.comp x Complex.ofRealCLM.contDiff.contDiffAt

theorem bblrDualMultiplier_normalizedTime_uniform_derivative_bounds {R : ℝ} (hR : 0 ≤ R) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j, ‖σ j‖ ≤ R) → ∀ x : ℝ, x ∈ Icc (1 : ℝ) 2 → ∀ n : ℕ,
      ‖iteratedDeriv n (fun y : ℝ => bblrDualMultiplier (T*y) (rawMomentShifts T σ)) x‖ ≤ B n := by
  let B : ℕ → ℝ := fun n => ((n.factorial : ℝ)/(1/4 : ℝ)^n)*(16*Real.exp (4*R))
  refine ⟨B,fun n => by dsimp [B]; positivity,?_⟩
  filter_upwards [bblrTimeDualMultiplier_uniform_complex_bound hR,
    eventually_ge_atTop (192*(R+R^2)+8),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with T hbound hT hL
  intro σ hσ x hx n
  have hd : DifferentiableOn ℂ (bblrTimeDualMultiplier T σ) (closedBall (x : ℂ) (1/4 : ℝ)) := by
    intro y hy
    have hw := bblrTimeGamma_closedBall_window hx hy
    exact (bblrTimeDualMultiplier_differentiableAt hR hL hT σ hσ hw.1).differentiableWithinAt
  have hf : DiffContOnCl ℂ (bblrTimeDualMultiplier T σ) (ball (x : ℂ) (1/4 : ℝ)) :=
    (hd.mono closure_ball_subset_closedBall).diffContOnCl
  have hM (y : ℂ) (hy : y ∈ sphere (x : ℂ) (1/4 : ℝ)) :
      ‖bblrTimeDualMultiplier T σ y‖ ≤ 16*Real.exp (4*R) := by
    have hw := bblrTimeGamma_closedBall_window hx (sphere_subset_closedBall hy)
    exact hbound σ hσ y hw.1 hw.2
  have he : (fun y : ℝ => bblrTimeDualMultiplier T σ (y : ℂ)) =
      (fun y : ℝ => bblrDualMultiplier (T*y) (rawMomentShifts T σ)) := by
    funext y
    exact bblrTimeDualMultiplier_ofReal T σ y
  rw [← he]
  exact SixthMoment.cauchy_real_iteratedDeriv_bound n (by norm_num) hf hM

end
end SixthMoment.Source
