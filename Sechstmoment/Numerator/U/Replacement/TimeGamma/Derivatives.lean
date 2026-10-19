import Sechstmoment.Numerator.U.Replacement.TimeGamma.Bounds

namespace Sechstmoment.Source
open Complex Set Metric
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem bblrTimeGammaQuotient_differentiableAt {T A : ℝ}
    (hA : 0 ≤ A) (hT : 8*(A+1) ≤ T)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    {z y : ℂ} (hlarge : 192*(‖z‖+‖z‖^2) < T)
    (hyre : y.re ∈ Icc (3/4 : ℝ) (9/4)) (hyim : |y.im| ≤ 1/4) :
    DifferentiableAt ℂ (bblrTimeGammaQuotient T α z) y := by
  unfold bblrTimeGammaQuotient
  apply DifferentiableAt.fun_finsetProd
  intro j _
  have hg := bblrTimeGammaBase_geometry hA hT α hα hyre hyim j
  have him : (bblrTimeGammaBase T α y j).im ≠ 0 := by
    intro he
    rw [he,abs_zero] at hg
    linarith
  have himz : (bblrTimeGammaBase T α y j+z/2).im ≠ 0 := by
    intro he
    have h : (bblrTimeGammaBase T α y j).im = -z.im/2 := by
      simp only [Complex.add_im,Complex.div_ofNat_im] at he
      linarith
    have hz := Complex.abs_im_le_norm z
    rw [h,abs_div,abs_neg] at hg
    norm_num at hg
    nlinarith [norm_nonneg z,sq_nonneg ‖z‖]
  have hp (n : ℕ) : bblrTimeGammaBase T α y j ≠ -(n : ℂ) := by
    intro he
    apply him
    rw [he]
    simp
  have hpz (n : ℕ) : bblrTimeGammaBase T α y j+z/2 ≠ -(n : ℂ) := by
    intro he
    apply himz
    rw [he]
    simp
  have hd : DifferentiableAt ℂ (fun y => bblrTimeGammaBase T α y j) y := by
    unfold bblrTimeGammaBase
    fun_prop
  have hdz : DifferentiableAt ℂ (fun y => bblrTimeGammaBase T α y j+z/2) y :=
    hd.add_const _
  exact ((Complex.differentiableAt_Gamma _ hpz).comp y hdz).div
    ((Complex.differentiableAt_Gamma _ hp).comp y hd) (Complex.Gamma_ne_zero hp)

theorem bblrTimeGamma_closedBall_window {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2)
    {y : ℂ} (hy : y ∈ closedBall (x : ℂ) (1/4 : ℝ)) :
    y.re ∈ Icc (3/4 : ℝ) (9/4) ∧ |y.im| ≤ 1/4 := by
  have hn : ‖y-(x : ℂ)‖ ≤ 1/4 := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hr := (Complex.abs_re_le_norm (y-(x : ℂ))).trans hn
  have hi := (Complex.abs_im_le_norm (y-(x : ℂ))).trans hn
  simp only [Complex.sub_re,Complex.ofReal_re] at hr
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hi
  exact ⟨⟨by linarith [(abs_le.mp hr).1,hx.1],
    by linarith [(abs_le.mp hr).2,hx.2]⟩,hi⟩

theorem bblrGammaQuotient_normalizedTime_analyticAt {T A : ℝ}
    (hA : 0 ≤ A) (hT : 8*(A+1) ≤ T)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    {z : ℂ} (hlarge : 192*(‖z‖+‖z‖^2) < T)
    {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    AnalyticAt ℂ (bblrTimeGammaQuotient T α z) (x : ℂ) := by
  apply DifferentiableOn.analyticAt _
    (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1/4)))
  intro y hy
  have hw := bblrTimeGamma_closedBall_window hx (ball_subset_closedBall hy)
  exact (bblrTimeGammaQuotient_differentiableAt hA hT α hα hlarge hw.1 hw.2).differentiableWithinAt

theorem bblrGammaQuotient_normalizedTime_contDiffAt {T A : ℝ}
    (hA : 0 ≤ A) (hT : 8*(A+1) ≤ T)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    {z : ℂ} (hlarge : 192*(‖z‖+‖z‖^2) < T)
    {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    ContDiffAt ℝ ⊤ (fun y : ℝ => bblrGammaQuotient (T*y) α z) x := by
  have ha := bblrGammaQuotient_normalizedTime_analyticAt hA hT α hα hlarge hx
  have hc : ContDiffAt ℝ ⊤ (bblrTimeGammaQuotient T α z) (x : ℂ) :=
    ha.contDiffAt.restrict_scalars ℝ
  have he : (fun y : ℝ => bblrTimeGammaQuotient T α z (y : ℂ)) =
      (fun y : ℝ => bblrGammaQuotient (T*y) α z) := by
    funext y
    exact bblrTimeGammaQuotient_ofReal T α z y
  rw [← he]
  exact hc.comp x Complex.ofRealCLM.contDiff.contDiffAt

theorem bblrGammaQuotient_normalizedTime_derivative_bound (n : ℕ) {T A : ℝ}
    (hA : 0 ≤ A) (hT : 8*(A+1) ≤ T)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    {z : ℂ} (hzre : 0 ≤ z.re) (hlarge : 192*(‖z‖+‖z‖^2) < T)
    {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    ‖iteratedDeriv n (fun y : ℝ => bblrGammaQuotient (T*y) α z) x‖ ≤
      ((n.factorial : ℝ)/(1/4 : ℝ)^n)*
        (16*(2*T)^(2*z.re)*Real.exp (2*Real.pi*|z.im|)) := by
  have hd : DifferentiableOn ℂ (bblrTimeGammaQuotient T α z)
      (closedBall (x : ℂ) (1/4 : ℝ)) := by
    intro y hy
    have hw := bblrTimeGamma_closedBall_window hx hy
    exact (bblrTimeGammaQuotient_differentiableAt hA hT α hα hlarge hw.1 hw.2).differentiableWithinAt
  have hf : DiffContOnCl ℂ (bblrTimeGammaQuotient T α z)
      (ball (x : ℂ) (1/4 : ℝ)) :=
    (hd.mono closure_ball_subset_closedBall).diffContOnCl
  have hM (y : ℂ) (hy : y ∈ sphere (x : ℂ) (1/4 : ℝ)) :
      ‖bblrTimeGammaQuotient T α z y‖ ≤
        16*(2*T)^(2*z.re)*Real.exp (2*Real.pi*|z.im|) := by
    have hw := bblrTimeGamma_closedBall_window hx (sphere_subset_closedBall hy)
    exact bblrTimeGammaQuotient_complex_norm_le hA hT α hα hzre hlarge hw.1 hw.2
  have he : (fun y : ℝ => bblrTimeGammaQuotient T α z (y : ℂ)) =
      (fun y : ℝ => bblrGammaQuotient (T*y) α z) := by
    funext y
    exact bblrTimeGammaQuotient_ofReal T α z y
  rw [← he]
  exact Sechstmoment.cauchy_real_iteratedDeriv_bound n (by norm_num) hf hM

end
end Sechstmoment.Source
