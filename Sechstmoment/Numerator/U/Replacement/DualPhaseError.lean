import Sechstmoment.Numerator.U.Replacement.TimeGamma.DualDerivatives
import Sechstmoment.Numerator.U.Replacement.TimeGammaError

namespace Sechstmoment.Source
open Sechstmoment Complex Set Metric Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000

def a03DualRawSum (T : ℝ) (σ : MomentShifts) : ℂ := ∑ j : Fin 4, σ j/(Real.log T : ℂ)

def a03DualBaseLogError (T : ℝ) (y : ℂ) : ℂ :=
  Complex.log (bblrTimeGammaBase T 0 y 0)+Complex.log (bblrTimeGammaBase T 0 y 2)-
    2*Complex.log ((T:ℂ)*y/2)

def a03DualLeadingPhase (T : ℝ) (σ : MomentShifts) (y : ℂ) : ℂ :=
  ((T:ℂ)*y/(2*(Real.pi:ℂ)))^(-a03DualRawSum T σ)

def a03DualGammaRatio (T : ℝ) (σ : MomentShifts) (y : ℂ) (j : Fin 4) : ℂ :=
  normalizedGammaRatio ((1-bblrTimeDualBase T y j)/2) (-(σ j/(Real.log T:ℂ))/2)/
    normalizedGammaRatio (bblrTimeDualBase T y j/2) ((σ j/(Real.log T:ℂ))/2)

private theorem dual_base_gamma_zero (T : ℝ) (y : ℂ) (j : Fin 4) :
    bblrTimeDualBase T y j/2=bblrTimeGammaBase T 0 y j := by
  fin_cases j <;> simp [bblrTimeDualBase,complexHeightPoint,bblrTimeGammaBase,bblrTimeGammaSign] <;> ring

private theorem dual_base_gamma_reflect (T : ℝ) (y : ℂ) (j : Fin 4) :
    (1-bblrTimeDualBase T y j)/2=bblrTimeGammaBase T 0 y (if j.val<2 then 2 else 0) := by
  fin_cases j <;> simp [bblrTimeDualBase,complexHeightPoint,bblrTimeGammaBase,bblrTimeGammaSign] <;> ring

theorem a03DualBaseLogError_norm_le {T : ℝ} (hT : 8≤T)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ} (hy : y∈closedBall (x:ℂ) (1/4:ℝ)) :
    ‖a03DualBaseLogError T y‖≤4/T := by
  have h0 := bblrTimeGammaBase_log_error (by norm_num : (0:ℝ)≤0) (by simpa using hT)
    (0:MomentShifts) (by simp) hx hy (0:Fin 4)
  have h2 := bblrTimeGammaBase_log_error (by norm_num : (0:ℝ)≤0) (by simpa using hT)
    (0:MomentShifts) (by simp) hx hy (2:Fin 4)
  simp [bblrGammaPhaseCenter,Complex.log_I,Complex.log_neg_I] at h0 h2
  have he : a03DualBaseLogError T y =
      (Complex.log (bblrTimeGammaBase T 0 y 0)-Complex.log ((T:ℂ)*y/2)-(Real.pi:ℂ)/2*I)+
      (Complex.log (bblrTimeGammaBase T 0 y 2)-Complex.log ((T:ℂ)*y/2)+(Real.pi:ℂ)/2*I) := by
    unfold a03DualBaseLogError
    ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add h0 h2).trans_eq (by ring))

private theorem dual_elementary_phase_eq {T : ℝ} (hT : 8≤T)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ} (hy : y∈closedBall (x:ℂ) (1/4:ℝ))
    (u z : ℂ) (j : Fin 4) :
    gammaChiMainPhase (bblrTimeDualBase T y j) u z = Complex.exp z*
      Complex.exp (u*(Complex.log (Real.pi:ℂ)-Complex.log ((T:ℂ)*y/2))-
        (u/2)*a03DualBaseLogError T y) := by
  have hw := bblrTimeGamma_closedBall_window hx hy
  have hb (k : Fin 4) : bblrTimeGammaBase T 0 y k≠0 := by
    have hg := bblrTimeGammaBase_geometry (by norm_num : (0:ℝ)≤0) (by simpa using hT)
      (0:MomentShifts) (by simp) hw.1 hw.2 k
    intro he
    simp [he] at hg
    linarith [hg.1]
  unfold gammaChiMainPhase
  rw [dual_base_gamma_zero,dual_base_gamma_reflect,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    Complex.cpow_def_of_ne_zero (hb _),Complex.cpow_def_of_ne_zero (hb _),
    ← Complex.exp_add,← Complex.exp_add]
  simp_rw [← Complex.exp_add]
  congr 1
  unfold a03DualBaseLogError
  fin_cases j <;> norm_num [bblrTimeGammaBase,bblrTimeGammaSign] <;> ring

private theorem dual_raw_norm_le {T R : ℝ} (hR : 0≤R) (hL : 1≤Real.log T)
    (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖≤R) (j : Fin 4) :
    ‖σ j/(Real.log T:ℂ)‖≤R := by
  have hL0 : 0<Real.log T := by linarith
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
  exact (div_le_iff₀ hL0).mpr (by nlinarith [hσ j])

private theorem dual_point_nonreal {T R : ℝ} (hR : 0≤R) (hL : 1≤Real.log T)
    (hT : 192*(R+R^2)+8≤T) (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖≤R)
    {y : ℂ} (hy : y.re∈Icc (3/4:ℝ) (9/4)) (j : Fin 4) :
    (bblrTimeDualBase T y j).im≠0 ∧
    (bblrTimeDualBase T y j+σ j/(Real.log T:ℂ)).im≠0 := by
  have hT0 : 0<T := by nlinarith [sq_nonneg R]
  have hn := dual_raw_norm_le hR hL σ hσ j
  have hi := abs_le.mp ((Complex.abs_im_le_norm _).trans hn)
  unfold bblrTimeDualBase
  split_ifs <;> simp only [Complex.add_im,Complex.sub_im,Complex.one_im,zero_sub,
    complexHeightPoint_im]
  · constructor <;> exact ne_of_gt (by nlinarith [hy.1])
  · constructor <;> exact ne_of_lt (by nlinarith [hy.1])

theorem a03DualMultiplier_phase_gamma_eq {T R : ℝ} (hR : 0≤R) (hL : 1≤Real.log T)
    (hT : 192*(R+R^2)+8≤T) (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖≤R)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ} (hy : y∈closedBall (x:ℂ) (1/4:ℝ)) :
    bblrTimeDualMultiplier T σ y =
      a03DualLeadingPhase T σ y*
        Complex.exp (-(a03DualRawSum T σ/2)*a03DualBaseLogError T y)*
          ∏ j : Fin 4, a03DualGammaRatio T σ y j := by
  have hT8 : 8≤T := by nlinarith [sq_nonneg R]
  have hT0 : 0<T := by linarith
  have hw := bblrTimeGamma_closedBall_window hx hy
  have hpoint : (complexHeightPoint T y).im≠0 := by
    rw [complexHeightPoint_im]
    exact ne_of_gt (by nlinarith [hw.1.1])
  rw [bblrTimeDualMultiplier_centering_eq σ hpoint]
  have he (j : Fin 4) : centeringFactorAt T (bblrTimeDualBase T y j) (σ j) =
      Complex.exp (σ j)*Complex.exp
        ((σ j/(Real.log T:ℂ))*(Complex.log (Real.pi:ℂ)-Complex.log ((T:ℂ)*y/2))-
          ((σ j/(Real.log T:ℂ))/2)*a03DualBaseLogError T y)*a03DualGammaRatio T σ y j := by
    have hp := dual_point_nonreal hR hL hT σ hσ hw.1 j
    rw [centeringFactorAt_eq_gamma_ratios T _ _ hp.1 hp.2,
      dual_elementary_phase_eq hT8 hx hy]
    rfl
  simp_rw [he]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,← Complex.exp_sum,← Complex.exp_sum,
    ← mul_assoc,← mul_assoc,← Complex.exp_add]
  simp only [neg_add_cancel,Complex.exp_zero,one_mul]
  have hyn : y≠0 := by intro he; rw [he] at hw; norm_num at hw
  have hp0 : (T:ℂ)*y/2≠0 := div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hT0.ne') hyn) (by norm_num)
  have hlead0 : (T:ℂ)*y/(2*(Real.pi:ℂ))≠0 := div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hT0.ne') hyn)
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hlog : Complex.log ((T:ℂ)*y/(2*(Real.pi:ℂ)))=
      Complex.log ((T:ℂ)*y/2)-Complex.log (Real.pi:ℂ) := by
    have hreal : (0:ℝ)<1/Real.pi := by positivity
    have he : (T:ℂ)*y/(2*(Real.pi:ℂ))=(1/Real.pi:ℝ)*((T:ℂ)*y/2) := by
      push_cast
      ring
    rw [he,Complex.log_ofReal_mul hreal hp0]
    have hl := Complex.ofReal_log (by positivity : (0:ℝ)≤Real.pi)
    rw [Real.log_div one_ne_zero Real.pi_ne_zero,Real.log_one]
    push_cast
    rw [hl]
    ring
  unfold a03DualLeadingPhase
  rw [Complex.cpow_def_of_ne_zero hlead0,hlog,← Complex.exp_add]
  congr 2
  unfold a03DualRawSum
  simp only [Fin.sum_univ_succ,Fin.isValue]
  ring

theorem a03DualGammaRatio_error_le {T R : ℝ} (hR : 0≤R) (hL : 1≤Real.log T)
    (hT : 192*(R+R^2)+8≤T) (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖≤R)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ} (hy : y∈closedBall (x:ℂ) (1/4:ℝ))
    (j : Fin 4) : ‖a03DualGammaRatio T σ y j-1‖≤192*(R+R^2)/T := by
  have hT8 : 8≤T := by nlinarith [sq_nonneg R]
  have hT0 : 0<T := by linarith
  let u := σ j/(Real.log T:ℂ)
  have hu : ‖u‖≤R := dual_raw_norm_le hR hL σ hσ j
  have hus : ‖u‖+‖u‖^2≤R+R^2 := by nlinarith [norm_nonneg u]
  have hz : 48*(‖u‖+‖u‖^2)<T := by nlinarith [sq_nonneg R]
  have hn (k : Fin 4) : ‖normalizedGammaRatio (bblrTimeGammaBase T 0 y k) (u/2)-1‖≤
      48*(R+R^2)/T := by
    have h := bblrTimeNormalizedGammaFactor_error_le (by norm_num : (0:ℝ)≤0)
      (by simpa using hT8) (0:MomentShifts) (by simp) hx hy u hz k
    change ‖normalizedGammaRatio (bblrTimeGammaBase T 0 y k) (u/2)-1‖≤_ at h
    exact h.trans (div_le_div_of_nonneg_right (by nlinarith) hT0.le)
  have hneg (k : Fin 4) : ‖normalizedGammaRatio (bblrTimeGammaBase T 0 y k) (-u/2)-1‖≤
      48*(R+R^2)/T := by
    have hz' : 48*(‖-u‖+‖-u‖^2)<T := by simpa using hz
    have h := bblrTimeNormalizedGammaFactor_error_le (by norm_num : (0:ℝ)≤0)
      (by simpa using hT8) (0:MomentShifts) (by simp) hx hy (-u) hz' k
    change ‖normalizedGammaRatio (bblrTimeGammaBase T 0 y k) (-u/2)-1‖≤_ at h
    rw [norm_neg] at h
    exact h.trans (div_le_div_of_nonneg_right (by nlinarith) hT0.le)
  unfold a03DualGammaRatio
  rw [dual_base_gamma_zero,dual_base_gamma_reflect]
  have hδ0 : 0≤48*(R+R^2)/T := by positivity
  have hδ1 : 48*(R+R^2)/T≤1/2 := (div_le_iff₀ hT0).mpr (by nlinarith [sq_nonneg R])
  exact (norm_div_sub_one_le_four hδ0 hδ1 (hneg _) (hn _)).trans_eq (by ring)

theorem a03DualMultiplier_normalized_error_le {T R : ℝ} (hR : 0≤R) (hL : 1≤Real.log T)
    (hT : 192*(R+R^2)+8≤T) (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖≤R)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ} (hy : y∈closedBall (x:ℂ) (1/4:ℝ)) :
    ‖bblrTimeDualMultiplier T σ y/a03DualLeadingPhase T σ y-1‖≤
      (5760*(R+R^2)+16*R)/T := by
  have hT8 : 8≤T := by nlinarith [sq_nonneg R]
  have hT0 : 0<T := by linarith
  have hs : ‖a03DualRawSum T σ‖≤4*R := by
    unfold a03DualRawSum
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => dual_raw_norm_le hR hL σ hσ j)).trans_eq (by simp))
  have hp : ‖-(a03DualRawSum T σ/2)*a03DualBaseLogError T y‖≤8*R/T := by
    rw [norm_mul,norm_neg,norm_div]
    norm_num
    calc
      _≤(4*R)/2*(4/T) := by gcongr; exact a03DualBaseLogError_norm_le hT8 hx hy
      _=_ := by ring
  have hp1 : ‖-(a03DualRawSum T σ/2)*a03DualBaseLogError T y‖≤1 :=
    hp.trans ((div_le_iff₀ hT0).mpr (by nlinarith [sq_nonneg R]))
  have hf : ‖Complex.exp (-(a03DualRawSum T σ/2)*a03DualBaseLogError T y)-1‖≤16*R/T :=
    (Complex.norm_exp_sub_one_le hp1).trans (by calc
      _≤2*(8*R/T) := by gcongr
      _=_ := by ring)
  have hfn : ‖Complex.exp (-(a03DualRawSum T σ/2)*a03DualBaseLogError T y)‖≤2 := by
    have hh := norm_add_le (Complex.exp (-(a03DualRawSum T σ/2)*a03DualBaseLogError T y)-1) (1:ℂ)
    simp only [sub_add_cancel,norm_one] at hh
    have hn : 16*R/T≤1 := (div_le_iff₀ hT0).mpr (by nlinarith [sq_nonneg R])
    linarith
  let E := 192*(R+R^2)/T
  have hE0 : 0≤E := by dsimp [E]; positivity
  have hE1 : E≤1 := by dsimp [E]; exact (div_le_iff₀ hT0).mpr (by linarith)
  have hr := fourfold_product_error_le (a03DualGammaRatio T σ y) hE0 hE1
    (a03DualGammaRatio_error_le hR hL hT σ hσ hx hy)
  have hw := bblrTimeGamma_closedBall_window hx hy
  have hy0 : y≠0 := by intro he; rw [he] at hw; norm_num at hw
  have hb0 : (T:ℂ)*y/(2*(Real.pi:ℂ))≠0 := div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hT0.ne') hy0)
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hlead : a03DualLeadingPhase T σ y≠0 := by simp [a03DualLeadingPhase,hb0]
  rw [a03DualMultiplier_phase_gamma_eq hR hL hT σ hσ hx hy]
  rw [mul_assoc,mul_div_cancel_left₀ _ hlead]
  let f := Complex.exp (-(a03DualRawSum T σ/2)*a03DualBaseLogError T y)
  let r := ∏ j : Fin 4, a03DualGammaRatio T σ y j
  change ‖f*r-1‖≤_
  rw [show f*r-1=f*(r-1)+(f-1) by ring]
  calc
    _≤‖f*(r-1)‖+‖f-1‖ := norm_add_le _ _
    _≤2*(15*E)+16*R/T := by rw [norm_mul]; gcongr
    _=_ := by dsimp [E]; ring

private theorem close_quotient_absolute_error {a b : ℂ} (hb : b≠0) {D δ : ℝ}
    (hδ0 : 0≤δ) (hδ1 : δ≤1/2) (ha : ‖a‖≤D) (hr : ‖a/b-1‖≤δ) :
    ‖a-b‖≤2*D*δ := by
  have he : a-b=b*(a/b-1) := by field_simp
  have hd : ‖a-b‖≤‖b‖*δ := by rw [he,norm_mul]; gcongr
  have hn : ‖b‖≤‖a-b‖+‖a‖ := by
    have h := norm_add_le (b-a) a
    simpa only [sub_add_cancel,norm_sub_rev] using h
  have hbD : ‖b‖≤2*D := by nlinarith [norm_nonneg b]
  exact hd.trans (mul_le_mul_of_nonneg_right hbD hδ0)

def a03DualPhaseErrorConstant (R : ℝ) : ℝ := 5760*(R+R^2)+16*R

def a03DualPhaseReplacementError (T : ℝ) (σ : MomentShifts) (y : ℂ) : ℂ :=
  bblrTimeDualMultiplier T σ y-a03DualLeadingPhase T σ y

theorem a03DualPhaseReplacementError_uniform_complex_bound {R : ℝ} (hR : 0≤R) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
      ∀ x : ℝ, x∈Icc (1:ℝ) 2 → ∀ y : ℂ, y∈closedBall (x:ℂ) (1/4:ℝ) →
      ‖a03DualPhaseReplacementError T σ y‖≤
        (32*Real.exp (4*R)*a03DualPhaseErrorConstant R)/T := by
  filter_upwards [bblrTimeDualMultiplier_uniform_complex_bound hR,
    eventually_ge_atTop (192*(R+R^2)+8),
    eventually_ge_atTop (2*a03DualPhaseErrorConstant R+8),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
      with T hb hT hC hL
  intro σ hσ x hx y hy
  have hT0 : 0<T := by nlinarith [sq_nonneg R]
  have hw := bblrTimeGamma_closedBall_window hx hy
  have hy0 : y≠0 := by intro he; rw [he] at hw; norm_num at hw
  have hb0 : (T:ℂ)*y/(2*(Real.pi:ℂ))≠0 := div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hT0.ne') hy0)
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hlead : a03DualLeadingPhase T σ y≠0 := by simp [a03DualLeadingPhase,hb0]
  have hδ0 : 0≤a03DualPhaseErrorConstant R/T := by unfold a03DualPhaseErrorConstant; positivity
  have hδ1 : a03DualPhaseErrorConstant R/T≤1/2 := (div_le_iff₀ hT0).mpr (by linarith)
  have h := close_quotient_absolute_error hlead hδ0 hδ1 (hb σ hσ y hw.1 hw.2)
    (a03DualMultiplier_normalized_error_le hR hL hT σ hσ hx hy)
  exact h.trans_eq (by ring)

theorem a03DualLeadingPhase_ofReal (T : ℝ) (σ : MomentShifts) (y : ℝ) :
    a03DualLeadingPhase T σ (y:ℂ)=
      (T*y/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j) := by
  unfold a03DualLeadingPhase a03DualRawSum rawMomentShifts
  rfl

private theorem dual_leading_differentiableAt {T : ℝ} (hT : 0<T)
    (σ : MomentShifts) {y : ℂ} (hy : 0<y.re) :
    DifferentiableAt ℂ (a03DualLeadingPhase T σ) y := by
  unfold a03DualLeadingPhase
  apply DifferentiableAt.cpow_const
  · fun_prop
  · apply Complex.mem_slitPlane_iff.mpr
    left
    simp [Complex.div_re,Complex.mul_re,Complex.mul_im]
    positivity

theorem a03DualPhaseReplacementError_normalizedTime_uniform_derivative_bounds
    {R : ℝ} (hR : 0≤R) :
    ∃ B : ℕ→ℝ, (∀ n, 0≤B n) ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) → ∀ x : ℝ, x∈Icc (1:ℝ) 2 → ∀ n : ℕ,
      ‖iteratedDeriv n (fun y : ℝ => bblrDualMultiplier (T*y) (rawMomentShifts T σ)-
        (T*y/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j)) x‖≤B n/T := by
  let C := 32*Real.exp (4*R)*a03DualPhaseErrorConstant R
  let B : ℕ→ℝ := fun n => ((n.factorial:ℝ)/(1/4:ℝ)^n)*C
  refine ⟨B,fun n => by dsimp [B,C,a03DualPhaseErrorConstant]; positivity,?_⟩
  filter_upwards [a03DualPhaseReplacementError_uniform_complex_bound hR,
    eventually_ge_atTop (192*(R+R^2)+8),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
      with T hb hT hL
  intro σ hσ x hx n
  have hT0 : 0<T := by nlinarith [sq_nonneg R]
  have hd : DifferentiableOn ℂ (a03DualPhaseReplacementError T σ) (closedBall (x:ℂ) (1/4:ℝ)) := by
    intro y hy
    have hw := bblrTimeGamma_closedBall_window hx hy
    exact ((bblrTimeDualMultiplier_differentiableAt hR hL hT σ hσ hw.1).sub
      (dual_leading_differentiableAt hT0 σ (by linarith [hw.1.1]))).differentiableWithinAt
  have hf : DiffContOnCl ℂ (a03DualPhaseReplacementError T σ) (ball (x:ℂ) (1/4:ℝ)) :=
    (hd.mono closure_ball_subset_closedBall).diffContOnCl
  have hM (y : ℂ) (hy : y∈sphere (x:ℂ) (1/4:ℝ)) :
      ‖a03DualPhaseReplacementError T σ y‖≤C/T :=
    hb σ hσ x hx y (sphere_subset_closedBall hy)
  have he : (fun y : ℝ => a03DualPhaseReplacementError T σ (y:ℂ))=
      (fun y : ℝ => bblrDualMultiplier (T*y) (rawMomentShifts T σ)-
        (T*y/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j)) := by
    funext y
    unfold a03DualPhaseReplacementError
    rw [bblrTimeDualMultiplier_ofReal,a03DualLeadingPhase_ofReal]
  rw [← he]
  have h := Sechstmoment.cauchy_real_iteratedDeriv_bound n (by norm_num : (0:ℝ)<1/4) hf hM
  exact h.trans_eq (by dsimp [B]; ring)

end
end Sechstmoment.Source
