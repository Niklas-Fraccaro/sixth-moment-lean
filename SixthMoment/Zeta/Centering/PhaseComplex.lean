import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.Positivity
import SixthMoment.Zeta.Centering.Elementary
import SixthMoment.Zeta.Centering.Stirling


namespace SixthMoment

open Filter Metric Asymptotics

noncomputable section

def complexHeightPoint (T : ℝ) (x : ℂ) : ℂ := (1 / 2 : ℂ) + (T : ℂ) * x * Complex.I

def gammaHeightA (T : ℝ) (x : ℂ) : ℂ := (1 - complexHeightPoint T x) / 2

def gammaHeightB (T : ℝ) (x : ℂ) : ℂ := complexHeightPoint T x / 2

def centeringGammaMain (T : ℝ) (x z : ℂ) : ℂ :=
  Complex.exp z * (Real.pi : ℂ) ^ (z / (Real.log T : ℂ)) *
    gammaHeightA T x ^ (-z / (2 * (Real.log T : ℂ))) *
    gammaHeightB T x ^ (-z / (2 * (Real.log T : ℂ)))

theorem centeringGammaMain_eq_gammaChiMainPhase (T : ℝ) (x z : ℂ) :
    centeringGammaMain T x z =
      gammaChiMainPhase (complexHeightPoint T x) (z / (Real.log T : ℂ)) z := by
  unfold centeringGammaMain gammaChiMainPhase gammaHeightA gammaHeightB
  have heq : -z / (2 * (Real.log T : ℂ)) = -(z / (Real.log T : ℂ)) / 2 := by ring
  rw [heq]

def centeringPhaseComplexBound : ℝ := |Real.log Real.pi| + Real.log 4 + Real.pi

def centeringGammaMainCoefficient (T : ℝ) (x : ℂ) : ℂ :=
  (Real.log Real.pi : ℂ) -
    (Complex.log (gammaHeightA T x / (T : ℂ)) +
      Complex.log (gammaHeightB T x / (T : ℂ))) / 2

theorem complexHeightPoint_re (T : ℝ) (x : ℂ) :
    (complexHeightPoint T x).re = 1 / 2 - T * x.im := by
  simp [complexHeightPoint, Complex.mul_re]
  ring

theorem complexHeightPoint_im (T : ℝ) (x : ℂ) :
    (complexHeightPoint T x).im = T * x.re := by
  simp [complexHeightPoint, Complex.mul_im]

theorem gammaReal_ne_zero_nonreal {s : ℂ} (hs : s.im ≠ 0) : Complex.Gammaℝ s ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  apply hs
  simpa using congrArg Complex.im hn

theorem gammaReal_differentiableAt_nonreal {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  unfold Complex.Gammaℝ
  apply DifferentiableAt.mul
  · exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · apply (Complex.differentiableAt_Gamma (s / 2) ?_).comp s
      (differentiableAt_id.div_const (2 : ℂ))
    intro n hn
    apply hs
    have h := congrArg Complex.im hn
    simp only [Complex.div_ofNat_im, Complex.neg_im, Complex.natCast_im, neg_zero] at h
    exact (div_eq_zero_iff).mp h |>.resolve_right (by norm_num)

theorem gammaReal_analyticOnNhd_nonreal :
    AnalyticOnNhd ℂ Complex.Gammaℝ {s : ℂ | s.im ≠ 0} := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_ne_fun Complex.continuous_im continuous_const)
  intro s hs
  exact (gammaReal_differentiableAt_nonreal hs).differentiableWithinAt

theorem gammaReal_analyticAt_nonreal {s : ℂ} (hs : s.im ≠ 0) :
    AnalyticAt ℂ Complex.Gammaℝ s := gammaReal_analyticOnNhd_nonreal s hs

theorem zetaChi_ne_zero_nonreal {s : ℂ} (hs : s.im ≠ 0) : zetaChi s ≠ 0 := by
  unfold zetaChi
  exact div_ne_zero (gammaReal_ne_zero_nonreal (by simpa using hs))
    (gammaReal_ne_zero_nonreal hs)

theorem zetaChi_analyticOnNhd_nonreal :
    AnalyticOnNhd ℂ zetaChi {s : ℂ | s.im ≠ 0} := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_ne_fun Complex.continuous_im continuous_const)
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  unfold zetaChi
  apply DifferentiableAt.div
  · exact (gammaReal_differentiableAt_nonreal (by simpa using hs)).comp s (by fun_prop)
  · exact gammaReal_differentiableAt_nonreal hs
  · exact gammaReal_ne_zero_nonreal hs

theorem zetaChi_analyticAt_nonreal {s : ℂ} (hs : s.im ≠ 0) :
    AnalyticAt ℂ zetaChi s := zetaChi_analyticOnNhd_nonreal s hs

theorem centeringFactorAt_analyticAt_base (T : ℝ) (z : ℂ) {s : ℂ}
    (hs : s.im ≠ 0) (hw : (s + z / (Real.log T : ℂ)).im ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ => centeringFactorAt T w z) s := by
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + z / (Real.log T : ℂ)) s := by fun_prop
  have hnum : AnalyticAt ℂ (fun w : ℂ => zetaChi (w + z / (Real.log T : ℂ))) s :=
    (zetaChi_analyticAt_nonreal hw).comp (f := fun w : ℂ => w + z / (Real.log T : ℂ)) hshift
  exact ((analyticAt_const.mul hnum).div
    (zetaChi_analyticAt_nonreal hs) (zetaChi_ne_zero_nonreal hs))

theorem centeringFactorAt_analyticAt_height (T : ℝ) (z : ℂ) {x : ℂ}
    (hs : (complexHeightPoint T x).im ≠ 0)
    (hw : (complexHeightPoint T x + z / (Real.log T : ℂ)).im ≠ 0) :
    AnalyticAt ℂ (fun y : ℂ => centeringFactorAt T (complexHeightPoint T y) z) x := by
  have hheight : AnalyticAt ℂ (complexHeightPoint T) x := by
    unfold complexHeightPoint
    fun_prop
  exact (centeringFactorAt_analyticAt_base T z hs hw).comp hheight

theorem centeringFactorAt_error_analyticAt_height (T : ℝ) (z : ℂ) {x : ℂ}
    (hs : (complexHeightPoint T x).im ≠ 0)
    (hw : (complexHeightPoint T x + z / (Real.log T : ℂ)).im ≠ 0) :
    AnalyticAt ℂ (fun y : ℂ => centeringFactorAt T (complexHeightPoint T y) z - 1) x :=
  (centeringFactorAt_analyticAt_height T z hs hw).sub analyticAt_const

theorem centeringFactorAt_analyticAt_shift (T : ℝ) (s : ℂ) {z : ℂ}
    (hw : (s + z / (Real.log T : ℂ)).im ≠ 0) :
    AnalyticAt ℂ (centeringFactorAt T s) z := by
  have hshift : AnalyticAt ℂ (fun w : ℂ => s + w / (Real.log T : ℂ)) z := by fun_prop
  exact (analyticAt_cexp.mul ((zetaChi_analyticAt_nonreal hw).comp
    (f := fun w : ℂ => s + w / (Real.log T : ℂ)) hshift)).div_const

theorem gammaHeightA_re (T : ℝ) (x : ℂ) :
    (gammaHeightA T x).re = 1 / 4 + T * x.im / 2 := by
  simp [gammaHeightA, complexHeightPoint, Complex.mul_re]
  ring

theorem gammaHeightA_im (T : ℝ) (x : ℂ) :
    (gammaHeightA T x).im = -(T * x.re / 2) := by
  simp [gammaHeightA, complexHeightPoint, Complex.mul_im]
  ring

theorem gammaHeightB_re (T : ℝ) (x : ℂ) :
    (gammaHeightB T x).re = 1 / 4 - T * x.im / 2 := by
  simp [gammaHeightB, complexHeightPoint, Complex.mul_re]
  ring

theorem gammaHeightB_im (T : ℝ) (x : ℂ) :
    (gammaHeightB T x).im = T * x.re / 2 := by
  simp [gammaHeightB, complexHeightPoint, Complex.mul_im]

theorem gammaHeightA_div_T_re {T : ℝ} (x : ℂ) (hT : T ≠ 0) :
    (gammaHeightA T x / (T : ℂ)).re = 1 / (4 * T) + x.im / 2 := by
  rw [Complex.div_ofReal_re, gammaHeightA_re]
  field_simp

theorem gammaHeightA_div_T_im {T : ℝ} (x : ℂ) (hT : T ≠ 0) :
    (gammaHeightA T x / (T : ℂ)).im = -x.re / 2 := by
  rw [Complex.div_ofReal_im, gammaHeightA_im]
  field_simp

theorem gammaHeightB_div_T_re {T : ℝ} (x : ℂ) (hT : T ≠ 0) :
    (gammaHeightB T x / (T : ℂ)).re = 1 / (4 * T) - x.im / 2 := by
  rw [Complex.div_ofReal_re, gammaHeightB_re]
  field_simp

theorem gammaHeightB_div_T_im {T : ℝ} (x : ℂ) (hT : T ≠ 0) :
    (gammaHeightB T x / (T : ℂ)).im = x.re / 2 := by
  rw [Complex.div_ofReal_im, gammaHeightB_im]
  field_simp

theorem gammaHeight_normalized_norm_bounds {T : ℝ} {x : ℂ} (hT : 1 ≤ T)
    (hxre : x.re ∈ Set.Icc (3 / 4 : ℝ) (9 / 4)) (hxim : |x.im| ≤ 1 / 4) :
    (1 / 4 ≤ ‖gammaHeightA T x / (T : ℂ)‖ ∧ ‖gammaHeightA T x / (T : ℂ)‖ ≤ 2) ∧
    (1 / 4 ≤ ‖gammaHeightB T x / (T : ℂ)‖ ∧ ‖gammaHeightB T x / (T : ℂ)‖ ≤ 2) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hscale : 0 ≤ 1 / (4 * T) ∧ 1 / (4 * T) ≤ 1 / 4 := by
    constructor
    · positivity
    · exact (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by linarith)
  have hx0 : 0 ≤ x.re := by linarith [hxre.1]
  have hxabs : |x.re| = x.re := abs_of_nonneg hx0
  have hhalfim : |x.im / 2| ≤ 1 / 8 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hreA : |(gammaHeightA T x / (T : ℂ)).re| ≤ 3 / 8 := by
    rw [gammaHeightA_div_T_re x hT0.ne']
    exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hscale.1]; linarith)
  have hreB : |(gammaHeightB T x / (T : ℂ)).re| ≤ 3 / 8 := by
    rw [gammaHeightB_div_T_re x hT0.ne']
    have h := abs_sub_le (1 / (4 * T)) 0 (x.im / 2)
    simp only [sub_zero, zero_sub, abs_neg] at h
    exact h.trans (by rw [abs_of_nonneg hscale.1]; linarith)
  have himA : |(gammaHeightA T x / (T : ℂ)).im| = x.re / 2 := by
    rw [gammaHeightA_div_T_im x hT0.ne', abs_div, abs_neg, hxabs]
    norm_num
  have himB : |(gammaHeightB T x / (T : ℂ)).im| = x.re / 2 := by
    rw [gammaHeightB_div_T_im x hT0.ne', abs_div, hxabs]
    norm_num
  constructor
  · constructor
    · have h := Complex.abs_im_le_norm (gammaHeightA T x / (T : ℂ))
      rw [himA] at h
      linarith [hxre.1]
    · have h := Complex.norm_le_abs_re_add_abs_im (gammaHeightA T x / (T : ℂ))
      rw [himA] at h
      linarith [hxre.2]
  · constructor
    · have h := Complex.abs_im_le_norm (gammaHeightB T x / (T : ℂ))
      rw [himB] at h
      linarith [hxre.1]
    · have h := Complex.norm_le_abs_re_add_abs_im (gammaHeightB T x / (T : ℂ))
      rw [himB] at h
      linarith [hxre.2]

theorem gammaHeight_im_ne_zero {T : ℝ} {x : ℂ} (hT : 0 < T)
    (hxre : 0 < x.re) : (gammaHeightA T x).im ≠ 0 ∧ (gammaHeightB T x).im ≠ 0 := by
  rw [gammaHeightA_im, gammaHeightB_im]
  have h : 0 < T * x.re / 2 := by positivity
  exact ⟨neg_ne_zero.mpr h.ne', h.ne'⟩

theorem centeringGammaMain_analyticOnNhd_height {T : ℝ} (hT : 0 < T) (z : ℂ) :
    AnalyticOnNhd ℂ (fun x : ℂ => centeringGammaMain T x z) {x : ℂ | 0 < x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro x hx
  have hnz := gammaHeight_im_ne_zero hT hx
  have hA : gammaHeightA T x ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr hnz.1)
  have hB : gammaHeightB T x ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr hnz.2)
  have hdA : DifferentiableAt ℂ (gammaHeightA T) x := by
    unfold gammaHeightA complexHeightPoint
    fun_prop
  have hdB : DifferentiableAt ℂ (gammaHeightB T) x := by
    unfold gammaHeightB complexHeightPoint
    fun_prop
  exact (((differentiableAt_const
    (Complex.exp z * (Real.pi : ℂ) ^ (z / (Real.log T : ℂ)))).mul
      (hdA.cpow_const hA)).mul (hdB.cpow_const hB)).differentiableWithinAt

theorem centeringGammaMain_analyticAt_height {T : ℝ} {x : ℂ} (z : ℂ)
    (hT : 0 < T) (hx : 0 < x.re) :
    AnalyticAt ℂ (fun y : ℂ => centeringGammaMain T y z) x :=
  centeringGammaMain_analyticOnNhd_height hT z x hx

theorem gammaHeight_im_abs_lower {T : ℝ} {x : ℂ} (hT : 0 ≤ T)
    (hxre : 3 / 4 ≤ x.re) :
    3 * T / 8 ≤ |(gammaHeightA T x).im| ∧
      3 * T / 8 ≤ |(gammaHeightB T x).im| := by
  rw [gammaHeightA_im, gammaHeightB_im, abs_neg]
  have hpos : 0 ≤ T * x.re / 2 := by positivity
  rw [abs_of_nonneg hpos]
  have hprod := mul_le_mul_of_nonneg_left hxre hT
  constructor <;> nlinarith

theorem gammaHeight_mem_cone {T : ℝ} {x : ℂ} (hT : 0 ≤ T)
    (hxre : 3 / 4 ≤ x.re) (hxim : |x.im| ≤ 1 / 4) :
    -|(gammaHeightA T x).im| ≤ (gammaHeightA T x).re ∧
      -|(gammaHeightB T x).im| ≤ (gammaHeightB T x).re := by
  rw [gammaHeightA_re, gammaHeightB_re, gammaHeightA_im, gammaHeightB_im, abs_neg]
  have hpos : 0 ≤ T * x.re / 2 := by positivity
  rw [abs_of_nonneg hpos]
  have hims := abs_le.mp hxim
  have hl := mul_le_mul_of_nonneg_left hims.1 hT
  have hu := mul_le_mul_of_nonneg_left hims.2 hT
  have hr := mul_le_mul_of_nonneg_left hxre hT
  constructor <;> nlinarith

theorem norm_log_le_of_annulus {w : ℂ} (hlo : 1 / 4 ≤ ‖w‖) (hhi : ‖w‖ ≤ 2) :
    ‖Complex.log w‖ ≤ Real.log 4 + Real.pi := by
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hlo
  have hlow : -Real.log 4 ≤ Real.log ‖w‖ := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hlo
    rw [Real.log_div one_ne_zero (by norm_num), Real.log_one, zero_sub] at h
    exact h
  have hhigh : Real.log ‖w‖ ≤ Real.log 4 :=
    Real.log_le_log hw0 (hhi.trans (by norm_num))
  calc
    ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ Real.log 4 + Real.pi := by
      rw [Complex.log_re, Complex.log_im]
      exact add_le_add (abs_le.mpr ⟨hlow, hhigh⟩) (Complex.abs_arg_le_pi w)

theorem centeringPhaseComplexBound_pos : 0 < centeringPhaseComplexBound := by
  unfold centeringPhaseComplexBound
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  linarith [abs_nonneg (Real.log Real.pi), Real.pi_pos]

theorem centeringGammaMain_eq_exp {T : ℝ} {x : ℂ} (z : ℂ)
    (hT : 0 < T) (hL : Real.log T ≠ 0)
    (hA : gammaHeightA T x ≠ 0) (hB : gammaHeightB T x ≠ 0) :
    centeringGammaMain T x z =
      Complex.exp ((z / (Real.log T : ℂ)) * centeringGammaMainCoefficient T x) := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hLA := Complex.log_ofReal_mul hT (div_ne_zero hA hTc)
  have hLB := Complex.log_ofReal_mul hT (div_ne_zero hB hTc)
  rw [mul_div_cancel₀ _ hTc] at hLA hLB
  rw [centeringGammaMain,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    Complex.cpow_def_of_ne_zero hA, Complex.cpow_def_of_ne_zero hB,
    ← Complex.ofReal_log Real.pi_pos.le,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, hLA, hLB]
  congr 1
  unfold centeringGammaMainCoefficient
  field_simp [Complex.ofReal_ne_zero.mpr hL]
  ring

theorem centeringGammaMainCoefficient_norm_le {T : ℝ} {x : ℂ} (hT : 1 ≤ T)
    (hxre : x.re ∈ Set.Icc (3 / 4 : ℝ) (9 / 4)) (hxim : |x.im| ≤ 1 / 4) :
    ‖centeringGammaMainCoefficient T x‖ ≤ centeringPhaseComplexBound := by
  have hb := gammaHeight_normalized_norm_bounds hT hxre hxim
  have hA := norm_log_le_of_annulus hb.1.1 hb.1.2
  have hB := norm_log_le_of_annulus hb.2.1 hb.2.2
  unfold centeringGammaMainCoefficient
  calc
    _ ≤ ‖(Real.log Real.pi : ℂ)‖ +
        ‖(Complex.log (gammaHeightA T x / (T : ℂ)) +
          Complex.log (gammaHeightB T x / (T : ℂ))) / 2‖ := norm_sub_le _ _
    _ ≤ |Real.log Real.pi| +
        (‖Complex.log (gammaHeightA T x / (T : ℂ))‖ +
          ‖Complex.log (gammaHeightB T x / (T : ℂ))‖) / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, norm_div]
      simp only [Complex.norm_ofNat]
      exact add_le_add le_rfl (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num))
    _ ≤ |Real.log Real.pi| + ((Real.log 4 + Real.pi) + (Real.log 4 + Real.pi)) / 2 := by
      exact add_le_add le_rfl (div_le_div_of_nonneg_right (add_le_add hA hB) (by norm_num))
    _ = centeringPhaseComplexBound := by unfold centeringPhaseComplexBound; ring

theorem centeringGammaMain_error_bound {T R : ℝ} {x z : ℂ} (hT : 1 ≤ T)
    (hxre : x.re ∈ Set.Icc (3 / 4 : ℝ) (9 / 4)) (hxim : |x.im| ≤ 1 / 4)
    (hz : ‖z‖ ≤ R) (hL : 0 < Real.log T)
    (hlarge : R * centeringPhaseComplexBound ≤ Real.log T) :
    ‖centeringGammaMain T x z - 1‖ ≤ 2 * R * centeringPhaseComplexBound / Real.log T := by
  have hT0 := zero_lt_one.trans_le hT
  have hx0 : 0 < x.re := lt_of_lt_of_le (by norm_num) hxre.1
  have hnz := gammaHeight_im_ne_zero hT0 hx0
  have hA : gammaHeightA T x ≠ 0 := by intro h; exact hnz.1 (by simp [h])
  have hB : gammaHeightB T x ≠ 0 := by intro h; exact hnz.2 (by simp [h])
  rw [centeringGammaMain_eq_exp z hT0 hL.ne' hA hB]
  have hR : 0 ≤ R := (norm_nonneg _).trans hz
  have hexponent : ‖(z / (Real.log T : ℂ)) * centeringGammaMainCoefficient T x‖ ≤
      R * centeringPhaseComplexBound / Real.log T := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    calc
      _ ≤ (R / Real.log T) * centeringPhaseComplexBound :=
        mul_le_mul (div_le_div_of_nonneg_right hz hL.le)
          (centeringGammaMainCoefficient_norm_le hT hxre hxim) (norm_nonneg _)
            (div_nonneg hR hL.le)
      _ = _ := by ring
  have hsmall : ‖(z / (Real.log T : ℂ)) * centeringGammaMainCoefficient T x‖ ≤ 1 :=
    hexponent.trans ((div_le_one hL).mpr hlarge)
  calc
    _ ≤ 2 * ‖(z / (Real.log T : ℂ)) * centeringGammaMainCoefficient T x‖ :=
      Complex.norm_exp_sub_one_le hsmall
    _ ≤ 2 * (R * centeringPhaseComplexBound / Real.log T) :=
      mul_le_mul_of_nonneg_left hexponent (by norm_num)
    _ = _ := by ring

theorem centeringGammaMain_uniform_error_bound (R : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ x : ℂ,
      x.re ∈ Set.Icc (3 / 4 : ℝ) (9 / 4) → |x.im| ≤ 1 / 4 →
      ∀ z : ℂ, ‖z‖ ≤ R →
        ‖centeringGammaMain T x z - 1‖ ≤ 2 * R * centeringPhaseComplexBound / Real.log T := by
  have hlog := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (R * centeringPhaseComplexBound))
  filter_upwards [hlog, eventually_gt_atTop (1 : ℝ)] with T hlogT hT
  intro x hxre hxim z hz
  exact centeringGammaMain_error_bound hT.le hxre hxim hz (Real.log_pos hT) hlogT

end

end SixthMoment
