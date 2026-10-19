import Sechstmoment.Numerator.U.Replacement.TimeGamma.Derivatives

/-!
# Actual Gamma replacement error on a complex time window

The complex time estimate preserves the factor T⁻¹ before Cauchy is applied.
This supplies the missing time-symbol saving, independently of any amplified
moment estimate or zero-mode reconstruction.
-/
namespace Sechstmoment.Source
open Complex Set Metric
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem bblrTimeWindow_log_im {x : ℝ} (hx : x ∈ Icc (1:ℝ) 2)
    {y : ℂ} (hy : y ∈ closedBall (x:ℂ) (1/4:ℝ)) :
    |(Complex.log y).im| ≤ 1/2 := by
  have hxpos : 0<x := by linarith [hx.1]
  have hx0 : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
  have hn : ‖y-(x:ℂ)‖≤1/4 := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hd : ‖y/(x:ℂ)-1‖≤1/4 := by
    rw [div_sub_one hx0,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxpos]
    apply (div_le_iff₀ hxpos).mpr
    nlinarith [hx.1]
  have hz : y/(x:ℂ)≠0 := by
    intro he
    rw [he] at hd
    norm_num at hd
  have hb := Complex.norm_log_one_add_half_le_self (hd.trans (by norm_num : (1/4:ℝ)≤1/2))
  rw [add_sub_cancel] at hb
  have he : (x:ℂ)*(y/(x:ℂ))=y := mul_div_cancel₀ _ hx0
  have hl := Complex.log_ofReal_mul hxpos hz
  rw [he] at hl
  rw [hl]
  simp only [Complex.add_im,Complex.ofReal_im,zero_add]
  exact (Complex.abs_im_le_norm _).trans (hb.trans (by linarith))

private theorem time_base_scaled_sub_center {T : ℝ} (hT : T≠0)
    (α : MomentShifts) {y : ℂ} (hy : y≠0) (j : Fin 4) :
    bblrTimeGammaBase T α y j/((T:ℂ)*y/2)-bblrGammaPhaseCenter j =
      ((1/2:ℂ)+α j)/((T:ℂ)*y) := by
  have hTc : (T:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hT
  fin_cases j <;> simp [bblrTimeGammaBase,bblrTimeGammaSign,bblrGammaPhaseCenter] <;>
    field_simp <;> ring

theorem bblrTimeGammaBase_log_error {T A : ℝ} (hA : 0≤A) (hT : 8*(A+1)≤T)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ}
    (hy : y∈closedBall (x:ℂ) (1/4:ℝ)) (j : Fin 4) :
    ‖Complex.log (bblrTimeGammaBase T α y j)-
      Complex.log ((T:ℂ)*y/2)-Complex.log (bblrGammaPhaseCenter j)‖≤
        (2+4*A)/T := by
  have hTp : 0<T := by linarith
  have hw := bblrTimeGamma_closedBall_window hx hy
  have hyn : 3/4≤‖y‖ := hw.1.1.trans ((le_abs_self y.re).trans (Complex.abs_re_le_norm y))
  have hy0 : y≠0 := by intro he; rw [he,norm_zero] at hyn; norm_num at hyn
  have hp0 : (T:ℂ)*y/2≠0 := by exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hTp.ne') hy0) (by norm_num)
  let q := bblrTimeGammaBase T α y j/((T:ℂ)*y/2)
  have hdist : ‖q-bblrGammaPhaseCenter j‖≤(1+2*A)/T := by
    dsimp [q]
    rw [time_base_scaled_sub_center hTp.ne' α hy0 j,norm_div,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hTp]
    apply (div_le_iff₀ (mul_pos hTp (by linarith : 0<‖y‖))).mpr
    have hb := norm_add_le (1/2:ℂ) (α j)
    norm_num at hb
    have hh : ‖(1/2:ℂ)+α j‖≤1/2+A := by linarith [hα j]
    have hnon : 0≤1+2*A := by positivity
    have he : ((1+2*A)/T)*(T*‖y‖)=(1+2*A)*‖y‖ := by
      field_simp
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hyn hnon]
  have hdhalf : ‖q-bblrGammaPhaseCenter j‖≤1/2 := by
    apply hdist.trans
    rw [div_le_iff₀ hTp]
    linarith
  have hq0 : q≠0 := by
    intro he
    rw [he,zero_sub,norm_neg,bblrGammaPhaseCenter_norm] at hdhalf
    norm_num at hdhalf
  have harg : |(Complex.log (bblrGammaPhaseCenter j)).im|≤Real.pi/2 := by
    fin_cases j <;> simp [bblrGammaPhaseCenter,Complex.log_I,Complex.log_neg_I,
      abs_of_nonneg (by positivity : 0≤Real.pi/2)]
  have hlog := principalLog_unit_near_bound (bblrGammaPhaseCenter_norm j) harg hdhalf
  -- The sharper half-unit q error leaves a full margin to the logarithm cut.
  have hlogq : ‖Complex.log q-Complex.log (bblrGammaPhaseCenter j)‖≤1/2 := by
    apply hlog.trans
    apply (le_trans (mul_le_mul_of_nonneg_left hdist (by norm_num)))
    calc
      2*((1+2*A)/T)=(2*(1+2*A))/T := by ring
      _≤1/2 := (div_le_iff₀ hTp).mpr (by linarith)
  have himq' : |(Complex.log q).im|≤Real.pi/2+1/2 := by
    have hi := (Complex.abs_im_le_norm _).trans hlogq
    simp only [Complex.sub_im] at hi
    have hh := abs_add_le ((Complex.log q).im-(Complex.log (bblrGammaPhaseCenter j)).im)
      (Complex.log (bblrGammaPhaseCenter j)).im
    rw [sub_add_cancel] at hh
    linarith
  have hlogy := bblrTimeWindow_log_im hx hy
  have hlogp : Complex.log ((T:ℂ)*y/2)=(Real.log (T/2):ℂ)+Complex.log y := by
    have he : (T:ℂ)*y/2=(T/2:ℂ)*y := by ring
    rw [he]
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
      Complex.log_ofReal_mul (by positivity : 0<T/2) hy0
  have himp : |(Complex.log ((T:ℂ)*y/2)).im|≤1/2 := by simpa [hlogp] using hlogy
  have hmul : Complex.log (((T:ℂ)*y/2)*q)=
      Complex.log ((T:ℂ)*y/2)+Complex.log q := by
    apply Complex.log_mul hp0 hq0
    simp only [Complex.log_im] at himp himq'
    constructor <;> linarith [(abs_le.mp himp).1,(abs_le.mp himp).2,
      (abs_le.mp himq').1,(abs_le.mp himq').2,Real.pi_gt_three]
  have he : ((T:ℂ)*y/2)*q=bblrTimeGammaBase T α y j := by
    dsimp [q]
    exact mul_div_cancel₀ _ hp0
  rw [he] at hmul
  rw [hmul,add_sub_cancel_left]
  exact hlog.trans (by
    calc
      2*‖q-bblrGammaPhaseCenter j‖≤2*((1+2*A)/T) := by gcongr
      _=(2+4*A)/T := by ring)


def bblrTimeGammaMainPhase (T : ℝ) (α : MomentShifts) (z y : ℂ) : ℂ :=
  (∏ j : Fin 4, (bblrTimeGammaBase T α y j)^(z/2))/((T:ℂ)*y/2)^(2*z)

def bblrTimeGammaPhaseLogError (T : ℝ) (α : MomentShifts) (y : ℂ) : ℂ :=
  ∑ j : Fin 4, (Complex.log (bblrTimeGammaBase T α y j)-
    Complex.log ((T:ℂ)*y/2)-Complex.log (bblrGammaPhaseCenter j))

theorem bblrTimeGammaPhaseLogError_norm_le {T A : ℝ} (hA : 0≤A)
    (hT : 8*(A+1)≤T) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ}
    (hy : y∈closedBall (x:ℂ) (1/4:ℝ)) :
    ‖bblrTimeGammaPhaseLogError T α y‖≤(8+16*A)/T := by
  unfold bblrTimeGammaPhaseLogError
  calc
    _≤∑ j : Fin 4, ‖Complex.log (bblrTimeGammaBase T α y j)-
        Complex.log ((T:ℂ)*y/2)-Complex.log (bblrGammaPhaseCenter j)‖ := norm_sum_le _ _
    _≤∑ _j : Fin 4, (2+4*A)/T :=
      Finset.sum_le_sum (fun j _ => bblrTimeGammaBase_log_error hA hT α hα hx hy j)
    _=_ := by simp; ring

theorem bblrTimeGammaMainPhase_eq_exp {T A : ℝ} (hA : 0≤A)
    (hT : 8*(A+1)≤T) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ}
    (hy : y∈closedBall (x:ℂ) (1/4:ℝ)) (z : ℂ) :
    bblrTimeGammaMainPhase T α z y =
      Complex.exp ((z/2)*bblrTimeGammaPhaseLogError T α y) := by
  have hTp : 0<T := by linarith
  have hw := bblrTimeGamma_closedBall_window hx hy
  have hy0 : y≠0 := by intro he; rw [he] at hw; norm_num at hw
  have hp0 : (T:ℂ)*y/2≠0 :=
    div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hTp.ne') hy0) (by norm_num)
  have hb0 (j : Fin 4) : bblrTimeGammaBase T α y j≠0 := by
    have hg := bblrTimeGammaBase_geometry hA hT α hα hw.1 hw.2 j
    intro he
    simp [he] at hg
    linarith [hg.1]
  unfold bblrTimeGammaMainPhase
  simp_rw [Complex.cpow_def_of_ne_zero (hb0 _)]
  rw [← Complex.exp_sum,Complex.cpow_def_of_ne_zero hp0,← Complex.exp_sub]
  congr 1
  unfold bblrTimeGammaPhaseLogError
  simp only [Fin.sum_univ_succ,Fin.isValue]
  simp [bblrGammaPhaseCenter,Complex.log_I,Complex.log_neg_I]
  ring

theorem bblrTimeGammaMainPhase_error_le {T A : ℝ} (hA : 0≤A)
    (hT : 8*(A+1)≤T) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ}
    (hy : y∈closedBall (x:ℂ) (1/4:ℝ)) (z : ℂ)
    (hz : (4+8*A)*‖z‖≤T) :
    ‖bblrTimeGammaMainPhase T α z y-1‖≤(8+16*A)*‖z‖/T := by
  have hTp : 0<T := by linarith
  rw [bblrTimeGammaMainPhase_eq_exp hA hT α hα hx hy z]
  have hb := bblrTimeGammaPhaseLogError_norm_le hA hT α hα hx hy
  have he : ‖(z/2)*bblrTimeGammaPhaseLogError T α y‖≤(4+8*A)*‖z‖/T := by
    rw [norm_mul,norm_div]
    calc
      _≤(‖z‖/‖(2:ℂ)‖)*((8+16*A)/T) := by gcongr
      _=_ := by norm_num; ring
  have hs : ‖(z/2)*bblrTimeGammaPhaseLogError T α y‖≤1 :=
    he.trans ((div_le_iff₀ hTp).mpr (by simpa using hz))
  exact (Complex.norm_exp_sub_one_le hs).trans (by
    calc
      2*‖(z/2)*bblrTimeGammaPhaseLogError T α y‖≤2*((4+8*A)*‖z‖/T) := by gcongr
      _=_ := by ring)

def bblrTimeNormalizedGammaFactor (T : ℝ) (α : MomentShifts) (z y : ℂ)
    (j : Fin 4) : ℂ :=
  (Gamma (bblrTimeGammaBase T α y j+z/2)/Gamma (bblrTimeGammaBase T α y j))/
    (bblrTimeGammaBase T α y j)^(z/2)

theorem bblrTimeNormalizedGammaFactor_error_le {T A : ℝ} (hA : 0≤A)
    (hT : 8*(A+1)≤T) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ}
    (hy : y∈closedBall (x:ℂ) (1/4:ℝ)) (z : ℂ)
    (hz : 48*(‖z‖+‖z‖^2)<T) (j : Fin 4) :
    ‖bblrTimeNormalizedGammaFactor T α z y j-1‖≤48*(‖z‖+‖z‖^2)/T := by
  have hTp : 0<T := by linarith
  have hw := bblrTimeGamma_closedBall_window hx hy
  have hg := bblrTimeGammaBase_geometry hA hT α hα hw.1 hw.2 j
  have hnz : ‖z/2‖=‖z‖/2 := by rw [norm_div]; norm_num
  have hs : 2≤|(bblrTimeGammaBase T α y j).im| := by linarith [hg.1]
  have hu : 24*(‖z/2‖+‖z/2‖^2)< |(bblrTimeGammaBase T α y j).im| := by
    rw [hnz]
    nlinarith [hg.1,norm_nonneg z,sq_nonneg ‖z‖]
  have hb := Sechstmoment.gammaRatio_normalized_error_cone
    (bblrTimeGammaBase T α y j) (z/2) hg.2.1 hs hu
  unfold bblrTimeNormalizedGammaFactor
  apply hb.trans
  rw [hnz,div_le_div_iff₀ (by linarith : 0< |(bblrTimeGammaBase T α y j).im|) hTp]
  nlinarith [hg.1,norm_nonneg z,sq_nonneg ‖z‖]

theorem bblrTimeGammaQuotient_normalized_eq {T A : ℝ} (hA : 0≤A)
    (hT : 8*(A+1)≤T) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ}
    (hy : y∈closedBall (x:ℂ) (1/4:ℝ)) (z : ℂ) :
    bblrTimeGammaQuotient T α z y/((T:ℂ)*y/2)^(2*z) =
      (∏ j : Fin 4, bblrTimeNormalizedGammaFactor T α z y j)*
        bblrTimeGammaMainPhase T α z y := by
  have hTp : 0<T := by linarith
  have hw := bblrTimeGamma_closedBall_window hx hy
  have hb (j : Fin 4) : bblrTimeGammaBase T α y j≠0 := by
    have hg := bblrTimeGammaBase_geometry hA hT α hα hw.1 hw.2 j
    intro he
    simp [he] at hg
    linarith [hg.1]
  have hp : (∏ j : Fin 4, (bblrTimeGammaBase T α y j)^(z/2))≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => by simp [hb j])
  unfold bblrTimeGammaQuotient bblrTimeNormalizedGammaFactor bblrTimeGammaMainPhase
  conv_rhs => lhs; rw [Finset.prod_div_distrib]
  field_simp
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  congr 2
  ring

/-- The genuine complex-time normalized quotient error. Its T⁻¹ saving is
uniform on the full Cauchy circle, unlike a pointwise real-time estimate. -/
theorem bblrTimeGammaQuotient_normalized_error_le {T A : ℝ} (hA : 0≤A)
    (hT : 8*(A+1)≤T) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ}
    (hy : y∈closedBall (x:ℂ) (1/4:ℝ)) (z : ℂ)
    (hz : 192*(‖z‖+‖z‖^2)<T) (hphase : (8+16*A)*‖z‖≤T) :
    ‖bblrTimeGammaQuotient T α z y/((T:ℂ)*y/2)^(2*z)-1‖≤
      (1440*(‖z‖+‖z‖^2)+(8+16*A)*‖z‖)/T := by
  have hTp : 0<T := by linarith
  have hzn : 0≤‖z‖+‖z‖^2 := by positivity
  have hz48 : 48*(‖z‖+‖z‖^2)<T := by linarith
  let E := 48*(‖z‖+‖z‖^2)/T
  have hE : 0≤E := by dsimp [E]; positivity
  have hE1 : E≤1 := by dsimp [E]; rw [div_le_iff₀ hTp]; linarith
  have herr (j : Fin 4) : ‖bblrTimeNormalizedGammaFactor T α z y j-1‖≤E :=
    bblrTimeNormalizedGammaFactor_error_le hA hT α hα hx hy z hz48 j
  have hp := fourfold_product_error_le (bblrTimeNormalizedGammaFactor T α z y) hE hE1 herr
  have hphase' : (4+8*A)*‖z‖≤T := by nlinarith [norm_nonneg z]
  have hf := bblrTimeGammaMainPhase_error_le hA hT α hα hx hy z hphase'
  have hfn : ‖bblrTimeGammaMainPhase T α z y‖≤2 := by
    have hh : ‖bblrTimeGammaMainPhase T α z y‖≤‖bblrTimeGammaMainPhase T α z y-1‖+1 := by
      convert norm_add_le (bblrTimeGammaMainPhase T α z y-1) (1:ℂ) using 1 <;> simp
    have hd : (8+16*A)*‖z‖/T≤1 := (div_le_iff₀ hTp).mpr (by simpa using hphase)
    linarith
  rw [bblrTimeGammaQuotient_normalized_eq hA hT α hα hx hy z]
  have he : (∏ j : Fin 4, bblrTimeNormalizedGammaFactor T α z y j)*
      bblrTimeGammaMainPhase T α z y-1 =
      ((∏ j : Fin 4, bblrTimeNormalizedGammaFactor T α z y j)-1)*
        bblrTimeGammaMainPhase T α z y+(bblrTimeGammaMainPhase T α z y-1) := by ring
  rw [he]
  calc
    _≤‖((∏ j : Fin 4, bblrTimeNormalizedGammaFactor T α z y j)-1)*
        bblrTimeGammaMainPhase T α z y‖+‖bblrTimeGammaMainPhase T α z y-1‖ := norm_add_le _ _
    _≤(15*E)*2+(8+16*A)*‖z‖/T := by rw [norm_mul]; gcongr
    _=_ := by dsimp [E]; ring


def bblrTimeGammaReplacementError (T : ℝ) (α : MomentShifts) (z y : ℂ) : ℂ :=
  bblrTimeGammaQuotient T α z y-((T:ℂ)*y/2)^(2*z)

private theorem time_main_power_norm_le {T : ℝ} (hT : 0<T)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ}
    (hy : y∈closedBall (x:ℂ) (1/4:ℝ)) {z : ℂ} (hz : 0≤z.re) :
    ‖((T:ℂ)*y/2)^(2*z)‖≤(2*T)^(2*z.re)*Real.exp (2*Real.pi*|z.im|) := by
  have hw := bblrTimeGamma_closedBall_window hx hy
  have hy0 : y≠0 := by intro he; rw [he] at hw; norm_num at hw
  have hp0 : (T:ℂ)*y/2≠0 :=
    div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hT.ne') hy0) (by norm_num)
  have hyn : ‖y‖≤5/2 := by
    have hre : |y.re|≤9/4 := by rw [abs_of_nonneg (by linarith [hw.1.1])]; exact hw.1.2
    exact (Complex.norm_le_abs_re_add_abs_im y).trans (by linarith [hw.2])
  have hpn : ‖(T:ℂ)*y/2‖≤2*T := by
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
    norm_num
    nlinarith
  have hre : (2*z).re=2*z.re := by simp
  have him : (2*z).im=2*z.im := by simp
  rw [Complex.norm_cpow_of_ne_zero hp0,hre,him,div_eq_mul_inv,← Real.exp_neg]
  apply mul_le_mul
  · exact Real.rpow_le_rpow (norm_nonneg _) hpn (by positivity)
  · apply Real.exp_le_exp.mpr
    have ha := Complex.abs_arg_le_pi ((T:ℂ)*y/2)
    have hh := mul_le_mul_of_nonneg_right ha (abs_nonneg z.im)
    have hn := neg_le_abs (Complex.arg ((T:ℂ)*y/2)*(2*z.im))
    rw [abs_mul,abs_mul] at hn
    norm_num at hn
    linarith
  · positivity
  · positivity

/-- The actual complex-time Gamma difference retains the T⁻¹ saving. -/
theorem bblrTimeGammaReplacementError_complex_norm_le {T A : ℝ} (hA : 0≤A)
    (hT : 8*(A+1)≤T) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) {y : ℂ}
    (hy : y∈closedBall (x:ℂ) (1/4:ℝ)) {z : ℂ} (hzre : 0≤z.re)
    (hz : 192*(‖z‖+‖z‖^2)<T) (hphase : (8+16*A)*‖z‖≤T) :
    ‖bblrTimeGammaReplacementError T α z y‖≤
      (2*T)^(2*z.re)*Real.exp (2*Real.pi*|z.im|)*
        ((1440*(‖z‖+‖z‖^2)+(8+16*A)*‖z‖)/T) := by
  have hTp : 0<T := by linarith
  have hw := bblrTimeGamma_closedBall_window hx hy
  have hy0 : y≠0 := by intro he; rw [he] at hw; norm_num at hw
  have hp0 : (T:ℂ)*y/2≠0 :=
    div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hTp.ne') hy0) (by norm_num)
  have hcp0 : ((T:ℂ)*y/2)^(2*z)≠0 := by simp [hp0]
  have he : bblrTimeGammaReplacementError T α z y =
      ((T:ℂ)*y/2)^(2*z)*(bblrTimeGammaQuotient T α z y/((T:ℂ)*y/2)^(2*z)-1) := by
    unfold bblrTimeGammaReplacementError
    field_simp
  rw [he,norm_mul]
  apply mul_le_mul
  · exact time_main_power_norm_le hTp hx hy hzre
  · exact bblrTimeGammaQuotient_normalized_error_le hA hT α hα hx hy z hz hphase
  · exact norm_nonneg _
  · positivity

/-- Cauchy now yields all real time derivatives with the same saving. -/
theorem bblrGammaReplacementError_normalizedTime_derivative_bound (n : ℕ)
    {T A : ℝ} (hA : 0≤A) (hT : 8*(A+1)≤T) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤A) {z : ℂ} (hzre : 0≤z.re)
    (hz : 192*(‖z‖+‖z‖^2)<T) (hphase : (8+16*A)*‖z‖≤T)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) :
    ‖iteratedDeriv n (fun y : ℝ => bblrGammaQuotient (T*y) α z-(T*y/2:ℂ)^(2*z)) x‖≤
      ((n.factorial:ℝ)/(1/4:ℝ)^n)*(2*T)^(2*z.re)*Real.exp (2*Real.pi*|z.im|)*
        ((1440*(‖z‖+‖z‖^2)+(8+16*A)*‖z‖)/T) := by
  have hTp : 0<T := by linarith
  have hd : DifferentiableOn ℂ (bblrTimeGammaReplacementError T α z)
      (closedBall (x:ℂ) (1/4:ℝ)) := by
    intro y hy
    have hw := bblrTimeGamma_closedBall_window hx hy
    have hy0 : y≠0 := by intro he; rw [he] at hw; norm_num at hw
    have hp0 : (T:ℂ)*y/2≠0 :=
      div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hTp.ne') hy0) (by norm_num)
    have hp : DifferentiableAt ℂ (fun y : ℂ => ((T:ℂ)*y/2)^(2*z)) y := by
      apply DifferentiableAt.cpow_const
      · fun_prop
      · apply Complex.mem_slitPlane_iff.mpr
        left
        simp only [Complex.div_ofNat_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
        have hrey : 0<y.re := by linarith [hw.1.1]
        positivity
    exact ((bblrTimeGammaQuotient_differentiableAt hA hT α hα hz hw.1 hw.2).sub hp).differentiableWithinAt
  have hf : DiffContOnCl ℂ (bblrTimeGammaReplacementError T α z)
      (ball (x:ℂ) (1/4:ℝ)) :=
    (hd.mono closure_ball_subset_closedBall).diffContOnCl
  have hM (y : ℂ) (hy : y∈sphere (x:ℂ) (1/4:ℝ)) :
      ‖bblrTimeGammaReplacementError T α z y‖≤
      (2*T)^(2*z.re)*Real.exp (2*Real.pi*|z.im|)*
        ((1440*(‖z‖+‖z‖^2)+(8+16*A)*‖z‖)/T) :=
    bblrTimeGammaReplacementError_complex_norm_le hA hT α hα hx (sphere_subset_closedBall hy) hzre hz hphase
  have he : (fun y : ℝ => bblrTimeGammaReplacementError T α z (y:ℂ))=
      (fun y : ℝ => bblrGammaQuotient (T*y) α z-(T*y/2:ℂ)^(2*z)) := by
    funext y
    unfold bblrTimeGammaReplacementError
    rw [bblrTimeGammaQuotient_ofReal]
  rw [← he]
  have hb := Sechstmoment.cauchy_real_iteratedDeriv_bound n (by norm_num : (0:ℝ)<1/4) hf hM
  convert hb using 1
  ring


theorem bblrGammaReplacementError_normalizedTime_contDiffAt
    {T A : ℝ} (hA : 0≤A) (hT : 8*(A+1)≤T) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤A) {z : ℂ}
    (hz : 192*(‖z‖+‖z‖^2)<T) {x : ℝ} (hx : x∈Icc (1:ℝ) 2) :
    ContDiffAt ℝ ⊤ (fun y : ℝ => bblrGammaQuotient (T*y) α z-(T*y/2:ℂ)^(2*z)) x := by
  have hTp : 0<T := by linarith
  have ha : AnalyticAt ℂ (bblrTimeGammaReplacementError T α z) (x:ℂ) := by
    apply DifferentiableOn.analyticAt _
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0:ℝ)<1/4)))
    intro y hy
    have hw := bblrTimeGamma_closedBall_window hx (ball_subset_closedBall hy)
    have hp : DifferentiableAt ℂ (fun y : ℂ => ((T:ℂ)*y/2)^(2*z)) y := by
      apply DifferentiableAt.cpow_const
      · fun_prop
      · apply Complex.mem_slitPlane_iff.mpr
        left
        simp only [Complex.div_ofNat_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
        have hrey : 0<y.re := by linarith [hw.1.1]
        positivity
    exact ((bblrTimeGammaQuotient_differentiableAt hA hT α hα hz hw.1 hw.2).sub hp).differentiableWithinAt
  have hc : ContDiffAt ℝ ⊤ (bblrTimeGammaReplacementError T α z) (x:ℂ) :=
    ha.contDiffAt.restrict_scalars ℝ
  have he : (fun y : ℝ => bblrTimeGammaReplacementError T α z (y:ℂ))=
      (fun y : ℝ => bblrGammaQuotient (T*y) α z-(T*y/2:ℂ)^(2*z)) := by
    funext y
    unfold bblrTimeGammaReplacementError
    rw [bblrTimeGammaQuotient_ofReal]
  rw [← he]
  exact hc.comp x Complex.ofRealCLM.contDiff.contDiffAt

end
end Sechstmoment.Source
