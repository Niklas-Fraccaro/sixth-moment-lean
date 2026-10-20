import Sechstmoment.Analysis.Gaussian.Tails
import Sechstmoment.Numerator.Polar.PureHorizontal
import Sechstmoment.Numerator.U.Replacement.CentralContourShift
import Sechstmoment.Zeta.AFE.Four.LargeGammaStrip


namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def bblrVKernel (G : ℂ → ℂ) (α : MomentShifts) (x t : ℝ) (z : ℂ) : ℂ :=
  G z/z*bblrGammaQuotient t α z*(Real.pi:ℂ)^(-2*z)*(x:ℂ)^(-z)

theorem positiveReal_cpow_norm_nonnegative_strip_bound {a b : ℝ} (ha : 0<a)
    (k : ℝ) {z : ℂ} (hz : z.re∈Icc (0:ℝ) b) :
    ‖(a:ℂ)^((k:ℂ)*z)‖ ≤ 1+a^(k*b) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]
  have he : ((k:ℂ)*z).re=k*z.re := by simp
  rw [he,Real.rpow_def_of_pos ha,Real.rpow_def_of_pos ha]
  by_cases hL : 0≤Real.log a*k
  · have hp : Real.log a*(k*z.re)≤Real.log a*(k*b) := by nlinarith [hz.2]
    exact (Real.exp_le_exp.mpr hp).trans (by linarith [Real.exp_pos (Real.log a*(k*b))])
  · have hp : Real.log a*(k*z.re)≤0 := by nlinarith [hz.1]
    exact (Real.exp_le_exp.mpr hp).trans (by simp; positivity)

theorem bblrGammaQuotient_differentiableOn_rightHalfPlane
    (t : ℝ) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
    DifferentiableOn ℂ (bblrGammaQuotient t α) {z : ℂ | 0<z.re} := by
  unfold bblrGammaQuotient
  apply DifferentiableOn.fun_finsetProd
  intro j _ z hz
  change 0<z.re at hz
  have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
  have hre : 0<((sourceZetaPoints t j+α j+z)/2).re := by
    rw [Complex.div_ofNat_re,Complex.add_re,Complex.add_re,sourceZetaPoints_re]
    linarith
  have hn (n : ℕ) : (sourceZetaPoints t j+α j+z)/2 ≠ -(n:ℂ) := by
    intro he
    rw [he,Complex.neg_re,Complex.natCast_re] at hre
    have hn0 : (0:ℝ)≤n := Nat.cast_nonneg _
    linarith
  have haff : DifferentiableAt ℂ (fun z : ℂ => (sourceZetaPoints t j+α j+z)/2) z := by
    fun_prop
  exact (((Complex.differentiableAt_Gamma _ hn).comp z haff).div_const _).differentiableWithinAt

theorem bblrVKernel_differentiableOn_rightHalfPlane {x : ℝ} (hx : 0<x)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t : ℝ) :
    DifferentiableOn ℂ (bblrVKernel G α x t) {z : ℂ | 0<z.re} := by
  have hQ := bblrGammaQuotient_differentiableOn_rightHalfPlane t α hα
  have hπ : DifferentiableOn ℂ (fun z : ℂ => (Real.pi:ℂ)^(-2*z)) {z : ℂ | 0<z.re} :=
    (differentiableOn_id.const_mul (-2:ℂ)).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hxp : DifferentiableOn ℂ (fun z : ℂ => (x:ℂ)^(-z)) {z : ℂ | 0<z.re} :=
    differentiableOn_id.neg.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hz0 : ∀ z∈{z : ℂ | 0<z.re}, z≠0 := by intro z hz he; simp [he] at hz
  exact (((hG.differentiableOn.div differentiableOn_id hz0).mul hQ).mul hπ).mul hxp

theorem bblrVKernel_large_strip_majorant (r : ℕ) {t x : ℝ}
    (ht : 0≤t) (hx : 0<x) (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, ‖α j‖≤1/4) :
    ∃ K : ℝ, 0≤K ∧ ∀ c∈Icc (1:ℝ) (1+2*(r:ℝ)), ∀ v : ℝ,
      ‖bblrVKernel G α x t ((c:ℂ)+(v:ℂ)*I)‖ ≤ K*(1+v^2)⁻¹ := by
  obtain ⟨C,hC,hGamma⟩ := bblrGammaQuotient_polynomial_large_positive_strip_bound r
  obtain ⟨B,hB,hWeight⟩ := hG.2.2.2 (1+2*(r:ℝ)) (by positivity) (4*r+10)
  let Q := 1+Real.pi^(-2*(1+2*(r:ℝ)))
  let X := 1+x^(-(1+2*(r:ℝ)))
  let D := C*(2+t)^(4*r+8)*Q*X
  have hD : 0≤D := by dsimp [D,Q,X]; positivity
  refine ⟨B*D,mul_nonneg hB hD,?_⟩
  intro c hc v
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  let W : ℝ := 1+|v|
  have hzre : z.re=c := by simp [z]
  have hzim : z.im=v := by simp [z]
  have hstrip : z.re∈Icc (0:ℝ) (1+2*(r:ℝ)) := by
    rw [hzre]
    exact ⟨(by norm_num : (0:ℝ)≤1).trans hc.1,hc.2⟩
  have hQ : ‖(Real.pi:ℂ)^(-2*z)‖≤Q := by
    simpa [Q] using positiveReal_cpow_norm_nonnegative_strip_bound Real.pi_pos (-2) hstrip
  have hX : ‖(x:ℂ)^(-z)‖≤X := by
    simpa [X] using positiveReal_cpow_norm_nonnegative_strip_bound hx (-1) hstrip
  have hGammaN : ‖bblrGammaQuotient t α z‖≤C*(2+t)^(4*r+8)*W^(4*r+8) := by
    apply (hGamma t v c ht (by linarith [hc.1]) hc.2 α hα).trans
    rw [mul_assoc,← mul_pow]
    gcongr
    dsimp [W]
    nlinarith [abs_nonneg v]
  have hInv : ‖z‖⁻¹≤1 := by
    have hn : 1≤‖z‖ := hc.1.trans (by rw [← hzre]; exact Complex.re_le_norm z)
    exact inv_le_one_of_one_le₀ hn
  have hN : ‖bblrVKernel G α x t z‖≤‖G z‖*D*W^(4*r+8) := by
    unfold bblrVKernel
    simp only [norm_mul,norm_div]
    rw [div_eq_mul_inv]
    calc
      _ ≤ (‖G z‖*1)*(C*(2+t)^(4*r+8)*W^(4*r+8))*Q*X := by gcongr
      _ = _ := by dsimp [D]; ring
  have hGN : ‖G z‖*W^(4*r+10)≤B := by
    have habs : |z.re|≤1+2*(r:ℝ) := by
      rw [hzre,abs_of_nonneg (by linarith [hc.1])]
      exact hc.2
    simpa only [hzim] using hWeight z habs
  have hFull : ‖bblrVKernel G α x t z‖*W^2≤B*D := by
    calc
      _ ≤ (‖G z‖*D*W^(4*r+8))*W^2 := mul_le_mul_of_nonneg_right hN (sq_nonneg W)
      _ = (‖G z‖*W^(4*r+10))*D := by
        rw [show 4*r+10=(4*r+8)+2 by omega,pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hGN hD
  have hSq : 1+v^2≤W^2 := by dsimp [W]; nlinarith only [sq_abs v,abs_nonneg v]
  have hProd : ‖bblrVKernel G α x t z‖*(1+v^2)≤B*D :=
    (mul_le_mul_of_nonneg_left hSq (norm_nonneg _)).trans hFull
  rw [inv_eq_one_div,mul_one_div]
  exact (le_div_iff₀ (by positivity : 0<1+v^2)).mpr hProd

theorem bblrVKernel_large_positive_line_integrable (r : ℕ) {t x c : ℝ}
    (ht : 0≤t) (hx : 0<x) (hc : c∈Icc (1:ℝ) (1+2*(r:ℝ)))
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖≤1/4) :
    Integrable (fun v : ℝ => bblrVKernel G α x t ((c:ℂ)+(v:ℂ)*I)) := by
  obtain ⟨K,_,hbound⟩ := bblrVKernel_large_strip_majorant r ht hx G α hG hα
  have hd := bblrVKernel_differentiableOn_rightHalfPlane hx G
    (Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1) α hα t
  have hcont : Continuous (fun v : ℝ => bblrVKernel G α x t ((c:ℂ)+(v:ℂ)*I)) :=
    hd.continuousOn.comp_continuous (by fun_prop) (fun v => by simp; linarith [hc.1])
  apply (integrable_inv_one_add_sq.const_mul K).mono' hcont.aestronglyMeasurable
  exact Eventually.of_forall (fun v => by simpa [one_div] using hbound c hc v)

theorem bblrVKernel_large_strip_horizontal_tendsto_zero (r : ℕ) {t x : ℝ}
    (ht : 0≤t) (hx : 0<x) (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, ‖α j‖≤1/4) :
    Tendsto (fun v : ℝ => ∫ c in (1:ℝ)..(1+2*(r:ℝ)),
      bblrVKernel G α x t ((c:ℂ)+(v:ℂ)*I)) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨K,_,hbound⟩ := bblrVKernel_large_strip_majorant r ht hx G α hG hα
  have hlim : Tendsto (fun v : ℝ => K*|1+2*(r:ℝ)-1| * (1+v^2)⁻¹)
      (cocompact ℝ) (𝓝 0) := by
    have hv : Tendsto (fun v : ℝ => |v|) (cocompact ℝ) atTop := by
      rw [cocompact_eq_atBot_atTop]
      exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
    have hv2 : Tendsto (fun v : ℝ => 1+v^2) (cocompact ℝ) atTop := by
      have h := (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp hv
      have hs : Tendsto (fun v : ℝ => v^2) (cocompact ℝ) atTop := by
        apply h.congr'
        exact Eventually.of_forall (fun v => by simp only [Function.comp_apply,sq_abs])
      exact tendsto_atTop_mono (fun v => by linarith) hs
    simpa only [Function.comp_apply,mul_zero] using
      (tendsto_inv_atTop_zero.comp hv2).const_mul (K*|1+2*(r:ℝ)-1|)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  exact Eventually.of_forall (fun v => by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1:ℝ)) (b := 1+2*(r:ℝ))
      (f := fun c => bblrVKernel G α x t ((c:ℂ)+(v:ℂ)*I))
      (C := K*(1+v^2)⁻¹) (by
        intro c hc
        rw [uIoc_of_le (by have hr : 0≤(r:ℝ) := Nat.cast_nonneg r; linarith : (1:ℝ)≤1+2*(r:ℝ))] at hc
        exact hbound c ⟨hc.1.le,hc.2⟩ v)
    exact hb.trans_eq (by ring))

theorem bblrV_large_positive_contour (r : ℕ) {t x : ℝ} (ht : 0≤t) (hx : 0<x)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖≤1/4) :
    bblrV G α x t = verticalIntegral (1+2*(r:ℝ)) (bblrVKernel G α x t) := by
  have h := Sechstmoment.bblrRectangle_verticalIntegral_shift
    (bblrVKernel G α x t)
    (bblrVKernel_differentiableOn_rightHalfPlane hx G
      (Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1) α hα t)
    (by have hr : 0≤(r:ℝ) := Nat.cast_nonneg r; linarith : (1:ℝ)≤1+2*(r:ℝ))
    (fun z hz _ => by change 0<z.re; linarith)
    (bblrVKernel_large_positive_line_integrable r ht hx
      ⟨le_rfl,by have hr : 0≤(r:ℝ) := Nat.cast_nonneg r; linarith⟩ G α hG hα)
    (bblrVKernel_large_positive_line_integrable r ht hx
      ⟨by have hr : 0≤(r:ℝ) := Nat.cast_nonneg r; linarith,le_rfl⟩ G α hG hα)
    (bblrVKernel_large_strip_horizontal_tendsto_zero r ht hx G α hG hα)
  exact h.symm

theorem bblrGaussianV_large_positive_line_norm_le (r : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, ∀ σ α : MomentShifts, (∀ j, ‖α j‖≤1/4) →
      ∀ t x : ℝ, 0≤t → 0<x →
      ‖bblrV (polarPoleKiller T σ) α x t‖ ≤
        C*polarGaussianConstant T σ (1+2*(r:ℝ))*(2+t)^(4*r+8)*
          x^(-(1+2*(r:ℝ))) := by
  obtain ⟨D,hD,hGamma⟩ := bblrGammaQuotient_polynomial_large_positive_strip_bound r
  let c : ℝ := 1+2*(r:ℝ)
  let d : ℕ := 4*r+56
  have hJ := gaussianTailConstant_nonneg d
  refine ⟨D*Real.pi^(-2*c)*gaussianTailConstant d/(2*Real.pi),by positivity,?_⟩
  intro T σ α hα t x ht hx
  let B : ℝ := D*polarGaussianConstant T σ c*(2+t)^(4*r+8)*Real.pi^(-2*c)*x^(-c)
  have hCG := polarGaussianConstant_nonneg T σ c
  have hB : 0≤B := by dsimp [B]; positivity
  have hpoint (v : ℝ) :
      ‖bblrVKernel (polarPoleKiller T σ) α x t ((c:ℂ)+(v:ℂ)*I)‖ ≤
        B*((1+|v|)^d*Real.exp (-(1/2)*v^2)) := by
    let z : ℂ := (c:ℂ)+(v:ℂ)*I
    have hzn : 1≤‖z‖ := by
      have hc1 : 1≤c := by dsimp [c]; have hr : 0≤(r:ℝ) := Nat.cast_nonneg r; linarith
      exact hc1.trans (by simpa [z] using Complex.re_le_norm z)
    have hg : ‖polarPoleKiller T σ z/z‖≤polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2) := by
      rw [norm_div]
      exact (div_le_self (norm_nonneg _) hzn).trans (polarPoleKiller_vertical_norm_le T σ c v)
    have hπ : ‖(Real.pi:ℂ)^(-2*z)‖=Real.pi^(-2*c) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      congr 1
      simp [z]
    have hxp : ‖(x:ℂ)^(-z)‖=x^(-c) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      congr 1
      simp [z]
    have hp : (2+t+|v|)^(4*r+8)≤(2+t)^(4*r+8)*(1+|v|)^(4*r+8) := by
      rw [← mul_pow]
      gcongr
      nlinarith [abs_nonneg v]
    have he : Real.exp (-v^2)≤Real.exp (-(1/2)*v^2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg v])
    unfold bblrVKernel
    rw [norm_mul,norm_mul,norm_mul,hπ,hxp]
    calc
      _ ≤ (polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2))*
          (D*((2+t)^(4*r+8)*(1+|v|)^(4*r+8)))*Real.pi^(-2*c)*x^(-c) := by
        gcongr
        exact (hGamma t v c ht (by dsimp [c]; positivity) le_rfl α hα).trans
          (mul_le_mul_of_nonneg_left hp hD.le)
      _ = B*((1+|v|)^d*Real.exp (-v^2)) := by
        dsimp [B,d]
        rw [show 4*r+56=48+(4*r+8) by omega,pow_add]
        ring
      _ ≤ _ := by gcongr
  have hi := bblrVKernel_large_positive_line_integrable r ht hx
    (show c∈Icc (1:ℝ) (1+2*(r:ℝ)) from
      ⟨by dsimp [c]; have hr : 0≤(r:ℝ) := Nat.cast_nonneg r; linarith,le_rfl⟩)
    (polarPoleKiller T σ) α (polarPoleKiller_BBLREntireWeight T σ α) hα
  have hb := norm_integral_le_of_norm_le
    ((gaussian_polynomial_half_integrable d).const_mul B) (Eventually.of_forall hpoint)
  rw [bblrV_large_positive_contour r ht hx _ _ (polarPoleKiller_BBLREntireWeight T σ α) hα]
  unfold verticalIntegral
  rw [norm_mul,show ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]]
  calc
    _ ≤ (1/(2*Real.pi))*(∫ v : ℝ, B*((1+|v|)^d*Real.exp (-(1/2)*v^2))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [integral_const_mul]; dsimp [B,c,gaussianTailConstant]; ring

end
end Sechstmoment.Source
