import Sechstmoment.Numerator.U.Separation.SmallContour.LogTail

/-! Genuine positive contour movement and Gaussian truncation for the
literal gamma-free VStar weight. No source divisor input is used. -/
namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def bblrVStarKernel (G : ℂ → ℂ) (y : ℝ) (z : ℂ) : ℂ :=
  G z/z*(2*Real.pi:ℂ)^(-2*z)*(y:ℂ)^(-z)

theorem bblrVStarKernel_differentiableOn_rightHalfPlane {y : ℝ} (hy : 0<y)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G) :
    DifferentiableOn ℂ (bblrVStarKernel G y) {z : ℂ | 0<z.re} := by
  have hπ : DifferentiableOn ℂ (fun z : ℂ => (2*Real.pi:ℂ)^(-2*z)) {z : ℂ | 0<z.re} :=
    (differentiableOn_id.const_mul (-2:ℂ)).const_cpow
      (.inl (by exact_mod_cast (show 2*Real.pi≠0 by positivity)))
  have hyw : DifferentiableOn ℂ (fun z : ℂ => (y:ℂ)^(-z)) {z : ℂ | 0<z.re} :=
    differentiableOn_id.neg.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  have hz0 : ∀ z∈{z : ℂ | 0<z.re}, z≠0 := by intro z hz he; simp [he] at hz
  exact ((hG.differentiableOn.div differentiableOn_id hz0).mul hπ).mul hyw

theorem bblrVStarKernel_positive_strip_majorant {y a b : ℝ}
    (hy : 0<y) (ha : 0<a) (hab : a≤b) (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) :
    ∃ K : ℝ, 0≤K ∧ ∀ d∈Icc a b, ∀ v : ℝ,
      ‖bblrVStarKernel G y ((d:ℂ)+(v:ℂ)*I)‖≤K*(1+v^2)⁻¹ := by
  obtain ⟨B,hB,hWeight⟩ := hG.2.2.2 b (ha.trans_le hab) 2
  let Q : ℝ := 1+(2*Real.pi)^(-2*b)
  let Y : ℝ := 1+y^(-b)
  let D : ℝ := a⁻¹*Q*Y
  have hD : 0≤D := by dsimp [D,Q,Y]; positivity
  refine ⟨B*D,mul_nonneg hB hD,?_⟩
  intro d hd v
  let z : ℂ := (d:ℂ)+(v:ℂ)*I
  have hzstrip : z.re∈Icc (0:ℝ) b := by simpa [z] using ⟨ha.le.trans hd.1,hd.2⟩
  have hQ : ‖(2*Real.pi:ℂ)^(-2*z)‖≤Q := by
    simpa [Q] using positiveReal_cpow_norm_nonnegative_strip_bound
      (by positivity : 0<2*Real.pi) (-2) hzstrip
  have hY : ‖(y:ℂ)^(-z)‖≤Y := by
    simpa [Y] using positiveReal_cpow_norm_nonnegative_strip_bound hy (-1) hzstrip
  have hInv : ‖z‖⁻¹≤a⁻¹ := by
    apply inv_anti₀ ha
    exact hd.1.trans (by simpa [z] using Complex.re_le_norm z)
  have hN : ‖bblrVStarKernel G y z‖≤‖G z‖*D := by
    unfold bblrVStarKernel
    rw [norm_mul,norm_mul,norm_div,div_eq_mul_inv]
    calc
      _ ≤ (‖G z‖*a⁻¹)*Q*Y := by gcongr
      _ = _ := by dsimp [D]; ring
  have hGN : ‖G z‖*(1+|v|)^2≤B := by
    have habs : |z.re|≤b := by simpa [z,abs_of_nonneg (ha.le.trans hd.1)] using hd.2
    simpa [z] using hWeight z habs
  have hFull : ‖bblrVStarKernel G y z‖*(1+|v|)^2≤B*D := by
    calc
      _ ≤ (‖G z‖*D)*(1+|v|)^2 := mul_le_mul_of_nonneg_right hN (by positivity)
      _ = (‖G z‖*(1+|v|)^2)*D := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hGN hD
  have hSq : 1+v^2≤(1+|v|)^2 := by nlinarith [sq_abs v,abs_nonneg v]
  have hProd := (mul_le_mul_of_nonneg_left hSq (norm_nonneg (bblrVStarKernel G y z))).trans hFull
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0<1+v^2)).mpr hProd

theorem bblrVStarKernel_vertical_integrable {y c : ℝ} (hy : 0<y) (hc : 0<c)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    Integrable (fun v : ℝ => bblrVStarKernel G y ((c:ℂ)+(v:ℂ)*I)) := by
  obtain ⟨K,_,hb⟩ := bblrVStarKernel_positive_strip_majorant hy hc le_rfl G α hG
  have hd := bblrVStarKernel_differentiableOn_rightHalfPlane hy G
    (Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1)
  have hcont : Continuous (fun v : ℝ => bblrVStarKernel G y ((c:ℂ)+(v:ℂ)*I)) :=
    hd.continuousOn.comp_continuous (by fun_prop) (fun v => by simpa using hc)
  apply (integrable_inv_one_add_sq.const_mul K).mono' hcont.aestronglyMeasurable
  exact Eventually.of_forall (fun v => hb c ⟨le_rfl,le_rfl⟩ v)

theorem bblrVStarKernel_horizontal_tendsto_zero {y a b : ℝ}
    (hy : 0<y) (ha : 0<a) (hab : a≤b)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    Tendsto (fun v : ℝ => ∫ d in a..b, bblrVStarKernel G y ((d:ℂ)+(v:ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨K,_,hbound⟩ := bblrVStarKernel_positive_strip_majorant hy ha hab G α hG
  have hlim : Tendsto (fun v : ℝ => K*|b-a| * (1+v^2)⁻¹) (cocompact ℝ) (𝓝 0) := by
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
      (tendsto_inv_atTop_zero.comp hv2).const_mul (K*|b-a|)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  exact Eventually.of_forall (fun v => by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun d => bblrVStarKernel G y ((d:ℂ)+(v:ℂ)*I))
      (C := K*(1+v^2)⁻¹) (by
        intro d hd
        rw [uIoc_of_le hab] at hd
        exact hbound d ⟨hd.1.le,hd.2⟩ v)
    exact hb.trans_eq (by ring))

theorem bblrVStar_positive_contour {y c : ℝ} (hy : 0<y) (hc : 0<c)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    bblrVStar G y=verticalIntegral c (bblrVStarKernel G y) := by
  have hd := bblrVStarKernel_differentiableOn_rightHalfPlane hy G
    (Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1)
  change verticalIntegral 1 (bblrVStarKernel G y)=_
  by_cases hc1 : c≤1
  · exact bblrRectangle_verticalIntegral_shift (bblrVStarKernel G y) hd hc1
      (fun z hz _ => hc.trans_le hz)
      (bblrVStarKernel_vertical_integrable hy hc G α hG)
      (bblrVStarKernel_vertical_integrable hy (by norm_num) G α hG)
      (bblrVStarKernel_horizontal_tendsto_zero hy hc hc1 G α hG)
  · exact (bblrRectangle_verticalIntegral_shift (bblrVStarKernel G y) hd
      (le_of_not_ge hc1) (fun z hz _ => show 0<z.re from zero_lt_one.trans_le hz)
      (bblrVStarKernel_vertical_integrable hy (by norm_num) G α hG)
      (bblrVStarKernel_vertical_integrable hy hc G α hG)
      (bblrVStarKernel_horizontal_tendsto_zero hy (by norm_num)
        (le_of_not_ge hc1) G α hG)).symm

theorem bblrGaussianVStarKernel_majorant {y c : ℝ} (hy : 0<y) (hc : 0<c)
    (T : ℝ) (σ : MomentShifts) (v : ℝ) :
    ‖bblrVStarKernel (polarPoleKiller T σ) y ((c:ℂ)+(v:ℂ)*I)‖≤
      (polarGaussianConstant T σ c/c*y^(-c))*(1+|v|)^48*Real.exp (-v^2) := by
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hCG := polarGaussianConstant_nonneg T σ c
  have hzn : c≤‖z‖ := by simpa [z,abs_of_pos hc] using Complex.abs_re_le_norm z
  have hG : ‖polarPoleKiller T σ z/z‖≤
      polarGaussianConstant T σ c/c*(1+|v|)^48*Real.exp (-v^2) := by
    rw [norm_div]
    have hCG := polarGaussianConstant_nonneg T σ c
    calc
      _ ≤ ‖polarPoleKiller T σ z‖/c := div_le_div_of_nonneg_left (norm_nonneg _) hc hzn
      _ ≤ (polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2))/c := by
        gcongr
        exact polarPoleKiller_vertical_norm_le T σ c v
      _ = _ := by ring
  have hπ : ‖(2*Real.pi:ℂ)^(-2*z)‖≤1 := by
    rw [show (2*Real.pi:ℂ)=((2*Real.pi:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<2*Real.pi)]
    have he : (-2*z).re=-2*c := by simp [z]
    rw [he]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hyw : ‖(y:ℂ)^(-z)‖=y^(-c) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    congr 1
    simp [z]
  unfold bblrVStarKernel
  rw [norm_mul,norm_mul,hyw]
  calc
    _ ≤ (polarGaussianConstant T σ c/c*(1+|v|)^48*Real.exp (-v^2))*1*y^(-c) := by
      gcongr
    _ = _ := by ring

def bblrGaussianVStarCore (c T : ℝ) (σ : MomentShifts) (x t R : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-R) R,
    bblrVStarKernel (polarPoleKiller T σ) (x/t^2) ((c:ℂ)+(v:ℂ)*I)

def bblrGaussianVStarTail (c T : ℝ) (σ : MomentShifts) (x t R : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in {v : ℝ | R < |v|},
    bblrVStarKernel (polarPoleKiller T σ) (x/t^2) ((c:ℂ)+(v:ℂ)*I)

theorem bblrGaussianVStar_core_add_tail {c x t : ℝ} (hc : 0<c) (hx : 0<x) (ht : t≠0)
    (T : ℝ) (σ : MomentShifts) (R : ℝ) :
    bblrVStar (polarPoleKiller T σ) (x/t^2)=
      bblrGaussianVStarCore c T σ x t R+bblrGaussianVStarTail c T σ x t R := by
  have hy : 0<x/t^2 := div_pos hx (sq_pos_of_ne_zero ht)
  have hG := polarPoleKiller_BBLREntireWeight T σ (0 : MomentShifts)
  have hi := bblrVStarKernel_vertical_integrable hy hc _ _ hG
  have hs : MeasurableSet {v : ℝ | R < |v|} := (isOpen_lt continuous_const continuous_abs).measurableSet
  have he := integral_add_compl hs hi
  have hset : {v : ℝ | R < |v|}ᶜ=Icc (-R) R := by
    ext v
    simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_lt,Set.mem_Icc]
    exact abs_le
  rw [hset] at he
  rw [bblrVStar_positive_contour hy hc _ _ hG]
  unfold verticalIntegral bblrGaussianVStarCore bblrGaussianVStarTail
  rw [←he]
  ring

theorem bblrGaussianVStar_norm_le {y c : ℝ} (hy : 0<y) (hc : 0<c)
    (T : ℝ) (σ : MomentShifts) :
    ‖bblrVStar (polarPoleKiller T σ) y‖≤
      (gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ c/c*y^(-c) := by
  have hCG := polarGaussianConstant_nonneg T σ c
  have hpoint : ∀ v : ℝ, ‖bblrVStarKernel (polarPoleKiller T σ) y ((c:ℂ)+(v:ℂ)*I)‖≤
      (polarGaussianConstant T σ c/c*y^(-c))*((1+|v|)^48*Real.exp (-(1/2)*v^2)) := by
    intro v
    calc
      _ ≤ (polarGaussianConstant T σ c/c*y^(-c))*(1+|v|)^48*Real.exp (-v^2) :=
        bblrGaussianVStarKernel_majorant hy hc T σ v
      _ ≤ (polarGaussianConstant T σ c/c*y^(-c))*(1+|v|)^48*Real.exp (-(1/2)*v^2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg v])) (by positivity)
      _ = _ := by ring
  have hb := norm_integral_le_of_norm_le
    ((gaussian_polynomial_half_integrable 48).const_mul (polarGaussianConstant T σ c/c*y^(-c)))
    (Eventually.of_forall hpoint)
  rw [bblrVStar_positive_contour hy hc _ _ (polarPoleKiller_BBLREntireWeight T σ (0 : MomentShifts))]
  unfold verticalIntegral
  rw [norm_mul,show ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]]
  calc
    _ ≤ (1/(2*Real.pi))*(∫ v : ℝ, (polarGaussianConstant T σ c/c*y^(-c))*
        ((1+|v|)^48*Real.exp (-(1/2)*v^2))) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [integral_const_mul]; dsimp [gaussianTailConstant]; ring

theorem bblrGaussianVStarTail_norm_le {c x t R : ℝ}
    (hc : 0<c) (hx : 0<x) (ht : t≠0) (hR : 0≤R) (T : ℝ) (σ : MomentShifts) :
    ‖bblrGaussianVStarTail c T σ x t R‖≤
      (gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ c/c*
        (x/t^2)^(-c)*Real.exp (-(1/2)*R^2) := by
  have hy : 0<x/t^2 := div_pos hx (sq_pos_of_ne_zero ht)
  have hCG := polarGaussianConstant_nonneg T σ c
  have hi := bblrVStarKernel_vertical_integrable hy hc _ _
    (polarPoleKiller_BBLREntireWeight T σ (0 : MomentShifts))
  have hb := gaussian_integral_tail_norm_le
    (fun v : ℝ => bblrVStarKernel (polarPoleKiller T σ) (x/t^2) ((c:ℂ)+(v:ℂ)*I))
    hi 48 (by positivity : 0≤polarGaussianConstant T σ c/c*(x/t^2)^(-c)) hR
    (fun v => bblrGaussianVStarKernel_majorant hy hc T σ v)
  unfold bblrGaussianVStarTail
  rw [norm_mul,show ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]]
  calc
    _ ≤ (1/(2*Real.pi))*((polarGaussianConstant T σ c/c*(x/t^2)^(-c))*
        gaussianTailConstant 48*Real.exp (-(1/2)*R^2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end
end Sechstmoment.Source
