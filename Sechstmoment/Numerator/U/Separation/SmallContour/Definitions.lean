import Sechstmoment.Numerator.U.Separation.PositiveVContour

namespace Sechstmoment.Source
open Real Complex MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem bblrVKernel_small_positive_strip_majorant {t x a : ℝ}
    (ht : 0 ≤ t) (hx : 0 < x) (ha : 0 < a) (_ha1 : a ≤ 1)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d ∈ Icc a 1, ∀ v : ℝ,
      ‖bblrVKernel G α x t ((d:ℂ)+(v:ℂ)*I)‖ ≤ K*(1+v^2)⁻¹ := by
  obtain ⟨C,hC,hGamma⟩ := bblrGammaQuotient_polynomial_positive_strip_bound
  obtain ⟨B,hB,hWeight⟩ := hG.2.2.2 1 (by norm_num) 10
  let Q := 1+Real.pi^(-2:ℝ)
  let X := 1+x^(-1:ℝ)
  let D := a⁻¹*(C*(2+t)^8)*Q*X
  have hD : 0 ≤ D := by dsimp [D,Q,X]; positivity
  refine ⟨B*D,mul_nonneg hB hD,?_⟩
  intro d hd v
  let z : ℂ := (d:ℂ)+(v:ℂ)*I
  let W : ℝ := 1+|v|
  have hW : 1 ≤ W := by dsimp [W]; linarith [abs_nonneg v]
  have hzre : z.re = d := by simp [z]
  have hzim : z.im = v := by simp [z]
  have hzstrip : z.re ∈ Icc (0:ℝ) 1 := by rw [hzre]; exact ⟨ha.le.trans hd.1,hd.2⟩
  have hQ : ‖(Real.pi:ℂ)^(-2*z)‖ ≤ Q := by
    simpa [Q] using positiveReal_cpow_norm_positive_strip_bound Real.pi_pos (-2) hzstrip
  have hX : ‖(x:ℂ)^(-z)‖ ≤ X := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using
      positiveReal_cpow_norm_positive_strip_bound hx (-1) hzstrip
  have hGammaN : ‖bblrGammaQuotient t α z‖ ≤ C*(2+t)^8*W^8 := by
    apply (hGamma t v d ht (ha.le.trans hd.1) hd.2 α hα).trans
    rw [mul_assoc,← mul_pow]
    gcongr
    dsimp [W]
    nlinarith [abs_nonneg v]
  have hInv : ‖z‖⁻¹ ≤ a⁻¹ := by
    apply inv_anti₀ ha
    exact hd.1.trans (by rw [← hzre]; exact Complex.re_le_norm z)
  have hN : ‖bblrVKernel G α x t z‖ ≤ ‖G z‖*D*W^8 := by
    unfold bblrVKernel
    simp only [norm_mul,norm_div]
    rw [div_eq_mul_inv]
    calc
      _ ≤ (‖G z‖*a⁻¹)*((C*(2+t)^8)*W^8)*Q*X := by
        gcongr
      _ = _ := by dsimp [D]; ring
  have hGN : ‖G z‖*W^10 ≤ B := by
    have habs : |z.re| ≤ 1 := by
      rw [hzre,abs_of_nonneg (ha.le.trans hd.1)]
      exact hd.2
    simpa only [hzim] using hWeight z habs
  have hFull : ‖bblrVKernel G α x t z‖*W^2 ≤ B*D := by
    calc
      _ ≤ (‖G z‖*D*W^8)*W^2 := mul_le_mul_of_nonneg_right hN (sq_nonneg W)
      _ = (‖G z‖*W^10)*D := by rw [show (10:ℕ)=8+2 by norm_num,pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hGN hD
  have hSq : 1+v^2 ≤ W^2 := by dsimp [W]; nlinarith only [sq_abs v,abs_nonneg v]
  have hProd : ‖bblrVKernel G α x t z‖*(1+v^2) ≤ B*D :=
    (mul_le_mul_of_nonneg_left hSq (norm_nonneg _)).trans hFull
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0<1+v^2)).mpr hProd

theorem bblrVKernel_small_vertical_continuous {t x c : ℝ}
    (_ht : 0 ≤ t) (hx : 0 < x) (hc : 0 < c)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    Continuous (fun v : ℝ => bblrVKernel G α x t ((c:ℂ)+(v:ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hd := bblrVKernel_differentiableOn_rightHalfPlane hx G hG α hα t
  have hz : ((c:ℂ)+(v:ℂ)*I) ∈ {z : ℂ | 0<z.re} := by simpa using hc
  exact (hd.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)).continuousAt.comp
      (f := fun w : ℝ => (c:ℂ)+(w:ℂ)*I) (by fun_prop)

theorem bblrVKernel_small_vertical_integrable {t x c : ℝ}
    (ht : 0 ≤ t) (hx : 0 < x) (hc : 0 < c) (hc1 : c ≤ 1)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    Integrable (fun v : ℝ => bblrVKernel G α x t ((c:ℂ)+(v:ℂ)*I)) := by
  obtain ⟨K,_,hbound⟩ := bblrVKernel_small_positive_strip_majorant ht hx hc hc1 G α hG hα
  apply (integrable_inv_one_add_sq.const_mul K).mono'
  · exact (bblrVKernel_small_vertical_continuous ht hx hc G
      (Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1) α hα).aestronglyMeasurable
  · exact Eventually.of_forall (fun v => hbound c ⟨le_rfl,hc1⟩ v)

theorem bblrVKernel_small_horizontal_integral_tendsto_zero {t x c : ℝ}
    (ht : 0 ≤ t) (hx : 0 < x) (hc : 0 < c) (hc1 : c ≤ 1)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    Tendsto (fun v : ℝ => ∫ d in c..1,
      bblrVKernel G α x t ((d:ℂ)+(v:ℂ)*I)) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨K,_,hbound⟩ := bblrVKernel_small_positive_strip_majorant ht hx hc hc1 G α hG hα
  have hlim : Tendsto (fun v : ℝ => K * |1-c| * (1+v^2)⁻¹) (cocompact ℝ) (𝓝 0) := by
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
      (tendsto_inv_atTop_zero.comp hv2).const_mul (K * |1-c|)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  exact Eventually.of_forall (fun v => by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c) (b := 1)
      (f := fun d => bblrVKernel G α x t ((d:ℂ)+(v:ℂ)*I))
      (C := K*(1+v^2)⁻¹) (by
        intro d hd
        rw [uIoc_of_le hc1] at hd
        exact hbound d ⟨hd.1.le,hd.2⟩ v)
    exact hb.trans_eq (by ring))

theorem bblrV_small_positive_contour {t x c : ℝ}
    (ht : 0 ≤ t) (hx : 0 < x) (hc : 0 < c) (hc1 : c ≤ 1)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    bblrV G α x t =
      verticalIntegral c (bblrVKernel G α x t) := by
  apply bblrRectangle_verticalIntegral_shift
    (bblrVKernel G α x t)
    (bblrVKernel_differentiableOn_rightHalfPlane hx G
      (Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1) α hα t) hc1
  · intro z hz _
    exact hc.trans_le hz
  · exact bblrVKernel_small_vertical_integrable ht hx hc hc1 G α hG hα
  · exact bblrVKernel_small_vertical_integrable ht hx (by norm_num) le_rfl G α hG hα
  · exact bblrVKernel_small_horizontal_integral_tendsto_zero ht hx hc hc1 G α hG hα


end
end Sechstmoment.Source
