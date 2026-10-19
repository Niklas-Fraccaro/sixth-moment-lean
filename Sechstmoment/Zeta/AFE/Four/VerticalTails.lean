import Mathlib.MeasureTheory.Integral.Bochner.Set
import Sechstmoment.Zeta.AFE.Four.FourDirichlet
import Sechstmoment.Zeta.AFE.Four.HorizontalDecay

/-!
# Quantitative tails of the original BBLR Mellin line

The estimate is obtained from an integrable weighted moment. No limiting
contour argument or approximate functional equation is assumed.
-/

namespace Sechstmoment.Source
open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

/-- A weighted-moment bound controls the difference between a full integral
and its truncation to `[-t/2,t/2]`. -/
theorem integral_sub_truncation_norm_le_of_weighted_moment
    (F : ℝ → ℂ) (W : ℝ → ℝ) (hF : Integrable F) (hW : Integrable W)
    (hW0 : ∀ v, 0 ≤ W v) (A : ℕ) (t : ℝ) (ht : 0 < t)
    (hbound : ∀ v, t/2 ≤ |v| → ‖F v‖*t^A ≤ W v) :
    ‖(∫ v : ℝ, F v) - ∫ v in Icc (-t/2) (t/2), F v‖ ≤
      (∫ v : ℝ, W v)*t^(-(A : ℝ)) := by
  have htp : 0 < t^A := pow_pos ht A
  rw [← setIntegral_compl measurableSet_Icc hF]
  calc
    _ ≤ ∫ v in (Icc (-t/2) (t/2))ᶜ, ‖F v‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v in (Icc (-t/2) (t/2))ᶜ, W v/t^A := by
      apply setIntegral_mono_on hF.norm.integrableOn
        (hW.div_const (t^A)).integrableOn measurableSet_Icc.compl
      intro v hv
      have hv' : t/2 ≤ |v| := by
        by_contra hn
        have ha := abs_le.mp (le_of_lt (lt_of_not_ge hn))
        exact hv (by constructor <;> linarith [ha.1, ha.2])
      exact (le_div_iff₀ htp).mpr (hbound v hv')
    _ ≤ ∫ v : ℝ, W v/t^A :=
      setIntegral_le_integral (hW.div_const _) (Eventually.of_forall
        (fun v => div_nonneg (hW0 v) htp.le))
    _ = _ := by
      rw [integral_div, Real.rpow_neg ht.le, Real.rpow_natCast, div_eq_mul_inv]

/-- Every natural weighted moment of the fixed auxiliary function on the
original line is integrable. The decay estimate of order `m+2` suffices. -/
theorem fixedAFE_entireWeight_line_moment_integrable
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0)) (m : ℕ) :
    Integrable (fun v : ℝ => ‖G (1+(v : ℂ)*I)‖*(1+|v|)^m) := by
  obtain ⟨C,hC,hbound⟩ := hG.2.2.2 1 (by norm_num) (m+2)
  have hc : Continuous (fun v : ℝ => ‖G (1+(v : ℂ)*I)‖*(1+|v|)^m) :=
    (hG.1.continuous.comp (by fun_prop)).norm.mul (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun v => by
    rw [Real.norm_of_nonneg (by positivity)]
    have hb : ‖G (1+(v : ℂ)*I)‖*(1+|v|)^(m+2) ≤ C := by
      simpa using hbound (1+(v : ℂ)*I) (by simp)
    have hquad : 1+v^2 ≤ (1+|v|)^2 := by
      nlinarith [abs_nonneg v, sq_abs v]
    have hm : (‖G (1+(v : ℂ)*I)‖*(1+|v|)^m)*(1+v^2) ≤ C := by
      calc
        _ ≤ (‖G (1+(v : ℂ)*I)‖*(1+|v|)^m)*(1+|v|)^2 := by
          gcongr
        _ = ‖G (1+(v : ℂ)*I)‖*(1+|v|)^(m+2) := by rw [pow_add]; ring
        _ ≤ C := hb
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 1+v^2)).mpr hm

/-- A uniform constant bounds the actual four zeta factors on the entire
original AFE line, because all four real parts are at least `5/4`. -/
theorem bblrZetaProduct_uniform_right_line_bound
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) (t v : ℝ) :
    ‖∏ j : Fin 4, riemannZeta
      (sourceZetaPoints t j+α j+(1+(v : ℂ)*I))‖ ≤
        (zetaDirichletMajorant (5/4))^4 := by
  simpa using finiteRiemannZetaProduct_norm_le_dirichlet Finset.univ
    (fun j : Fin 4 => sourceZetaPoints t j+α j+(1+(v : ℂ)*I))
    (b := 5/4) (by norm_num) (by
      intro j hj
      have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_self, sourceZetaPoints_re, add_zero]
      linarith)

/-- A global polynomial bound for the complete explicit right-line
integrand; its constant is independent of both height and small shifts. -/
theorem bblrExplicitAFEIntegrand_polynomial_right_line_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ G : ℂ → ℂ, ∀ t v : ℝ, 0 ≤ t →
      ∀ α : MomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
      ‖bblrExplicitAFEIntegrand G α t (1+(v : ℂ)*I)‖ ≤
        D*‖G (1+(v : ℂ)*I)‖*(2+t+|v|)^8 := by
  obtain ⟨CΓ,hCΓ,hΓ⟩ := bblrGammaQuotient_polynomial_line_bound
  let B : ℝ := (zetaDirichletMajorant (5/4))^4
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨CΓ*B*Real.pi^(-2 : ℝ), by positivity, ?_⟩
  intro G t v ht α hα
  let z : ℂ := 1+(v : ℂ)*I
  have hz : 1 ≤ ‖z‖ := by
    simpa [z] using Complex.abs_re_le_norm z
  have hdiv : ‖G z/z‖ ≤ ‖G z‖ := by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hz
  have hπ : ‖(Real.pi : ℂ)^(-2*z)‖ = Real.pi^(-2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp [z]
  have hζ : ‖∏ j : Fin 4, riemannZeta (sourceZetaPoints t j+α j+z)‖ ≤ B :=
    bblrZetaProduct_uniform_right_line_bound α hα t v
  have hΓ' := hΓ t v ht α hα
  change ‖G z/z*(bblrGammaQuotient t α z*
      ∏ j : Fin 4, riemannZeta (sourceZetaPoints t j+α j+z))*
        (Real.pi : ℂ)^(-2*z)‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul, hπ]
  calc
    _ ≤ ‖G z‖*((CΓ*(2+t+|v|)^8)*B)*Real.pi^(-2 : ℝ) := by gcongr
    _ = _ := by ring

/-- Actual integrability of the full right-line explicit integrand. -/
theorem bblrExplicitAFEIntegrand_right_integrable
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0))
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) (t : ℝ) :
    Integrable (fun v : ℝ => bblrExplicitAFEIntegrand G α t (1+(v : ℂ)*I)) := by
  have hα' (j : Fin 4) : -1/2 < (α j).re := by
    have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
    linarith
  have hF := fixedAFEWeightOnLine_integrable G hG α t hα'
  have hc : Continuous (fun v : ℝ => ∏ j : Fin 4, riemannZeta
      (sourceZetaPoints t j+α j+(1+(v : ℂ)*I))) := by
    apply continuous_finsetProd
    intro j hj
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (differentiableAt_riemannZeta ?_).continuousAt.comp (by fun_prop)
    intro heq
    have hr := congrArg Complex.re heq
    have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
    simp at hr
    linarith
  apply (hF.norm.mul_const ((zetaDirichletMajorant (5/4))^4)).mono'
    ?_ (Eventually.of_forall (fun v => ?_))
  · have he : (fun v : ℝ => bblrExplicitAFEIntegrand G α t (1+(v : ℂ)*I)) =
        fun v => fixedAFEWeightOnLine G α t v * ∏ j : Fin 4, riemannZeta
          (sourceZetaPoints t j+α j+(1+(v : ℂ)*I)) := by
      funext v
      unfold bblrExplicitAFEIntegrand fixedAFEWeightOnLine
      dsimp only
      ring
    rw [he]
    exact hF.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · have he : bblrExplicitAFEIntegrand G α t (1+(v : ℂ)*I) =
        fixedAFEWeightOnLine G α t v * ∏ j : Fin 4, riemannZeta
          (sourceZetaPoints t j+α j+(1+(v : ℂ)*I)) := by
      unfold bblrExplicitAFEIntegrand fixedAFEWeightOnLine
      dsimp only
      ring
    rw [he, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (bblrZetaProduct_uniform_right_line_bound α hα t v) (norm_nonneg _)

/-- Arbitrary inverse-polynomial decay of the two omitted right-line tails,
uniform in height and all four small shifts. -/
theorem bblrExplicitAFEIntegrand_right_tail
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 16 ≤ t →
      ∀ α : MomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
      ‖(∫ v : ℝ, bblrExplicitAFEIntegrand G α t (1+(v : ℂ)*I)) -
        ∫ v in Icc (-t/2) (t/2), bblrExplicitAFEIntegrand G α t (1+(v : ℂ)*I)‖ ≤
          C*t^(-(A : ℝ)) := by
  obtain ⟨D,hD,hbound⟩ := bblrExplicitAFEIntegrand_polynomial_right_line_bound
  let W : ℝ → ℝ := fun v =>
    (D*3^8*2^A)*(‖G (1+(v : ℂ)*I)‖*(1+|v|)^(A+8))
  have hW : Integrable W :=
    (fixedAFE_entireWeight_line_moment_integrable G hG (A+8)).const_mul _
  have hW0 (v : ℝ) : 0 ≤ W v := by dsimp [W]; positivity
  refine ⟨∫ v : ℝ, W v, integral_nonneg hW0, ?_⟩
  intro t ht α hα
  apply integral_sub_truncation_norm_le_of_weighted_moment _ W
    (bblrExplicitAFEIntegrand_right_integrable G hG α hα t) hW hW0 A t
    (by linarith)
  intro v hv
  have ht0 : 0 ≤ t := by linarith
  have hP : 2+t+|v| ≤ 3*(1+|v|) := by linarith
  have htP : t ≤ 2*(1+|v|) := by linarith
  calc
    _ ≤ (D*‖G (1+(v : ℂ)*I)‖*(2+t+|v|)^8)*t^A := by
      gcongr
      exact hbound G t v ht0 α hα
    _ ≤ (D*‖G (1+(v : ℂ)*I)‖*(3*(1+|v|))^8)*
        (2*(1+|v|))^A := by gcongr
    _ = W v := by dsimp [W]; rw [mul_pow, mul_pow, pow_add]; ring

/-- The same tail estimate with the actual Mellin normalization. -/
theorem bblrExplicitAFEIntegral_right_tail
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 16 ≤ t →
      ∀ α : MomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
      ‖verticalIntegral 1 (bblrExplicitAFEIntegrand G α t) -
        (1/(2*Real.pi) : ℂ)*∫ v in Icc (-t/2) (t/2),
          bblrExplicitAFEIntegrand G α t (1+(v : ℂ)*I)‖ ≤
            C*t^(-(A : ℝ)) := by
  obtain ⟨D,hD,hbound⟩ := bblrExplicitAFEIntegrand_right_tail G hG A
  refine ⟨‖(1/(2*Real.pi) : ℂ)‖*D, mul_nonneg (norm_nonneg _) hD, ?_⟩
  intro t ht α hα
  unfold verticalIntegral
  rw [← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_left (hbound t ht α hα) (norm_nonneg _)).trans_eq
    (mul_assoc ..).symm

/-- The actual completed kernel equals the explicit Gamma/zeta integrand on
the whole right line. -/
theorem fixedAFECompletedKernel_right_eq_explicit
    (G : ℂ → ℂ) (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) (t v : ℝ) :
    fixedAFECompletedKernel G α t (1+(v : ℂ)*I)/(1+(v : ℂ)*I) =
      bblrExplicitAFEIntegrand G α t (1+(v : ℂ)*I) := by
  rw [fixedAFECompletedKernel_div_eq_gamma_zeta G α t _ (by
    intro j
    have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
    simp only [fixedAFEShiftedPoint, Complex.add_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self,
      sourceZetaPoints_re, add_zero]
    linarith)]
  unfold bblrExplicitAFEIntegrand
  ring

/-- Quantitative tail estimate for the completed kernel used by the finite
rectangle argument. -/
theorem fixedAFECompletedIntegral_right_tail
    (G : ℂ → ℂ) (hG : BBLREntireWeight G (fun _ => 0)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 16 ≤ t →
      ∀ α : MomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
      ‖verticalIntegral 1 (fun z => fixedAFECompletedKernel G α t z/z) -
        (1/(2*Real.pi) : ℂ)*∫ v in Icc (-t/2) (t/2),
          fixedAFECompletedKernel G α t (1+(v : ℂ)*I)/(1+(v : ℂ)*I)‖ ≤
            C*t^(-(A : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := bblrExplicitAFEIntegral_right_tail G hG A
  refine ⟨C,hC,?_⟩
  intro t ht α hα
  simpa only [verticalIntegral, Complex.ofReal_one,
    fixedAFECompletedKernel_right_eq_explicit G α hα t] using hbound t ht α hα

end
end Sechstmoment.Source
