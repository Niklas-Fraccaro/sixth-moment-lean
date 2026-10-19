import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic
import Sechstmoment.Analysis.Complex.ContourShift
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEGrouping
import Sechstmoment.Numerator.U.Replacement.GaussianAdmissible
import Sechstmoment.Zeta.AFE.Four.GammaRemainder
import Sechstmoment.Zeta.Gamma.PositiveStrip

/-!
# The genuine positive contour movement for the Gamma weight difference

The global Gamma strip estimate and the actual rapid strip decay of the
auxiliary weight prove all boundary hypotheses of rectangle Cauchy. The
literal source weights are identified by positive-real complex-power laws.
-/

namespace Sechstmoment.Source
open Real Complex MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem positiveReal_cpow_norm_positive_strip_bound {a : ℝ} (ha : 0 < a)
    (k : ℝ) {z : ℂ} (hz : z.re ∈ Icc (0:ℝ) 1) :
    ‖(a:ℂ)^((k:ℂ)*z)‖ ≤ 1+a^k := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]
  have he : ((k:ℂ)*z).re = k*z.re := by simp
  rw [he,Real.rpow_def_of_pos ha,Real.rpow_def_of_pos ha]
  by_cases hL : 0 ≤ Real.log a*k
  · have hp : Real.log a*(k*z.re) ≤ Real.log a*k := by nlinarith [hz.2]
    exact (Real.exp_le_exp.mpr hp).trans (by linarith [Real.exp_pos (Real.log a*k)])
  · have hp : Real.log a*(k*z.re) ≤ 0 := by nlinarith [hz.1]
    exact (Real.exp_le_exp.mpr hp).trans (by simp; positivity)

theorem bblr_main_positive_cpow_identity {t x : ℝ} (ht : 0 < t) (hx : 0 < x)
    (z : ℂ) :
    (t/2:ℂ)^(2*z)*(Real.pi:ℂ)^(-2*z)*(x:ℂ)^(-z) =
      (2*Real.pi:ℂ)^(-2*z)*(x/t^2:ℂ)^(-z) := by
  have hhalf : 0 < t/2 := by positivity
  have htwoPi : 0 < 2*Real.pi := by positivity
  have hxscale : 0 < x/t^2 := by positivity
  have hhalfne : (t/2:ℂ) ≠ 0 := by exact_mod_cast hhalf.ne'
  have hpine : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have h2pine : (2*Real.pi:ℂ) ≠ 0 := by exact_mod_cast htwoPi.ne'
  have hscne : (x/t^2:ℂ) ≠ 0 := by exact_mod_cast hxscale.ne'
  have hloghalf : Complex.log (t/2:ℂ) = ((Real.log t-Real.log 2:ℝ):ℂ) := by
    rw [show (t/2:ℂ) = ((t/2:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_log hhalf.le,Real.log_div ht.ne' (by norm_num)]
  have hlogpi : Complex.log (Real.pi:ℂ) = (Real.log Real.pi:ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  have hlogx : Complex.log (x:ℂ) = (Real.log x:ℂ) := (Complex.ofReal_log hx.le).symm
  have hlog2pi : Complex.log (2*Real.pi:ℂ) = ((Real.log 2+Real.log Real.pi:ℝ):ℂ) := by
    rw [show (2*Real.pi:ℂ) = ((2*Real.pi:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_log htwoPi.le,Real.log_mul (by norm_num) Real.pi_ne_zero]
  have hlogscale : Complex.log (x/t^2:ℂ) = ((Real.log x-2*Real.log t:ℝ):ℂ) := by
    rw [show (x/t^2:ℂ) = ((x/t^2:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_log hxscale.le,Real.log_div hx.ne' (pow_ne_zero 2 ht.ne'),Real.log_pow]
    norm_num
  simp only [Complex.cpow_def_of_ne_zero hhalfne,Complex.cpow_def_of_ne_zero hpine,
    Complex.cpow_def_of_ne_zero hxne,Complex.cpow_def_of_ne_zero h2pine,
    Complex.cpow_def_of_ne_zero hscne,hloghalf,hlogpi,hlogx,hlog2pi,hlogscale]
  rw [← Complex.exp_add,← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem polarPoleKiller_BBLREntireWeight (T : ℝ) (σ α : MomentShifts) :
    BBLREntireWeight (polarPoleKiller T σ) α := by
  refine ⟨Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (polarPoleKiller_differentiable T σ),polarPoleKiller_even T σ,
    polarPoleKiller_zero T σ,?_⟩
  intro R hR N
  choose C hC hbound using (fun i : Fin 25 => fixedGaussianBasis_rapid_strip i R hR N)
  refine ⟨∑ i : Fin 25, ‖polarPoleBasisWeights T σ i‖*C i,
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hC i)),?_⟩
  intro z hz
  rw [polarPoleKiller_fixed_basis]
  unfold finiteAuxiliaryCombination
  calc
    _ ≤ (∑ i : Fin 25, ‖polarPoleBasisWeights T σ i*fixedGaussianBasis i z‖)*
        (1+|z.im|)^N := mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ = ∑ i : Fin 25, ‖polarPoleBasisWeights T σ i‖*
        (‖fixedGaussianBasis i z‖*(1+|z.im|)^N) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_mul,mul_assoc]
    _ ≤ _ := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hbound i z hz) (norm_nonneg _))

theorem bblrCentralWeightDifference_positive_strip_majorant {t x a : ℝ}
    (ht : 0 < t) (hx : 0 < x) (ha : 0 < a) (_ha1 : a ≤ 1)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d ∈ Icc a 1, ∀ v : ℝ,
      ‖bblrCentralWeightDifference G t α x ((d:ℂ)+(v:ℂ)*I)‖ ≤ K*(1+v^2)⁻¹ := by
  obtain ⟨C,hC,hGamma⟩ := bblrGammaQuotient_polynomial_positive_strip_bound
  obtain ⟨B,hB,hWeight⟩ := hG.2.2.2 1 (by norm_num) 10
  let P := 1+(t/2)^(2:ℝ)
  let Q := 1+Real.pi^(-2:ℝ)
  let X := 1+x^(-1:ℝ)
  let D := a⁻¹*(C*(2+t)^8+P)*Q*X
  have hD : 0 ≤ D := by dsimp [D,P,Q,X]; positivity
  refine ⟨B*D,mul_nonneg hB hD,?_⟩
  intro d hd v
  let z : ℂ := (d:ℂ)+(v:ℂ)*I
  let W : ℝ := 1+|v|
  have hW : 1 ≤ W := by dsimp [W]; linarith [abs_nonneg v]
  have hzre : z.re = d := by simp [z]
  have hzim : z.im = v := by simp [z]
  have hzstrip : z.re ∈ Icc (0:ℝ) 1 := by rw [hzre]; exact ⟨ha.le.trans hd.1,hd.2⟩
  have hP : ‖(t/2:ℂ)^(2*z)‖ ≤ P := by
    simpa [P] using positiveReal_cpow_norm_positive_strip_bound (by positivity : 0<t/2) 2 hzstrip
  have hQ : ‖(Real.pi:ℂ)^(-2*z)‖ ≤ Q := by
    simpa [Q] using positiveReal_cpow_norm_positive_strip_bound Real.pi_pos (-2) hzstrip
  have hX : ‖(x:ℂ)^(-z)‖ ≤ X := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using
      positiveReal_cpow_norm_positive_strip_bound hx (-1) hzstrip
  have hGammaN : ‖bblrGammaQuotient t α z‖ ≤ C*(2+t)^8*W^8 := by
    apply (hGamma t v d ht.le (ha.le.trans hd.1) hd.2 α hα).trans
    rw [mul_assoc,← mul_pow]
    gcongr
    dsimp [W]
    nlinarith [abs_nonneg v]
  have hSub : ‖bblrGammaQuotient t α z-(t/2:ℂ)^(2*z)‖ ≤
      (C*(2+t)^8+P)*W^8 := by
    refine (norm_sub_le _ _).trans ?_
    have hP0 : 0 ≤ P := by dsimp [P]; positivity
    have hW8 : 1 ≤ W^8 := one_le_pow₀ hW
    calc
      _ ≤ C*(2+t)^8*W^8+P := add_le_add hGammaN hP
      _ ≤ C*(2+t)^8*W^8+P*W^8 := add_le_add le_rfl
        (by simpa using mul_le_mul_of_nonneg_left hW8 hP0)
      _ = _ := by ring
  have hInv : ‖z‖⁻¹ ≤ a⁻¹ := by
    apply inv_anti₀ ha
    exact hd.1.trans (by rw [← hzre]; exact Complex.re_le_norm z)
  have hN : ‖bblrCentralWeightDifference G t α x z‖ ≤ ‖G z‖*D*W^8 := by
    unfold bblrCentralWeightDifference
    simp only [norm_mul,norm_div]
    rw [div_eq_mul_inv]
    calc
      _ ≤ (‖G z‖*a⁻¹)*((C*(2+t)^8+P)*W^8)*Q*X := by
        gcongr
      _ = _ := by dsimp [D]; ring
  have hGN : ‖G z‖*W^10 ≤ B := by
    have habs : |z.re| ≤ 1 := by
      rw [hzre,abs_of_nonneg (ha.le.trans hd.1)]
      exact hd.2
    simpa only [hzim] using hWeight z habs
  have hFull : ‖bblrCentralWeightDifference G t α x z‖*W^2 ≤ B*D := by
    calc
      _ ≤ (‖G z‖*D*W^8)*W^2 := mul_le_mul_of_nonneg_right hN (sq_nonneg W)
      _ = (‖G z‖*W^10)*D := by rw [show (10:ℕ)=8+2 by norm_num,pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hGN hD
  have hSq : 1+v^2 ≤ W^2 := by dsimp [W]; nlinarith only [sq_abs v,abs_nonneg v]
  have hProd : ‖bblrCentralWeightDifference G t α x z‖*(1+v^2) ≤ B*D :=
    (mul_le_mul_of_nonneg_left hSq (norm_nonneg _)).trans hFull
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0<1+v^2)).mpr hProd

theorem bblrCentralWeightDifference_vertical_continuous {t x c : ℝ}
    (ht : 0 < t) (hx : 0 < x) (hc : 0 < c)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    Continuous (fun v : ℝ => bblrCentralWeightDifference G t α x ((c:ℂ)+(v:ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hd := bblrCentralWeightDifference_differentiableOn_rightHalfPlane ht hx G hG α hα
  have hz : ((c:ℂ)+(v:ℂ)*I) ∈ {z : ℂ | 0<z.re} := by simpa using hc
  exact (hd.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)).continuousAt.comp
      (f := fun w : ℝ => (c:ℂ)+(w:ℂ)*I) (by fun_prop)

theorem bblrCentralWeightDifference_vertical_integrable {t x c : ℝ}
    (ht : 0 < t) (hx : 0 < x) (hc : 0 < c) (hc1 : c ≤ 1)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    Integrable (fun v : ℝ => bblrCentralWeightDifference G t α x ((c:ℂ)+(v:ℂ)*I)) := by
  obtain ⟨K,_,hbound⟩ := bblrCentralWeightDifference_positive_strip_majorant ht hx hc hc1 G α hG hα
  apply (integrable_inv_one_add_sq.const_mul K).mono'
  · exact (bblrCentralWeightDifference_vertical_continuous ht hx hc G
      (Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1) α hα).aestronglyMeasurable
  · exact Eventually.of_forall (fun v => hbound c ⟨le_rfl,hc1⟩ v)

theorem bblrCentralWeightDifference_horizontal_integral_tendsto_zero {t x c : ℝ}
    (ht : 0 < t) (hx : 0 < x) (hc : 0 < c) (hc1 : c ≤ 1)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    Tendsto (fun v : ℝ => ∫ d in c..1,
      bblrCentralWeightDifference G t α x ((d:ℂ)+(v:ℂ)*I)) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨K,_,hbound⟩ := bblrCentralWeightDifference_positive_strip_majorant ht hx hc hc1 G α hG hα
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
      (f := fun d => bblrCentralWeightDifference G t α x ((d:ℂ)+(v:ℂ)*I))
      (C := K*(1+v^2)⁻¹) (by
        intro d hd
        rw [uIoc_of_le hc1] at hd
        exact hbound d ⟨hd.1.le,hd.2⟩ v)
    exact hb.trans_eq (by ring))

theorem bblrCentralWeightDifference_verticalIntegral_shift {t x c : ℝ}
    (ht : 0 < t) (hx : 0 < x) (hc : 0 < c) (hc1 : c ≤ 1)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    verticalIntegral 1 (bblrCentralWeightDifference G t α x) =
      verticalIntegral c (bblrCentralWeightDifference G t α x) := by
  apply bblrRectangle_verticalIntegral_shift
    (bblrCentralWeightDifference G t α x)
    (bblrCentralWeightDifference_differentiableOn_rightHalfPlane ht hx G
      (Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1) α hα) hc1
  · intro z hz _
    exact hc.trans_le hz
  · exact bblrCentralWeightDifference_vertical_integrable ht hx hc hc1 G α hG hα
  · exact bblrCentralWeightDifference_vertical_integrable ht hx (by norm_num) le_rfl G α hG hα
  · exact bblrCentralWeightDifference_horizontal_integral_tendsto_zero ht hx hc hc1 G α hG hα

theorem bblrV_sub_bblrVStar_eq_centralWeightDifference {t x : ℝ}
    (ht : 0 < t) (hx : 0 < x)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    bblrV G α x t-bblrVStar G (x/t^2) =
      verticalIntegral 1 (bblrCentralWeightDifference G t α x) := by
  have hID := bblrCentralWeightDifference_vertical_integrable ht hx
    (by norm_num : (0:ℝ)<1) le_rfl G α hG hα
  have hreal (j : Fin 4) : -1/2 < (α j).re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
    linarith
  have hIV := bblrVerticalIntegrand_integrable G (continuousOn_univ.mp hG.1.continuousOn)
    (rectangular_BBLR_weight_vertical_integrable G α hG) α x t hx hreal
  let S : ℂ → ℂ := fun z => G z/z*(2*Real.pi:ℂ)^(-2*z)*(x/t^2:ℂ)^(-z)
  have hPoint (z : ℂ) :
      G z/z*bblrGammaQuotient t α z*(Real.pi:ℂ)^(-2*z)*(x:ℂ)^(-z)-S z =
        bblrCentralWeightDifference G t α x z := by
    unfold S bblrCentralWeightDifference
    rw [show G z/z*(2*Real.pi:ℂ)^(-2*z)*(x/t^2:ℂ)^(-z) =
      G z/z*((2*Real.pi:ℂ)^(-2*z)*(x/t^2:ℂ)^(-z)) by ring,
      ← bblr_main_positive_cpow_identity ht hx z]
    ring
  have hIS : Integrable (fun v : ℝ => S (1+(v:ℂ)*I)) := by
    convert hIV.sub hID using 1
    funext v
    have h := hPoint (1+(v:ℂ)*I)
    simp only [Pi.sub_apply,Complex.ofReal_one]
    unfold bblrVerticalIntegrand
    linear_combination -h
  have hsub : (∫ v : ℝ, bblrVerticalIntegrand G α x t v)-
      (∫ v : ℝ, S (1+(v:ℂ)*I)) =
      ∫ v : ℝ, bblrCentralWeightDifference G t α x (1+(v:ℂ)*I) := by
    rw [← integral_sub hIV hIS]
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => hPoint (1+(v:ℂ)*I))
  unfold bblrV bblrVStar verticalIntegral
  simp only [Complex.ofReal_one]
  simpa only [bblrVerticalIntegrand,S,Complex.ofReal_div,Complex.ofReal_pow,mul_sub] using
    congrArg (fun q : ℂ => (1/(2*Real.pi):ℂ)*q) hsub

/-- The genuine source V-minus-VStar difference is the actual Gamma
difference on every prescribed positive contour at most one unit wide. -/
theorem bblrV_sub_bblrVStar_eq_shifted_centralWeightDifference {t x c : ℝ}
    (ht : 0 < t) (hx : 0 < x) (hc : 0 < c) (hc1 : c ≤ 1)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    bblrV G α x t-bblrVStar G (x/t^2) =
      verticalIntegral c (bblrCentralWeightDifference G t α x) := by
  rw [bblrV_sub_bblrVStar_eq_centralWeightDifference ht hx G α hG hα,
    bblrCentralWeightDifference_verticalIntegral_shift ht hx hc hc1 G α hG hα]

theorem bblrGaussianV_sub_bblrVStar_eq_shifted_centralWeightDifference
    {t x c : ℝ} (ht : 0 < t) (hx : 0 < x) (hc : 0 < c) (hc1 : c ≤ 1)
    (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    bblrV (polarPoleKiller T σ) α x t-bblrVStar (polarPoleKiller T σ) (x/t^2) =
      verticalIntegral c (bblrCentralWeightDifference (polarPoleKiller T σ) t α x) :=
  bblrV_sub_bblrVStar_eq_shifted_centralWeightDifference ht hx hc hc1
    (polarPoleKiller T σ) α (polarPoleKiller_BBLREntireWeight T σ α) hα

end
end Sechstmoment.Source
