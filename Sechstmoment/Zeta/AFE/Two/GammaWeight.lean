import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Sechstmoment.Analysis.Complex.ContourShift
import Sechstmoment.Analysis.Gaussian.Decay
import Sechstmoment.Analysis.Gaussian.MellinContours
import Sechstmoment.Zeta.AFE.Two.Gamma

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem secondPoleCorrection_vertical_norm_le {t c : ℝ} (ht : 10 ≤ t)
    (hc : 0 < c) (hc1 : c ≤ 1) (α : SecondMomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) (v : ℝ) :
    ‖secondPoleCorrection (secondSourceZetaPoints t 0+α 0)
      (secondSourceZetaPoints t 1+α 1) ((c:ℂ)+(v:ℂ)*I)‖ ≤
        4096*(1+|v|)^8 := by
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  let s := secondSourceZetaPoints t 0+α 0
  let r := secondSourceZetaPoints t 1+α 1
  have hbase (j : Fin 4) : t/2 ≤ ‖secondPoleCorrectionBases s r j‖ :=
    secondPoleCorrectionBases_norm_lower (by norm_num : (0:ℝ) ≤ 1/4)
      (by norm_num; exact ht) α hα j
  have hcoeff (j : Fin 4) : 1+‖(secondPoleCorrectionBases s r j)^2‖⁻¹ ≤ 2 := by
    have hb : 1 ≤ ‖(secondPoleCorrectionBases s r j)^2‖ := by
      rw [norm_pow]
      nlinarith [hbase j, norm_nonneg (secondPoleCorrectionBases s r j)]
    linarith [inv_le_one_of_one_le₀ hb]
  have hp : (∏ j : Fin 4, (1+‖(secondPoleCorrectionBases s r j)^2‖⁻¹)) ≤ 16 := by
    calc
      _ ≤ ∏ _j : Fin 4, (2:ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => hcoeff j)
      _ = _ := by norm_num
  have hn : ‖z‖ ≤ 1+|v| := by
    have hh := norm_add_le (c:ℂ) ((v:ℂ)*I)
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
      mul_one, abs_of_pos hc] at hh
    exact hh.trans (by linarith)
  have hz : (1+‖z‖)^8 ≤ 256*(1+|v|)^8 := by
    calc
      _ ≤ (2*(1+|v|))^8 := by gcongr; linarith [abs_nonneg v]
      _ = _ := by ring
  exact ((secondPoleCorrection_polynomial_norm_le s r z).trans
    (mul_le_mul hp hz (by positivity) (by norm_num))).trans_eq (by ring)

def secondPoleCorrectedGaussianKernel (t : ℝ) (α : SecondMomentShifts)
    (c v : ℝ) : ℂ :=
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  Complex.exp (z^2)/z*secondPoleCorrectedGammaQuotient t α z

theorem secondPoleCorrectedGaussianKernel_global_majorant :
    ∃ C : ℝ, 0 < C ∧ ∀ t c : ℝ, 10 ≤ t → 0 < c → c ≤ 1 →
      ∀ α : SecondMomentShifts, (∀ j, ‖α j‖ ≤ 1/4) → ∀ v : ℝ,
        ‖secondPoleCorrectedGaussianKernel t α c v‖ ≤
          C*(2+t)^4/c*(1+|v|)^12*Real.exp (-v^2) := by
  obtain ⟨C, hC, hb⟩ := secondGammaGaussianKernel_global_majorant
  refine ⟨4096*C, by positivity, ?_⟩
  intro t c ht hc hc1 α hα v
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have he : secondPoleCorrectedGaussianKernel t α c v =
      secondPoleCorrection (secondSourceZetaPoints t 0+α 0)
        (secondSourceZetaPoints t 1+α 1) z*secondGammaGaussianKernel t α c v := by
    unfold secondPoleCorrectedGaussianKernel secondPoleCorrectedGammaQuotient
      secondGammaGaussianKernel
    ring
  rw [he, norm_mul]
  have hp := secondPoleCorrection_vertical_norm_le ht hc hc1 α hα v
  have hq := hb t c (by linarith) hc hc1 α hα v
  exact (mul_le_mul hp hq (norm_nonneg _) (by positivity)).trans_eq (by ring)

def secondCorrectedWeightKernel (t : ℝ) (α : SecondMomentShifts) (x : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z^2)/z*secondPoleCorrectedGammaQuotient t α z*
    (Real.pi:ℂ)^(-z)*(x:ℂ)^(-z)

def secondCorrectedWeightOnLine (c t : ℝ) (α : SecondMomentShifts) (x : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v : ℝ, secondCorrectedWeightKernel t α x ((c:ℂ)+(v:ℂ)*I)

theorem secondCorrectedWeightKernel_differentiableOn (t : ℝ)
    (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (secondCorrectedWeightKernel t α x) {z : ℂ | 0 < z.re} := by
  have hq : DifferentiableOn ℂ (secondGammaQuotient t α) {z : ℂ | 0 < z.re} := by
    intro z hz
    change 0 < z.re at hz
    unfold secondGammaQuotient
    apply DifferentiableWithinAt.fun_finsetProd
    intro j hj
    apply DifferentiableWithinAt.div_const
    apply DifferentiableAt.differentiableWithinAt
    apply (Complex.differentiableAt_Gamma _ ?_).comp z (by fun_prop)
    intro n hn
    have hr := congrArg Complex.re hn
    have ha := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
    simp at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  intro z hz
  change 0 < z.re at hz
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  unfold secondCorrectedWeightKernel secondPoleCorrectedGammaQuotient
  apply DifferentiableWithinAt.mul
  · apply DifferentiableWithinAt.mul
    · apply DifferentiableWithinAt.mul
      · apply DifferentiableAt.differentiableWithinAt
        fun_prop
      · apply DifferentiableWithinAt.mul
        · unfold secondPoleCorrection
          fun_prop
        · exact hq z hz
    · apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow
      · fun_prop
      · exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  · apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')

theorem secondCorrectedWeightKernel_vertical_norm (t : ℝ) (α : SecondMomentShifts)
    {x : ℝ} (hx : 0 < x) (c v : ℝ) :
    ‖secondCorrectedWeightKernel t α x ((c:ℂ)+(v:ℂ)*I)‖ =
      ‖secondPoleCorrectedGaussianKernel t α c v‖*Real.pi^(-c)*x^(-c) := by
  unfold secondCorrectedWeightKernel secondPoleCorrectedGaussianKernel
  rw [norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem secondCorrectedWeightKernel_integrable {t c x : ℝ}
    (ht : 10 ≤ t) (hc : 0 < c) (hc1 : c ≤ 1) (hx : 0 < x)
    (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    Integrable (fun v : ℝ => secondCorrectedWeightKernel t α x ((c:ℂ)+(v:ℂ)*I)) := by
  obtain ⟨C, hC, hb⟩ := secondPoleCorrectedGaussianKernel_global_majorant
  let B : ℝ := C*(2+t)^4/c*Real.pi^(-c)*x^(-c)
  have hgi : Integrable (fun v : ℝ => (1+|v|)^12*Real.exp (-v^2)) := by
    simpa only [zero_mul, zero_sub] using
      Sechstmoment.gaussianPolynomialExponential_integrable 12 0
  have hcont : Continuous (fun v : ℝ =>
      secondCorrectedWeightKernel t α x ((c:ℂ)+(v:ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hd := secondCorrectedWeightKernel_differentiableOn t α hα hx
    have hz : 0 < (((c:ℂ)+(v:ℂ)*I):ℂ).re := by simpa using hc
    have hdz : DifferentiableAt ℂ (secondCorrectedWeightKernel t α x)
        ((c:ℂ)+(v:ℂ)*I) :=
      (hd _ hz).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
    have hline : ContinuousAt (fun v : ℝ => (c:ℂ)+(v:ℂ)*I) v := by fun_prop
    exact hdz.continuousAt.comp (f := fun w : ℝ => (c:ℂ)+(w:ℂ)*I) (x := v) hline
  apply (hgi.const_mul B).mono' hcont.aestronglyMeasurable
  apply Eventually.of_forall
  intro v
  rw [secondCorrectedWeightKernel_vertical_norm t α hx c v]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hb t c ht hc hc1 α hα v) (by positivity))
    (by positivity)).trans_eq (by dsimp [B]; ring)

theorem secondCorrectedWeightOnLine_eq_one {t c x : ℝ}
    (ht : 10 ≤ t) (hc : 0 < c) (hc1 : c ≤ 1) (hx : 0 < x)
    (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    secondCorrectedWeightOnLine c t α x = secondCorrectedWeightOnLine 1 t α x := by
  obtain ⟨C, hC, hb⟩ := secondPoleCorrectedGaussianKernel_global_majorant
  let B : ℝ := C*(2+t)^4/c*Real.exp |Real.log x|
  have hpoint (u v : ℝ) (hu : u ∈ Icc c 1) :
      ‖secondCorrectedWeightKernel t α x ((u:ℂ)+(v:ℂ)*I)‖ ≤
        B*(1+|v|)^12*Real.exp (-v^2) := by
    have hup : 0 < u := hc.trans_le hu.1
    have hp : Real.pi^(-u) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
    have hxp : x^(-u) ≤ Real.exp |Real.log x| := by
      rw [Real.rpow_def_of_pos hx]
      apply Real.exp_le_exp.mpr
      calc
        Real.log x*(-u) = u*(-Real.log x) := by ring
        _ ≤ u*|Real.log x| := mul_le_mul_of_nonneg_left (neg_le_abs _) hup.le
        _ ≤ 1*|Real.log x| := mul_le_mul_of_nonneg_right hu.2 (abs_nonneg _)
        _ = _ := one_mul _
    rw [secondCorrectedWeightKernel_vertical_norm t α hx u v]
    have hk := hb t u ht hup hu.2 α hα v
    have hdiv : C*(2+t)^4/u ≤ C*(2+t)^4/c :=
      div_le_div_of_nonneg_left (by positivity) hc hu.1
    calc
      _ ≤ (C*(2+t)^4/c*(1+|v|)^12*Real.exp (-v^2))*1*Real.exp |Real.log x| := by
        apply mul_le_mul
        · exact mul_le_mul (hk.trans (by gcongr)) hp (by positivity) (by positivity)
        · exact hxp
        · positivity
        · positivity
      _ = _ := by dsimp [B]; ring
  have hedge : Tendsto (fun v : ℝ => ∫ u in c..1,
      secondCorrectedWeightKernel t α x ((u:ℂ)+(v:ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
    have hlim : Tendsto (fun v : ℝ => (1-c)*B*(1+|v|)^12*Real.exp (-v^2))
        (cocompact ℝ) (𝓝 0) := by
      simpa only [zero_mul, zero_sub, mul_zero, mul_assoc] using
        (Sechstmoment.gaussianPolynomialExponential_tendsto_zero 12 0).const_mul ((1-c)*B)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
    apply Eventually.of_forall
    intro v
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu =>
      hpoint u v (by rw [uIoc_of_le hc1] at hu; exact ⟨hu.1.le, hu.2⟩))
    simp only [abs_of_nonneg (sub_nonneg.mpr hc1)] at hh
    exact hh.trans_eq (by ring)
  have he := Sechstmoment.bblrRectangle_integral_shift (secondCorrectedWeightKernel t α x)
    (secondCorrectedWeightKernel_differentiableOn t α hα hx) hc1
    (fun z ha hb => by simpa using hc.trans_le ha)
    (secondCorrectedWeightKernel_integrable ht hc hc1 hx α hα)
    (secondCorrectedWeightKernel_integrable ht (by norm_num) (by norm_num) hx α hα) hedge
  unfold secondCorrectedWeightOnLine
  rw [he]

def secondLeadingWeightKernel (t x : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z^2)/z*(t/2:ℂ)^z*(Real.pi:ℂ)^(-z)*(x:ℂ)^(-z)

def secondCorrectedWeightErrorKernel (t : ℝ) (α : SecondMomentShifts)
    (x : ℝ) (z : ℂ) : ℂ :=
  secondCorrectedWeightKernel t α x z-secondLeadingWeightKernel t x z

theorem secondLeadingWeightKernel_eq_gaussian {t x : ℝ} (ht : 0 < t)
    (hx : 0 < x) (z : ℂ) :
    secondLeadingWeightKernel t x z =
      Complex.exp (z^2)/z*((2*Real.pi*x/t:ℝ):ℂ)^(-z) := by
  have hp : 0 < 2*Real.pi*x/t := by positivity
  have hp2 : 0 < t/2 := by positivity
  have hy : 2*Real.pi*x/t = Real.pi*x/(t/2) := by field_simp
  have hlog : Complex.log ((2*Real.pi*x/t:ℝ):ℂ) =
      Complex.log (Real.pi:ℂ)+Complex.log (x:ℂ)-Complex.log (t/2:ℂ) := by
    rw [←Complex.ofReal_log hp.le, ←Complex.ofReal_log Real.pi_pos.le,
      ←Complex.ofReal_log hx.le, secondGammaHalf_log ht, hy,
      Real.log_div (mul_pos Real.pi_pos hx).ne' hp2.ne',
      Real.log_mul Real.pi_pos.ne' hx.ne']
    push_cast
    rfl
  have he : (t/2:ℂ)^z*(Real.pi:ℂ)^(-z)*(x:ℂ)^(-z) =
      ((2*Real.pi*x/t:ℝ):ℂ)^(-z) := by
    rw [Complex.cpow_def_of_ne_zero (secondGammaHalf_ne_zero ht),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
      ←Complex.exp_add, ←Complex.exp_add, hlog]
    congr 1
    ring
  unfold secondLeadingWeightKernel
  rw [show Complex.exp (z^2)/z*(t/2:ℂ)^z*(Real.pi:ℂ)^(-z)*(x:ℂ)^(-z) =
    Complex.exp (z^2)/z*((t/2:ℂ)^z*(Real.pi:ℂ)^(-z)*(x:ℂ)^(-z)) by ring, he]

theorem secondLeadingWeightKernel_integrable {t c x : ℝ} (ht : 0 < t)
    (hc : 0 < c) (hx : 0 < x) :
    Integrable (fun v : ℝ => secondLeadingWeightKernel t x ((c:ℂ)+(v:ℂ)*I)) := by
  have hp : 0 < 2*Real.pi*x/t := by positivity
  have he (v : ℝ) : secondLeadingWeightKernel t x ((c:ℂ)+(v:ℂ)*I) =
      Sechstmoment.d02GaussianMellinIntegrandOnLine c (Real.log (2*Real.pi*x/t)) v := by
    rw [secondLeadingWeightKernel_eq_gaussian ht hx]
    unfold Sechstmoment.d02GaussianMellinIntegrandOnLine
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
      ←Complex.ofReal_log hp.le]
    rw [div_mul_eq_mul_div, ←Complex.exp_add]
    apply congrArg (fun w : ℂ => Complex.exp w/((c:ℂ)+(v:ℂ)*I))
    ring
  exact (Sechstmoment.d02GaussianMellinIntegrandOnLine_integrable hc _).congr
    (Eventually.of_forall (fun v => (he v).symm))

theorem secondLeadingWeightKernel_integral_eq {t c x : ℝ} (ht : 0 < t)
    (hc : 0 < c) (hx : 0 < x) :
    (1/(2*Real.pi):ℂ)*(∫ v : ℝ,
      secondLeadingWeightKernel t x ((c:ℂ)+(v:ℂ)*I)) =
        (Sechstmoment.d02GaussianV0 (2*Real.pi*x/t):ℂ) := by
  have he : (fun v : ℝ => secondLeadingWeightKernel t x ((c:ℂ)+(v:ℂ)*I)) =
      (fun v : ℝ => let z : ℂ := (c:ℂ)+(v:ℂ)*I;
        Complex.exp (z^2)/z*((2*Real.pi*x/t:ℝ):ℂ)^(-z)) := by
    funext v
    exact secondLeadingWeightKernel_eq_gaussian ht hx _
  rw [he]
  exact Sechstmoment.d02GaussianMellinV0OnLine_eq_gaussianV0 hc (by positivity)

theorem secondLeadingWeightKernel_vertical_majorant {t c x : ℝ}
    (ht : 10 ≤ t) (hc : 0 < c) (hc1 : c ≤ 1) (hx : 0 < x) (v : ℝ) :
    ‖secondLeadingWeightKernel t x ((c:ℂ)+(v:ℂ)*I)‖ ≤
      Real.exp 1*(2+t)^4/c*Real.pi^(-c)*x^(-c)*
        ((1+|v|)^12*Real.exp (-v^2)) := by
  have htp : 0 < t := by linarith
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hr : z.re = c := by simp [z]
  have hi : z.im = v := by simp [z]
  have hn : c ≤ ‖z‖ := by simpa [hr, abs_of_pos hc] using Complex.abs_re_le_norm z
  have hs : (z^2).re = c^2-v^2 := by simp [pow_two, Complex.mul_re, hr, hi]
  have hg : ‖Complex.exp (z^2)/z‖ ≤ Real.exp 1/c*Real.exp (-v^2) := by
    rw [norm_div, Complex.norm_exp, hs,
      show c^2-v^2 = c^2+(-v^2) by ring, Real.exp_add]
    calc
      _ ≤ (Real.exp 1*Real.exp (-v^2))/c := by
        apply div_le_div₀ (by positivity)
        · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
        · exact hc
        · exact hn
      _ = _ := by ring
  have hpow : (t/2)^c ≤ (2+t)^4 := by
    calc
      _ ≤ (t/2)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hc1
      _ = t/2 := Real.rpow_one _
      _ ≤ 2+t := by linarith
      _ ≤ (2+t)^4 := le_self_pow₀ (by linarith) (by norm_num)
  have hv : 1 ≤ (1+|v|)^12 := one_le_pow₀ (by linarith [abs_nonneg v])
  unfold secondLeadingWeightKernel
  rw [norm_mul, norm_mul, norm_mul,
    secondGammaHalfPower_norm htp,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.neg_re]
  change ‖Complex.exp (z^2)/z‖*(t/2)^z.re*Real.pi^(-z.re)*x^(-z.re) ≤ _
  rw [hr]
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hg hpow (by positivity) (by positivity))
      (by positivity)) (by positivity)).trans
  have hh := mul_le_mul_of_nonneg_left hv
    (by positivity : 0 ≤ (Real.exp 1/c*Real.exp (-v^2))*(2+t)^4*Real.pi^(-c)*x^(-c))
  calc
    _ ≤ (Real.exp 1/c*Real.exp (-v^2))*(2+t)^4*Real.pi^(-c)*x^(-c)*(1+|v|)^12 := by
      simpa only [mul_one] using hh
    _ = Real.exp 1*(2+t)^4/c*Real.pi^(-c)*x^(-c)*
        ((1+|v|)^12*Real.exp (-v^2)) := by ring

theorem secondCorrectedWeightErrorKernel_global_majorant :
    ∃ C : ℝ, 0 < C ∧ ∀ t c x : ℝ, 10 ≤ t → 0 < c → c ≤ 1 → 0 < x →
      ∀ α : SecondMomentShifts, (∀ j, ‖α j‖ ≤ 1/4) → ∀ v : ℝ,
        ‖secondCorrectedWeightErrorKernel t α x ((c:ℂ)+(v:ℂ)*I)‖ ≤
          C*(2+t)^4/c*Real.pi^(-c)*x^(-c)*((1+|v|)^12*Real.exp (-v^2)) := by
  obtain ⟨C, hC, hb⟩ := secondPoleCorrectedGaussianKernel_global_majorant
  refine ⟨C+Real.exp 1, by positivity, ?_⟩
  intro t c x ht hc hc1 hx α hα v
  have ha := hb t c ht hc hc1 α hα v
  have hal : ‖secondCorrectedWeightKernel t α x ((c:ℂ)+(v:ℂ)*I)‖ ≤
      C*(2+t)^4/c*Real.pi^(-c)*x^(-c)*((1+|v|)^12*Real.exp (-v^2)) := by
    rw [secondCorrectedWeightKernel_vertical_norm t α hx c v]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (by positivity))
      (by positivity)).trans_eq (by ring)
  have hl := secondLeadingWeightKernel_vertical_majorant ht hc hc1 hx v
  exact (norm_sub_le _ _).trans ((add_le_add hal hl).trans_eq (by ring))

theorem secondCorrectedWeightErrorKernel_integrable {t c x : ℝ}
    (ht : 10 ≤ t) (hc : 0 < c) (hc1 : c ≤ 1) (hx : 0 < x)
    (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    Integrable (fun v : ℝ => secondCorrectedWeightErrorKernel t α x ((c:ℂ)+(v:ℂ)*I)) :=
  (secondCorrectedWeightKernel_integrable ht hc hc1 hx α hα).sub
    (secondLeadingWeightKernel_integrable (by linarith) hc hx)

theorem secondCorrectedWeightErrorKernel_central_point {t c x : ℝ}
    (ht : 10 ≤ t) (hc : 0 < c) (hc1 : c ≤ 1) (hx : 0 < x)
    (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) (v : ℝ)
    (hz : 192*(‖(c:ℂ)+(v:ℂ)*I‖+‖(c:ℂ)+(v:ℂ)*I‖^2) < t) :
    ‖secondCorrectedWeightErrorKernel t α x ((c:ℂ)+(v:ℂ)*I)‖ ≤
      (1164*Real.exp 1/c)*t^(c-1)*Real.pi^(-c)*x^(-c)*
        ((1+|v|)^2*Real.exp (-v^2)) := by
  have htp : 0 < t := by linarith
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  let W : ℝ := 1+|v|
  have hr : z.re = c := by simp [z]
  have hi : z.im = v := by simp [z]
  have hn : ‖z‖ ≤ W := by
    have hh := norm_add_le (c:ℂ) ((v:ℂ)*I)
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at hh
    exact hh.trans (by dsimp [W]; linarith)
  have hW : 1 ≤ W := by dsimp [W]; linarith [abs_nonneg v]
  have hsq : ‖z‖^2 ≤ W^2 := by nlinarith [norm_nonneg z]
  have hlin : ‖z‖ ≤ W^2 := by nlinarith [norm_nonneg z]
  have hphase : (2+4*(1/4:ℝ))*‖z‖ ≤ t := by
    change 192*(‖z‖+‖z‖^2) < t at hz
    norm_num
    nlinarith [norm_nonneg z, sq_nonneg ‖z‖]
  have hb := secondPoleCorrectedGammaQuotient_normalized_error_le
    (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num; exact ht) α hα z hz hphase
  norm_num only [show (2:ℝ)+4*(1/4)=3 by norm_num] at hb
  have hden : 60*‖z‖^2/t^2 ≤ 6*‖z‖^2/t := by
    rw [div_le_div_iff₀ (sq_pos_of_pos htp) htp]
    have ht2 : 10*t ≤ t^2 := by nlinarith [mul_nonneg htp.le (sub_nonneg.mpr ht)]
    nlinarith [mul_le_mul_of_nonneg_left ht2 (by positivity : 0 ≤ 6*‖z‖^2)]
  have hpoly : 2*((288*(‖z‖+‖z‖^2)+3*‖z‖)/t)+60*‖z‖^2/t^2 ≤ 1164*W^2/t := by
    calc
      _ ≤ 2*((288*(‖z‖+‖z‖^2)+3*‖z‖)/t)+6*‖z‖^2/t := add_le_add_right hden _
      _ = (582*‖z‖+582*‖z‖^2)/t := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) htp.le
  have hrel := hb.trans hpoly
  have hbase : (t/2:ℂ)^z ≠ 0 := by
    simp [secondGammaHalf_ne_zero htp]
  have he : secondPoleCorrectedGammaQuotient t α z-(t/2:ℂ)^z =
      (t/2:ℂ)^z*(secondPoleCorrectedGammaQuotient t α z/(t/2:ℂ)^z-1) := by field_simp
  have hcore : ‖secondPoleCorrectedGammaQuotient t α z-(t/2:ℂ)^z‖ ≤
      t^c*(1164*W^2/t) := by
    rw [he, norm_mul, secondGammaHalfPower_norm htp, hr]
    exact mul_le_mul (Real.rpow_le_rpow (by positivity) (by linarith) hc.le)
      hrel (norm_nonneg _) (by positivity)
  have hg : ‖Complex.exp (z^2)/z‖ ≤ Real.exp 1/c*Real.exp (-v^2) := by
    have hg0 := Sechstmoment.d02GaussianMellinIntegrandOnLine_norm_le hc 0 v
    simp only [Sechstmoment.d02GaussianMellinIntegrandOnLine, zero_mul,
      sub_zero, Complex.ofReal_zero] at hg0
    apply hg0.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply div_le_div_of_nonneg_right _ hc.le
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hew : secondCorrectedWeightErrorKernel t α x z =
      Complex.exp (z^2)/z*(secondPoleCorrectedGammaQuotient t α z-(t/2:ℂ)^z)*
        (Real.pi:ℂ)^(-z)*(x:ℂ)^(-z) := by
    unfold secondCorrectedWeightErrorKernel secondCorrectedWeightKernel secondLeadingWeightKernel
    ring
  rw [hew, norm_mul, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.neg_re, hr]
  calc
    _ ≤ (Real.exp 1/c*Real.exp (-v^2))*(t^c*(1164*W^2/t))*Real.pi^(-c)*x^(-c) := by
      gcongr
    _ = _ := by rw [Real.rpow_sub htp, Real.rpow_one]; dsimp [W]; ring

theorem secondCorrectedWeight_sqrt_cut_admissible {t c : ℝ}
    (ht : 10000 ≤ t) (hc : 0 < c) (hc1 : c ≤ 1) {v : ℝ}
    (hv : v ∈ Icc (-Real.sqrt t/100) (Real.sqrt t/100)) :
    192*(‖(c:ℂ)+(v:ℂ)*I‖+‖(c:ℂ)+(v:ℂ)*I‖^2) < t := by
  have htp : 0 ≤ t := by linarith
  have hs : (Real.sqrt t)^2 = t := Real.sq_sqrt htp
  have h100 : 100 ≤ Real.sqrt t := by
    have hh := Real.sqrt_le_sqrt ht
    norm_num at hh
    exact hh
  have hm : 100*Real.sqrt t ≤ t := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg t) (sub_nonneg.mpr h100)]
  have hva : |v| ≤ Real.sqrt t/100 := abs_le.mpr (by constructor <;> linarith [hv.1, hv.2])
  have hn : ‖(c:ℂ)+(v:ℂ)*I‖ ≤ 1+Real.sqrt t/100 := by
    have hh := norm_add_le (c:ℂ) ((v:ℂ)*I)
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at hh
    linarith
  have hn2 : ‖(c:ℂ)+(v:ℂ)*I‖^2 ≤ (1+Real.sqrt t/100)^2 := by
    nlinarith [norm_nonneg ((c:ℂ)+(v:ℂ)*I)]
  nlinarith [norm_nonneg ((c:ℂ)+(v:ℂ)*I)]

theorem secondCorrectedWeightErrorKernel_central_integral_norm_le {t c x : ℝ}
    (ht : 10000 ≤ t) (hc : 0 < c) (hc1 : c ≤ 1) (hx : 0 < x)
    (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    ‖∫ v in Icc (-Real.sqrt t/100) (Real.sqrt t/100),
      secondCorrectedWeightErrorKernel t α x ((c:ℂ)+(v:ℂ)*I)‖ ≤
      (1164*Real.exp 1/c)*t^(c-1)*Real.pi^(-c)*x^(-c)*secondGaussianQuadraticMass := by
  let B : ℝ := (1164*Real.exp 1/c)*t^(c-1)*Real.pi^(-c)*x^(-c)
  have hgi : Integrable (fun v : ℝ => B*((1+|v|)^2*Real.exp (-v^2))) :=
    secondGaussianQuadraticMajorant_integrable.const_mul B
  have hpoint : ∀ᵐ (v : ℝ) ∂volume.restrict (Icc (-Real.sqrt t/100) (Real.sqrt t/100)),
      ‖secondCorrectedWeightErrorKernel t α x ((c:ℂ)+(v:ℂ)*I)‖ ≤
        B*((1+|v|)^2*Real.exp (-v^2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact secondCorrectedWeightErrorKernel_central_point (by linarith) hc hc1 hx α hα v
      (secondCorrectedWeight_sqrt_cut_admissible ht hc hc1 hv)
  calc
    _ ≤ ∫ v in Icc (-Real.sqrt t/100) (Real.sqrt t/100), B*((1+|v|)^2*Real.exp (-v^2)) :=
      norm_integral_le_of_norm_le hgi.integrableOn hpoint
    _ ≤ ∫ v : ℝ, B*((1+|v|)^2*Real.exp (-v^2)) :=
      setIntegral_le_integral hgi (Eventually.of_forall (fun _ => by dsimp [B]; positivity))
    _ = _ := by rw [integral_const_mul]; rfl

theorem secondCorrectedWeight_exponential_absorption {t : ℝ} (ht : 0 < t) :
    t^4*Real.exp (-t/20000) ≤ ((Nat.factorial 5:ℝ)*20000^5)/t := by
  have hh := Real.pow_div_factorial_le_exp (t/20000) (by positivity : 0 ≤ t/20000) 5
  have hfac : 0 < (Nat.factorial 5:ℝ) := by positivity
  have hh' : (t/20000)^5 ≤ (Nat.factorial 5:ℝ)*Real.exp (t/20000) := by
    simpa only [mul_comm] using (div_le_iff₀ hfac).mp hh
  have hs := mul_le_mul_of_nonneg_left hh' (by positivity : 0 ≤ (20000:ℝ)^5)
  have he : (20000:ℝ)^5*(t/20000)^5 = t^5 := by ring
  rw [he] at hs
  rw [show -t/20000 = -(t/20000) by ring, Real.exp_neg, ←div_eq_mul_inv,
    div_le_div_iff₀ (Real.exp_pos _) ht]
  simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hs

theorem secondCorrectedWeightErrorKernel_tail_norm_le {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t x : ℝ, 10000 ≤ t → 0 < x →
      ∀ α : SecondMomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
        ‖∫ v in {v : ℝ | Real.sqrt t/100 < |v|},
          secondCorrectedWeightErrorKernel t α x ((c:ℂ)+(v:ℂ)*I)‖ ≤
          D*t^(c-1)*Real.pi^(-c)*x^(-c) := by
  obtain ⟨C, hC, hb⟩ := secondCorrectedWeightErrorKernel_global_majorant
  have hM : 0 ≤ gaussianTailConstant 12 := gaussianTailConstant_nonneg _
  let D : ℝ := (81*C/c)*gaussianTailConstant 12*(Nat.factorial 5:ℝ)*20000^5
  refine ⟨D, by dsimp [D]; exact mul_nonneg (mul_nonneg
    (mul_nonneg (by positivity) (gaussianTailConstant_nonneg _)) (by positivity)) (by positivity), ?_⟩
  intro t x ht hx α hα
  have htp : 0 < t := by linarith
  let B : ℝ := C*(2+t)^4/c*Real.pi^(-c)*x^(-c)
  have htail := gaussian_integral_tail_norm_le (B := B)
    (fun v : ℝ => secondCorrectedWeightErrorKernel t α x ((c:ℂ)+(v:ℂ)*I))
    (secondCorrectedWeightErrorKernel_integrable (by linarith) hc hc1 hx α hα) 12
    (by dsimp [B]; positivity) (by positivity : 0 ≤ Real.sqrt t/100)
    (fun v => by dsimp [B]; simpa only [mul_assoc] using hb t c x (by linarith) hc hc1 hx α hα v)
  have hsq : (Real.sqrt t/100)^2 = t/10000 := by rw [div_pow, Real.sq_sqrt htp.le]; norm_num
  rw [hsq] at htail
  have hp : (2+t)^4 ≤ 81*t^4 := by
    calc
      _ ≤ (3*t)^4 := by gcongr; linarith
      _ = _ := by ring
  have hpower : 1/t ≤ t^(c-1) := by
    rw [one_div, ←Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  apply htail.trans
  calc
    _ ≤ (C*(81*t^4)/c*Real.pi^(-c)*x^(-c))*gaussianTailConstant 12*
        Real.exp (-(1/2)*(t/10000)) := by
      dsimp [B]
      gcongr
    _ = (81*C/c*gaussianTailConstant 12)*Real.pi^(-c)*x^(-c)*
        (t^4*Real.exp (-t/20000)) := by
      rw [show -(1/2)*(t/10000) = -t/20000 by ring]
      ring
    _ ≤ (81*C/c*gaussianTailConstant 12)*Real.pi^(-c)*x^(-c)*
        (((Nat.factorial 5:ℝ)*20000^5)/t) :=
      mul_le_mul_of_nonneg_left (secondCorrectedWeight_exponential_absorption htp)
        (by exact mul_nonneg (mul_nonneg
          (mul_nonneg (by positivity) (gaussianTailConstant_nonneg _)) (by positivity)) (by positivity))
    _ = D*Real.pi^(-c)*x^(-c)*(1/t) := by dsimp [D]; ring
    _ ≤ D*Real.pi^(-c)*x^(-c)*t^(c-1) := by
      apply mul_le_mul_of_nonneg_left hpower
      exact mul_nonneg (mul_nonneg (by dsimp [D]; positivity) (by positivity)) (by positivity)
    _ = _ := by ring

theorem secondCorrectedWeightErrorKernel_full_integral_norm_le {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x : ℝ, 10000 ≤ t → 0 < x →
      ∀ α : SecondMomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
        ‖∫ v : ℝ, secondCorrectedWeightErrorKernel t α x ((c:ℂ)+(v:ℂ)*I)‖ ≤
          C*t^(c-1)*Real.pi^(-c)*x^(-c) := by
  obtain ⟨D, hD, hb⟩ := secondCorrectedWeightErrorKernel_tail_norm_le hc hc1
  have hM := secondGaussianQuadraticMass_nonneg
  refine ⟨(1164*Real.exp 1/c)*secondGaussianQuadraticMass+D, by positivity, ?_⟩
  intro t x ht hx α hα
  let H : ℝ := Real.sqrt t/100
  have hfi := secondCorrectedWeightErrorKernel_integrable (t := t) (by linarith) hc hc1 hx α hα
  have hcomp : (Icc (-H) H)ᶜ = {v : ℝ | H < |v|} := by
    ext v
    simp only [mem_compl_iff, mem_Icc, mem_ofPred_eq]
    rw [←abs_le, not_le]
  have hsplit := integral_add_compl (s := Icc (-H) H) measurableSet_Icc hfi
  rw [hcomp] at hsplit
  rw [←hsplit]
  have hcentral : ‖∫ v in Icc (-H) H,
      secondCorrectedWeightErrorKernel t α x ((c:ℂ)+(v:ℂ)*I)‖ ≤
      (1164*Real.exp 1/c)*t^(c-1)*Real.pi^(-c)*x^(-c)*secondGaussianQuadraticMass := by
    simpa only [H, neg_div] using
      secondCorrectedWeightErrorKernel_central_integral_norm_le ht hc hc1 hx α hα
  have htail : ‖∫ v in {v : ℝ | H < |v|},
      secondCorrectedWeightErrorKernel t α x ((c:ℂ)+(v:ℂ)*I)‖ ≤
      D*t^(c-1)*Real.pi^(-c)*x^(-c) := hb t x ht hx α hα
  calc
    _ ≤ ‖∫ v in Icc (-H) H, secondCorrectedWeightErrorKernel t α x ((c:ℂ)+(v:ℂ)*I)‖+
        ‖∫ v in {v : ℝ | H < |v|}, secondCorrectedWeightErrorKernel t α x ((c:ℂ)+(v:ℂ)*I)‖ :=
      norm_add_le _ _
    _ ≤ (1164*Real.exp 1/c)*t^(c-1)*Real.pi^(-c)*x^(-c)*secondGaussianQuadraticMass+
        D*t^(c-1)*Real.pi^(-c)*x^(-c) := add_le_add hcentral htail
    _ = ((1164*Real.exp 1/c)*secondGaussianQuadraticMass+D)*
        t^(c-1)*Real.pi^(-c)*x^(-c) := by ring

theorem secondCorrectedWeightOnLine_one_gaussian_error {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x : ℝ, 10000 ≤ t → 0 < x →
      ∀ α : SecondMomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
        ‖secondCorrectedWeightOnLine 1 t α x-
          (Sechstmoment.d02GaussianV0 (2*Real.pi*x/t):ℂ)‖ ≤
            C*t^(c-1)*x^(-c) := by
  obtain ⟨D, hD, hb⟩ := secondCorrectedWeightErrorKernel_full_integral_norm_le hc hc1
  refine ⟨D*Real.pi^(-c)/(2*Real.pi), by positivity, ?_⟩
  intro t x ht hx α hα
  have htp : 0 < t := by linarith
  rw [←secondCorrectedWeightOnLine_eq_one (by linarith) hc hc1 hx α hα,
    ←secondLeadingWeightKernel_integral_eq htp hc hx]
  unfold secondCorrectedWeightOnLine
  rw [←mul_sub, ←integral_sub
    (secondCorrectedWeightKernel_integrable (by linarith) hc hc1 hx α hα)
    (secondLeadingWeightKernel_integrable htp hc hx), norm_mul]
  have hscale : ‖(1/(2*Real.pi):ℂ)‖ = 1/(2*Real.pi) := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hscale]
  exact (mul_le_mul_of_nonneg_left (hb t x ht hx α hα) (by positivity)).trans_eq (by ring)

end
end Sechstmoment.Source
