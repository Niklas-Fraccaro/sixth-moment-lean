import SixthMoment.Denominator.Balanced.FourProfileCutoff
import SixthMoment.Denominator.Balanced.GaussianSharpTilt


namespace SixthMoment
open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 0

def d02FourCapSupport (f : D01LogSpace → ℂ) (a : Fin 4 → ℝ) : Prop :=
  ∀ y, f y ≠ 0 → y.1 1 ≤ a 0 ∧ y.1 2 ≤ a 1 ∧ y.2 1 ≤ a 2 ∧ y.2 2 ≤ a 3

def d02ProfileCapSum (a : Fin 4 → ℝ) : ℝ := a 0+a 1+a 2+a 3

def d02UntiltFunction (f : D01LogSpace → ℂ) (y : D01LogSpace) : ℂ :=
  (Real.exp (d01LogTotal y) : ℂ)*f y

theorem d02LogTotal_le_cut_add_caps {f : D01LogSpace → ℂ} {a : Fin 4 → ℝ}
    (hf : d02FourCapSupport f a) {y : D01LogSpace} (hy : f y ≠ 0) :
    d01LogTotal y ≤ d02LogCutCoordinate y+d02ProfileCapSum a := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := hf y hy
  simp only [d01LogTotal, d02LogCutCoordinate, d02ProfileCapSum,
    Fin.sum_univ_three]
  linarith

theorem d02UntiltFunction_growth {f : D01LogSpace → ℂ} {a : Fin 4 → ℝ}
    {B C : ℝ} (hB : 0 ≤ B) (hf : d02FourCapSupport f a)
    (hbound : ∀ y ∈ d01PositiveOrthant, ‖f y‖ ≤ B*Real.exp (C*d02LogCutCoordinate y))
    {y : D01LogSpace} (hy : y ∈ d01PositiveOrthant) :
    ‖d02UntiltFunction f y‖ ≤
      B*Real.exp (d02ProfileCapSum a)*Real.exp ((C+1)*d02LogCutCoordinate y) := by
  by_cases hfy : f y = 0
  · simp only [d02UntiltFunction, hfy, mul_zero, norm_zero]
    positivity
  have htotal := d02LogTotal_le_cut_add_caps hf hfy
  rw [d02UntiltFunction, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (d01LogTotal y)*(B*Real.exp (C*d02LogCutCoordinate y)) :=
      mul_le_mul_of_nonneg_left (hbound y hy) (Real.exp_pos _).le
    _ = B*Real.exp (d01LogTotal y+C*d02LogCutCoordinate y) := by
      rw [Real.exp_add]
      ring
    _ ≤ B*Real.exp (d02ProfileCapSum a+(C+1)*d02LogCutCoordinate y) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hB
    _ = _ := by rw [Real.exp_add]; ring

def d02GaussianProfileTailConstant (B C : ℝ) (a : Fin 4 → ℝ) : ℝ :=
  B*Real.exp (d02ProfileCapSum a)*
    (Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp ((C+1)^2)

theorem d02GaussianProfileTailConstant_nonneg {B C : ℝ} (hB : 0 ≤ B)
    (a : Fin 4 → ℝ) : 0 ≤ d02GaussianProfileTailConstant B C a := by
  unfold d02GaussianProfileTailConstant
  positivity

theorem d02GaussianProfile_tail_bound {f : D01LogSpace → ℂ} {a : Fin 4 → ℝ}
    {B C L R c : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hR : 2 ≤ R)
    (hL : 8+2*(C+1) ≤ L) (hc : |c| ≤ C) (hf : d02FourCapSupport f a)
    (hbound : ∀ y ∈ d01PositiveOrthant, ‖f y‖ ≤ B*Real.exp (C*d02LogCutCoordinate y))
    {y : D01LogSpace} (hy : y ∈ d01PositiveOrthant) (hq : R < d02LogCutCoordinate y) :
    ‖d02UntiltFunction f y*
      (d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)‖ ≤
      d02GaussianProfileTailConstant B C a*Real.exp (-R) := by
  have hG0 := d02GaussianTail_nonneg ((L*(d02LogCutCoordinate y-1)+c)/2)
  change 0 ≤ d02GaussianLogWeight L (d02LogCutCoordinate y) c at hG0
  have hD : 0 ≤ C+1 := by linarith
  have hq2 : 2 ≤ d02LogCutCoordinate y := hR.trans hq.le
  have ht := d02GaussianLogWeight_exponential_tail hD hL hq2 (hc.trans (by linarith))
  have hsq : R ≤ d02LogCutCoordinate y^2 := by
    have hp : 0 ≤ d02LogCutCoordinate y*(d02LogCutCoordinate y-1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hG0]
  calc
    _ ≤ (B*Real.exp (d02ProfileCapSum a)*
        Real.exp ((C+1)*d02LogCutCoordinate y))*
          d02GaussianLogWeight L (d02LogCutCoordinate y) c :=
      mul_le_mul_of_nonneg_right (d02UntiltFunction_growth hB hf hbound hy) hG0
    _ = (B*Real.exp (d02ProfileCapSum a))*
        (Real.exp ((C+1)*d02LogCutCoordinate y)*
          d02GaussianLogWeight L (d02LogCutCoordinate y) c) := by ring
    _ ≤ (B*Real.exp (d02ProfileCapSum a))*
        ((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp ((C+1)^2)*
          Real.exp (-d02LogCutCoordinate y^2)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = d02GaussianProfileTailConstant B C a*Real.exp (-d02LogCutCoordinate y^2) := by
      unfold d02GaussianProfileTailConstant
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (d02GaussianProfileTailConstant_nonneg hB a)

private theorem d02GaussianTilt_profile_comparison
    {f : D01LogSpace → ℂ} {a : Fin 4 → ℝ} {B C L R c : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hR : 2 ≤ R) (hL : 8+2*(C+1) ≤ L)
    (hc : |c| ≤ C) (hfm : Measurable f) (hf : d02FourCapSupport f a)
    (hbound : ∀ y ∈ d01PositiveOrthant, ‖f y‖ ≤ B*Real.exp (C*d02LogCutCoordinate y)) :
    let g := d02UntiltFunction f
    let gR := {y | d02LogCutCoordinate y ≤ R}.indicator g
    ‖(∫ y, g y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)
        ∂d02TiltedDiagonalMeasure L) -
      ∫ y, gR y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)
        ∂d02TiltedDiagonalMeasure L‖ ≤
      d02GaussianProfileTailConstant B C a*Real.exp (-R)*
        (∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedDiagonalMeasure L) := by
  dsimp only
  let g := d02UntiltFunction f
  let gR := {y | d02LogCutCoordinate y ≤ R}.indicator g
  let MR := B*Real.exp (d02ProfileCapSum a)*Real.exp ((C+1)*R)+1
  let K := d02GaussianProfileTailConstant B C a*Real.exp (-R)
  have hL0 : 0 < L := by linarith
  have hMR : 0 < MR := by dsimp [MR]; positivity
  have hK0 : 0 ≤ K := mul_nonneg (d02GaussianProfileTailConstant_nonneg hB a)
    (Real.exp_pos _).le
  have hgm : Measurable g := (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp d01LogTotal_continuous)).measurable.mul hfm
  have hset : MeasurableSet {y | d02LogCutCoordinate y ≤ R} :=
    (isClosed_le d02LogCutCoordinate_continuous continuous_const).measurableSet
  have hRm : Measurable gR := hgm.indicator hset
  have hGaussm : Measurable (fun y : D01LogSpace =>
      (d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)) :=
    Complex.measurable_ofReal.comp ((d02GaussianLogWeight_measurable L c).comp
      d02LogCutCoordinate_continuous.measurable)
  have hRb : ∀ᵐ y ∂d02TiltedDiagonalMeasure L, ‖gR y‖ ≤ MR := by
    filter_upwards [d02TiltedDiagonalMeasure_ae_orthant hL0] with y hy
    by_cases hq : d02LogCutCoordinate y ≤ R
    · rw [show gR y = g y from indicator_of_mem (show y ∈ {z : D01LogSpace | d02LogCutCoordinate z ≤ R} from hq) g]
      have hg := d02UntiltFunction_growth hB hf hbound hy
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ C+1))
      have hp := mul_le_mul_of_nonneg_left he (show 0 ≤ B*Real.exp (d02ProfileCapSum a)
        by positivity)
      dsimp [MR]
      exact hg.trans (hp.trans (by linarith))
    · rw [show gR y = 0 from indicator_of_notMem (show y ∉ {z : D01LogSpace | d02LogCutCoordinate z ≤ R} from hq) g, norm_zero]
      exact hMR.le
  have hRi : Integrable gR (d02TiltedDiagonalMeasure L) :=
    (integrable_const MR).mono' hRm.aestronglyMeasurable hRb
  have hRGi : Integrable (fun y => gR y*
      (d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ))
      (d02TiltedDiagonalMeasure L) := by
    apply hRi.norm.mono' (hRm.mul hGaussm).aestronglyMeasurable
    exact ae_of_all _ (fun y => by
      change ‖gR y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)‖ ≤ ‖gR y‖
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ d02GaussianLogWeight L (d02LogCutCoordinate y) c from
        d02GaussianTail_nonneg _)]
      exact mul_le_of_le_one_right (norm_nonneg _) (d02GaussianTail_le_one _))
  have htail : ∀ᵐ y ∂d02TiltedDiagonalMeasure L,
      ‖g y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) -
        gR y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)‖ ≤ K := by
    filter_upwards [d02TiltedDiagonalMeasure_ae_orthant hL0] with y hy
    by_cases hq : d02LogCutCoordinate y ≤ R
    · rw [show gR y = g y from indicator_of_mem (show y ∈ {z : D01LogSpace | d02LogCutCoordinate z ≤ R} from hq) g, sub_self, norm_zero]
      exact hK0
    · rw [show gR y = 0 from indicator_of_notMem (show y ∉ {z : D01LogSpace | d02LogCutCoordinate z ≤ R} from hq) g, zero_mul, sub_zero]
      exact d02GaussianProfile_tail_bound hB hC hR hL hc hf hbound hy (not_le.mp hq)
  have hti : Integrable (fun y => g y*
      (d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) -
      gR y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ))
      (d02TiltedDiagonalMeasure L) :=
    (integrable_const K).mono' ((hgm.mul hGaussm).sub
      (hRm.mul hGaussm)).aestronglyMeasurable htail
  have hGi : Integrable (fun y => g y*
      (d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ))
      (d02TiltedDiagonalMeasure L) := by
    apply (hti.add hRGi).congr
    exact ae_of_all _ (fun _ => sub_add_cancel _ _)
  rw [← integral_sub hGi hRGi]
  calc
    _ ≤ ∫ y, ‖g y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) -
        gR y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)‖
        ∂d02TiltedDiagonalMeasure L := norm_integral_le_integral_norm _
    _ ≤ ∫ _y : D01LogSpace, K ∂d02TiltedDiagonalMeasure L :=
      integral_mono_ae hti.norm (integrable_const K) htail
    _ = _ := by
      simpa [K] using (integral_const_mul (μ := d02TiltedDiagonalMeasure L) K (fun _ : D01LogSpace => (1:ℝ)))

theorem d02DiagonalMeasure_gaussian_sharp_profile_uniform
    (a : Fin 4 → ℝ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ (f : D01LogSpace → ℂ) (c : ℝ),
      Measurable f → d02FourCapSupport f a →
      (∀ y ∈ d01PositiveOrthant, ‖f y‖ ≤ B*Real.exp (C*d02LogCutCoordinate y)) →
      |c| ≤ C →
      ‖(∫ y, f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)
        ∂d01DiagonalMeasure L) -
        ∫ y, d02SharpLogTest f y ∂d01DiagonalMeasure L‖ < ε := by
  let A := ∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedLimitMeasure
  let M := A+1
  have hA0 : 0 ≤ A := integral_nonneg (fun _ => by norm_num)
  have hM0 : 0 < M := by dsimp [M]; linarith
  let K := d02GaussianProfileTailConstant B C a
  have hK0 : 0 ≤ K := d02GaussianProfileTailConstant_nonneg hB a
  have hdecay : Tendsto (fun R : ℝ => K*Real.exp (-R)*M) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul K).mul_const M
  obtain ⟨R, hTail, hR⟩ := ((hdecay.eventually_lt_const (by linarith : (0:ℝ) < ε/2)).and
    (eventually_ge_atTop (2:ℝ))).exists
  let MR := B*Real.exp (d02ProfileCapSum a)*Real.exp ((C+1)*R)+1
  have hMR : 0 < MR := by dsimp [MR]; positivity
  have hmass := d02TiltedDiagonalMeasure_mass_tendsto.eventually_lt_const
    (show (∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedLimitMeasure) < M by
      dsimp [M,A]; linarith)
  filter_upwards [hmass,
    d02TiltedDiagonalMeasure_gaussian_sharp_uniform hMR C (by linarith : (0:ℝ) < ε/2),
    eventually_ge_atTop (8+2*(C+1))] with L hMass hCompact hL
  intro f c hfm hf hbound hc
  have hL0 : 0 < L := by linarith
  let g := d02UntiltFunction f
  let gR := {y | d02LogCutCoordinate y ≤ R}.indicator g
  have hgm : Measurable g := (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp d01LogTotal_continuous)).measurable.mul hfm
  have hset : MeasurableSet {y | d02LogCutCoordinate y ≤ R} :=
    (isClosed_le d02LogCutCoordinate_continuous continuous_const).measurableSet
  have hRm : Measurable gR := hgm.indicator hset
  have hRb : ∀ᵐ y ∂d02TiltedDiagonalMeasure L, ‖gR y‖ ≤ MR := by
    filter_upwards [d02TiltedDiagonalMeasure_ae_orthant hL0] with y hy
    by_cases hq : d02LogCutCoordinate y ≤ R
    · rw [show gR y = g y from indicator_of_mem (show y ∈ {z : D01LogSpace | d02LogCutCoordinate z ≤ R} from hq) g]
      have hg := d02UntiltFunction_growth hB hf hbound hy
      have hp := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ C+1)))
        (show 0 ≤ B*Real.exp (d02ProfileCapSum a) by positivity)
      dsimp [MR]
      exact hg.trans (hp.trans (by linarith))
    · rw [show gR y = 0 from indicator_of_notMem (show y ∉ {z : D01LogSpace | d02LogCutCoordinate z ≤ R} from hq) g, norm_zero]
      exact hMR.le
  have hComp := hCompact gR c hRm hRb hc
  have hTailNorm := d02GaussianTilt_profile_comparison hB hC hR hL hc hfm hf hbound
  have hTailSmall : ‖(∫ y, g y*
      (d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) ∂d02TiltedDiagonalMeasure L) -
      ∫ y, gR y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)
        ∂d02TiltedDiagonalMeasure L‖ < ε/2 := by
    apply lt_of_le_of_lt hTailNorm
    have hmassbound := mul_le_mul_of_nonneg_left hMass.le
      (show 0 ≤ K*Real.exp (-R) by positivity)
    exact hmassbound.trans_lt hTail
  have hSharpEq : d02SharpLogTest gR = d02SharpLogTest g := by
    funext y
    by_cases hq : d02LogCutCoordinate y ≤ 1
    · have hqR : d02LogCutCoordinate y ≤ R := hq.trans (by linarith)
      simp [d02SharpLogTest, d02SharpLogRegion, gR, hq, hqR]
    · simp [d02SharpLogTest, d02SharpLogRegion, hq]
  rw [hSharpEq] at hComp
  have hSum : ‖(∫ y, g y*
      (d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) ∂d02TiltedDiagonalMeasure L) -
      ∫ y, d02SharpLogTest g y ∂d02TiltedDiagonalMeasure L‖ < ε := by
    have hn := norm_sub_le_norm_sub_add_norm_sub
      (∫ y, g y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)
        ∂d02TiltedDiagonalMeasure L)
      (∫ y, gR y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)
        ∂d02TiltedDiagonalMeasure L)
      (∫ y, d02SharpLogTest g y ∂d02TiltedDiagonalMeasure L)
    linarith
  have hUntiltG : (∫ y, g y*
      (d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) ∂d02TiltedDiagonalMeasure L) =
      ∫ y, f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ)
        ∂d01DiagonalMeasure L := by
    unfold d02TiltedDiagonalMeasure
    rw [d01TiltedDiagonalFiniteMeasure_toMeasure hL0]
    simpa only [g, d02UntiltFunction, mul_assoc] using
      d01_integral_remove_exponential_tilt (d01DiagonalMeasure L) d01LogTotal
        d01LogTotal_continuous.measurable
        (fun y => f y*(d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ))
  have hUntiltS : (∫ y, d02SharpLogTest g y ∂d02TiltedDiagonalMeasure L) =
      ∫ y, d02SharpLogTest f y ∂d01DiagonalMeasure L := by
    unfold d02TiltedDiagonalMeasure
    rw [d01TiltedDiagonalFiniteMeasure_toMeasure hL0]
    have he : d02SharpLogTest g = fun y =>
        (Real.exp (d01LogTotal y) : ℂ)*d02SharpLogTest f y := by
      funext y
      by_cases hq : d02LogCutCoordinate y ≤ 1 <;>
        simp [d02SharpLogTest,d02SharpLogRegion,g,d02UntiltFunction,hq]
    rw [he]
    exact d01_integral_remove_exponential_tilt (d01DiagonalMeasure L) d01LogTotal
      d01LogTotal_continuous.measurable (d02SharpLogTest f)
  rwa [hUntiltG,hUntiltS] at hSum

theorem d02DiagonalMeasure_sharp_profile_norm_bound
    (a : Fin 4 → ℝ) {B C L : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 < L)
    (f : D01LogSpace → ℂ) (hf : d02FourCapSupport f a)
    (hbound : ∀ y ∈ d01PositiveOrthant, ‖f y‖ ≤ B*Real.exp (C*d02LogCutCoordinate y)) :
    ‖∫ y, d02SharpLogTest f y ∂d01DiagonalMeasure L‖ ≤
      B*Real.exp (d02ProfileCapSum a)*Real.exp (C+1)*
        (∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedDiagonalMeasure L) := by
  let K := B*Real.exp (d02ProfileCapSum a)*Real.exp (C+1)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hdom : ∀ᵐ y ∂d02TiltedDiagonalMeasure L,
      ‖d02SharpLogTest (d02UntiltFunction f) y‖ ≤ K := by
    filter_upwards [d02TiltedDiagonalMeasure_ae_orthant hL] with y hy
    by_cases hq : d02LogCutCoordinate y ≤ 1
    · rw [d02SharpLogTest, indicator_of_mem (show y ∈ d02SharpLogRegion from hq)]
      have hg := d02UntiltFunction_growth hB hf hbound hy
      have he := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ C+1))
      simpa only [mul_one] using hg.trans
        (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ B*Real.exp (d02ProfileCapSum a)))
    · rw [d02SharpLogTest, indicator_of_notMem (show y ∉ d02SharpLogRegion from hq),
        norm_zero]
      exact hK0
  have hUntilt : (∫ y, d02SharpLogTest (d02UntiltFunction f) y
      ∂d02TiltedDiagonalMeasure L) = ∫ y, d02SharpLogTest f y ∂d01DiagonalMeasure L := by
    unfold d02TiltedDiagonalMeasure
    rw [d01TiltedDiagonalFiniteMeasure_toMeasure hL]
    have he : d02SharpLogTest (d02UntiltFunction f) = fun y =>
        (Real.exp (d01LogTotal y) : ℂ)*d02SharpLogTest f y := by
      funext y
      by_cases hq : d02LogCutCoordinate y ≤ 1 <;>
        simp [d02SharpLogTest,d02SharpLogRegion,d02UntiltFunction,hq]
    rw [he]
    exact d01_integral_remove_exponential_tilt (d01DiagonalMeasure L) d01LogTotal
      d01LogTotal_continuous.measurable (d02SharpLogTest f)
  rw [← hUntilt]
  calc
    _ ≤ ∫ _y : D01LogSpace, K ∂d02TiltedDiagonalMeasure L :=
      norm_integral_le_of_norm_le (integrable_const K) hdom
    _ = _ := by
      simpa [K] using (integral_const_mul (μ := d02TiltedDiagonalMeasure L) K (fun _ : D01LogSpace => (1:ℝ)))

theorem d02FourProfileProduct_cap_support (ρ : Fin 4 → ℝ → ℂ)
    (a : Fin 4 → ℝ) (hρ : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k)) :
    d02FourCapSupport (d02FourProfileProduct ρ) a := by
  intro y hy
  have h₀ : ρ 0 (y.1 1) ≠ 0 := by
    intro h; exact hy (by simp [d02FourProfileProduct,h])
  have h₁ : ρ 1 (y.1 2) ≠ 0 := by
    intro h; exact hy (by simp [d02FourProfileProduct,h])
  have h₂ : ρ 2 (y.2 1) ≠ 0 := by
    intro h; exact hy (by simp [d02FourProfileProduct,h])
  have h₃ : ρ 3 (y.2 2) ≠ 0 := by
    intro h; exact hy (by simp [d02FourProfileProduct,h])
  exact ⟨(hρ 0 _ h₀).2,(hρ 1 _ h₁).2,(hρ 2 _ h₂).2,(hρ 3 _ h₃).2⟩

private theorem d02ComplexLaplaceWeight_norm_bound {C : ℝ}
    (ab : PolarShiftSpace) (ha : ∀ i, -C ≤ (ab.1 i).re)
    (hb : ∀ i, -C ≤ (ab.2 i).re) {y : D01LogSpace}
    (hy : y ∈ d01PositiveOrthant) :
    ‖d01ComplexLaplaceWeight ab y‖ ≤ Real.exp (C*d01LogTotal y) := by
  rw [d01ComplexLaplaceWeight_norm]
  unfold d01LaplaceWeight
  apply Real.exp_le_exp.mpr
  have hl : -C*(∑ i, y.1 i) ≤ ∑ i, (ab.1 i).re*y.1 i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (ha i) (hy.1 i))
  have hr : -C*(∑ i, y.2 i) ≤ ∑ i, (ab.2 i).re*y.2 i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hb i) (hy.2 i))
  unfold d01LogTotal
  nlinarith

private theorem d02FourProfileProduct_norm_bound
    (ρ : Fin 4 → ℝ → ℂ) (b : Fin 4 → ℝ) (hb0 : ∀ k, 0 ≤ b k)
    (hb : ∀ k t, ‖ρ k t‖ ≤ b k) (y : D01LogSpace) :
    ‖d02FourProfileProduct ρ y‖ ≤ b 0*b 1*b 2*b 3 := by
  simp only [d02FourProfileProduct,norm_mul]
  have h₀₁ := mul_le_mul (hb 0 (y.1 1)) (hb 1 (y.1 2)) (norm_nonneg _) (hb0 0)
  have h₀₁₂ := mul_le_mul h₀₁ (hb 2 (y.2 1)) (norm_nonneg _) (mul_nonneg (hb0 0) (hb0 1))
  exact mul_le_mul h₀₁₂ (hb 3 (y.2 2)) (norm_nonneg _)
    (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (hb0 2))

theorem d02ShiftedFourProfile_growth
    (ρ : Fin 4 → ℝ → ℂ) (a b : Fin 4 → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hb0 : ∀ k, 0 ≤ b k) (hb : ∀ k t, ‖ρ k t‖ ≤ b k)
    (ab : PolarShiftSpace) (ha : ∀ i, -C ≤ (ab.1 i).re)
    (hbshift : ∀ i, -C ≤ (ab.2 i).re) :
    ∀ y ∈ d01PositiveOrthant,
      ‖d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y‖ ≤
        (b 0*b 1*b 2*b 3*Real.exp (C*d02ProfileCapSum a))*
          Real.exp (C*d02LogCutCoordinate y) := by
  have hprod0 : 0 ≤ b 0*b 1*b 2*b 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (hb0 2)) (hb0 3)
  intro y hy
  let f := fun y => d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y
  have hcap : d02FourCapSupport f a := by
    intro y hy
    have hp : d02FourProfileProduct ρ y ≠ 0 := by
      intro h
      exact hy (by simp [f,h])
    exact d02FourProfileProduct_cap_support ρ a hρcap y hp
  by_cases hfy : f y = 0
  · change ‖f y‖ ≤ _
    rw [hfy,norm_zero]
    exact mul_nonneg (mul_nonneg hprod0 (Real.exp_pos _).le) (Real.exp_pos _).le
  have ht := d02LogTotal_le_cut_add_caps hcap hfy
  have hnorm := d02ComplexLaplaceWeight_norm_bound ab ha hbshift hy
  have hprofile := d02FourProfileProduct_norm_bound ρ b hb0 hb y
  rw [norm_mul]
  calc
    _ ≤ Real.exp (C*d01LogTotal y)*(b 0*b 1*b 2*b 3) :=
      mul_le_mul hnorm hprofile (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (C*(d02LogCutCoordinate y+d02ProfileCapSum a))*(b 0*b 1*b 2*b 3) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ht hC)) hprod0
    _ = _ := by rw [mul_add, Real.exp_add]; ring

theorem d02DiagonalMeasure_shifted_four_profile_sharp_norm_bound
    (ρ : Fin 4 → ℝ → ℂ) (a b : Fin 4 → ℝ) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hb0 : ∀ k, 0 ≤ b k) (hb : ∀ k t, ‖ρ k t‖ ≤ b k)
    (ab : PolarShiftSpace) (ha : ∀ i, -C ≤ (ab.1 i).re)
    (hbshift : ∀ i, -C ≤ (ab.2 i).re) :
    ‖∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
      ∂d01DiagonalMeasure L‖ ≤
      (b 0*b 1*b 2*b 3*Real.exp (C*d02ProfileCapSum a))*
        Real.exp (d02ProfileCapSum a)*Real.exp (C+1)*
          (∫ _y : D01LogSpace, (1:ℝ) ∂d02TiltedDiagonalMeasure L) := by
  let f := fun y => d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y
  have hcap : d02FourCapSupport f a := by
    intro y hy
    have hp : d02FourProfileProduct ρ y ≠ 0 := by
      intro h
      exact hy (by simp [f,h])
    exact d02FourProfileProduct_cap_support ρ a hρcap y hp
  have hprod0 : 0 ≤ b 0*b 1*b 2*b 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (hb0 2)) (hb0 3)
  have h := d02DiagonalMeasure_sharp_profile_norm_bound a
    (B := b 0*b 1*b 2*b 3*Real.exp (C*d02ProfileCapSum a))
    (mul_nonneg hprod0 (Real.exp_pos _).le)
    hC hL f hcap (d02ShiftedFourProfile_growth ρ a b hC hρcap hb0 hb ab ha hbshift)
  have he : d02SharpLogTest f = fun y =>
      d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y := by
    funext y
    by_cases hq : d02LogCutCoordinate y ≤ 1 <;>
      simp [d02SharpLogTest,d02SharpLogRegion,f,hq]
  rwa [he] at h

theorem d02DiagonalMeasure_shifted_four_profile_gaussian_sharp_uniform
    (ρ : Fin 4 → ℝ → ℂ) (a b : Fin 4 → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hb0 : ∀ k, 0 ≤ b k) (hb : ∀ k t, ‖ρ k t‖ ≤ b k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ (ab : PolarShiftSpace) (c : ℝ),
      (∀ i, -C ≤ (ab.1 i).re) → (∀ i, -C ≤ (ab.2 i).re) → |c| ≤ C →
      ‖(∫ y, d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y*
          (d02GaussianLogWeight L (d02LogCutCoordinate y) c : ℂ) ∂d01DiagonalMeasure L) -
        ∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
          ∂d01DiagonalMeasure L‖ < ε := by
  let P := b 0*b 1*b 2*b 3
  let B := P*Real.exp (C*d02ProfileCapSum a)
  have hP0 : 0 ≤ P :=
    mul_nonneg (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (hb0 2)) (hb0 3)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  filter_upwards [d02DiagonalMeasure_gaussian_sharp_profile_uniform a hB0 hC hε]
    with L hL
  intro ab c ha hbshift hc
  let f := fun y => d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y
  have hfm : Measurable f := (d01ComplexLaplaceWeight_continuous ab).measurable.mul
    (d02FourProfileProduct_continuous ρ hρc).measurable
  have hcap : d02FourCapSupport f a := by
    intro y hy
    have hp : d02FourProfileProduct ρ y ≠ 0 := by
      intro h
      exact hy (by simp [f,h])
    exact d02FourProfileProduct_cap_support ρ a hρcap y hp
  have hbound : ∀ y ∈ d01PositiveOrthant,
      ‖f y‖ ≤ B*Real.exp (C*d02LogCutCoordinate y) := by
    intro y hy
    by_cases hfy : f y = 0
    · rw [hfy,norm_zero]
      positivity
    have ht := d02LogTotal_le_cut_add_caps hcap hfy
    have hnorm := d02ComplexLaplaceWeight_norm_bound ab ha hbshift hy
    have hprofile := d02FourProfileProduct_norm_bound ρ b hb0 hb y
    dsimp [f]
    rw [norm_mul]
    calc
      _ ≤ Real.exp (C*d01LogTotal y)*P :=
        mul_le_mul hnorm hprofile (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (C*(d02LogCutCoordinate y+d02ProfileCapSum a))*P :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left ht hC)) hP0
      _ = _ := by
        dsimp [B]
        rw [mul_add, Real.exp_add]
        ring
  have h := hL f c hfm hcap hbound hc
  have he : d02SharpLogTest f = fun y =>
      d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y := by
    funext y
    by_cases hq : d02LogCutCoordinate y ≤ 1 <;>
      simp [d02SharpLogTest,d02SharpLogRegion,f,hq]
  rwa [he] at h

theorem d02DiagonalMeasure_four_profile_gaussian_limit
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (ab : PolarShiftSpace)
    (c : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (ha : ∀ i, -C ≤ (ab.1 i).re) (hbshift : ∀ i, -C ≤ (ab.2 i).re)
    (hc : ∀ᶠ L : ℝ in atTop, |c L| ≤ C) :
    Tendsto (fun L : ℝ => ∫ y,
      d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y*
        (d02GaussianLogWeight L (d02LogCutCoordinate y) (c L) : ℂ)
          ∂d01DiagonalMeasure L) atTop
      (𝓝 ((arithmeticFactor : ℂ)*∫ x : D01EdgeSpace,
        d01ComplexLaplaceWeight ab (d01RowColumnSums x)*
          d02SharpLogTest (d02FourProfileProduct ρ) (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) := by
  have hρK : ∀ k, HasCompactSupport (ρ k) := by
    intro k
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := a k))
    intro t ht
    exact hρcap k t ht
  choose b hb using fun k => (hρK k).exists_bound_of_continuous (hρc k)
  have hb0 : ∀ k, 0 ≤ b k := fun k => (norm_nonneg (ρ k 0)).trans (hb k 0)
  have herr : Tendsto (fun L : ℝ =>
      (∫ y, d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y*
        (d02GaussianLogWeight L (d02LogCutCoordinate y) (c L) : ℂ) ∂d01DiagonalMeasure L) -
      ∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
        ∂d01DiagonalMeasure L) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [d02DiagonalMeasure_shifted_four_profile_gaussian_sharp_uniform
      ρ a b hC hρc hρcap hb0 hb hε, hc] with L hL hCL
    simpa only [dist_zero_right] using hL ab (c L) ha hbshift hCL
  have hsharp := d02DiagonalMeasure_four_profile_sharp_log_limit ρ a
    (d01ComplexLaplaceWeight ab) hρc hρcap (d01ComplexLaplaceWeight_continuous ab)
  simpa only [sub_add_cancel, zero_add] using herr.add hsharp

theorem d02GaussianPhysicalOffset_bound {τ : ℝ} (hτ : τ ∈ Icc (1:ℝ) 2) :
    |Real.log (2*Real.pi/τ)| ≤ |Real.log (2*Real.pi)|+Real.log 2 := by
  have hτ0 : 0 < τ := zero_lt_one.trans_le hτ.1
  have hπ0 : 0 < 2*Real.pi := by positivity
  have hlog0 : 0 ≤ Real.log τ := Real.log_nonneg hτ.1
  have hlog2 : Real.log τ ≤ Real.log 2 := Real.log_le_log hτ0 hτ.2
  rw [Real.log_div hπ0.ne' hτ0.ne']
  have h := abs_sub_le (Real.log (2*Real.pi)) 0 (Real.log τ)
  simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hlog0] at h
  linarith

theorem d02DiagonalMeasure_shifted_four_profile_physical_gaussian_sharp_uniform
    (ρ : Fin 4 → ℝ → ℂ) (a b : Fin 4 → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hOffset : |Real.log (2*Real.pi)|+Real.log 2 ≤ C)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hb0 : ∀ k, 0 ≤ b k) (hb : ∀ k t, ‖ρ k t‖ ≤ b k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ (ab : PolarShiftSpace) (τ : ℝ),
      (∀ i, -C ≤ (ab.1 i).re) → (∀ i, -C ≤ (ab.2 i).re) → τ ∈ Icc (1:ℝ) 2 →
      ‖(∫ y, d01ComplexLaplaceWeight ab y*d02FourProfileProduct ρ y*
          (d02GaussianV0 (2*Real.pi*Real.exp (L*d02LogCutCoordinate y)/
            (Real.exp L*τ)) : ℂ) ∂d01DiagonalMeasure L) -
        ∫ y, d01ComplexLaplaceWeight ab y*d02SharpLogTest (d02FourProfileProduct ρ) y
          ∂d01DiagonalMeasure L‖ < ε := by
  filter_upwards [d02DiagonalMeasure_shifted_four_profile_gaussian_sharp_uniform
    ρ a b hC hρc hρcap hb0 hb hε] with L hL
  intro ab τ ha hbshift hτ
  have hτ0 : 0 < τ := zero_lt_one.trans_le hτ.1
  have hc : |Real.log (2*Real.pi/τ)| ≤ C :=
    (d02GaussianPhysicalOffset_bound hτ).trans hOffset
  have h := hL ab (Real.log (2*Real.pi/τ)) ha hbshift hc
  simpa only [d02GaussianV0_logarithmic_identity L _ hτ0] using h

end
end SixthMoment
