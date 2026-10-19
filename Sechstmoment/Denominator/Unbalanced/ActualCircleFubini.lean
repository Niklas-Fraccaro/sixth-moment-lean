import Sechstmoment.Denominator.Balanced.ActualCircleFubini
import Sechstmoment.Denominator.Unbalanced.MomentDefinitions

/-! Exact Cauchy extraction for the actual unbalanced height moment. The
unit phase is continuous on the whole critical line; the height window and
both contours have the proved compact product integrability. -/
namespace Sechstmoment
open MeasureTheory Set Complex Polynomial Filter Metric
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 800000

/-- The archimedean phase has no critical-line singularity. -/
theorem d04_criticalChi_continuous : Continuous criticalChi := by
  have hc : Continuous criticalLinePoint := by unfold criticalLinePoint; fun_prop
  have hi : Continuous (fun t => (Gammaℝ (criticalLinePoint t))⁻¹) :=
    differentiable_Gammaℝ_inv.continuous.comp hc
  have hg : Continuous (fun t => Gammaℝ (criticalLinePoint t)) := by
    have h := hi.inv₀ (fun t => inv_ne_zero (gammaReal_criticalLinePoint_ne_zero t))
    change Continuous (fun t => ((Gammaℝ (criticalLinePoint t))⁻¹)⁻¹) at h
    simpa only [inv_inv] using h
  have he : criticalChi = fun t =>
      star (Gammaℝ (criticalLinePoint t)) / Gammaℝ (criticalLinePoint t) := by
    funext t
    exact criticalChi_eq_conj_div t
  rw [he]
  exact hg.star.div hg gammaReal_criticalLinePoint_ne_zero

theorem d04_criticalChi_ne_zero (t : ℝ) : criticalChi t ≠ 0 := by
  intro h
  have hn := criticalChi_norm t
  rw [h, norm_zero] at hn
  norm_num at hn

theorem d04_criticalChi_inv_continuous : Continuous (fun t => (criticalChi t)⁻¹) :=
  d04_criticalChi_continuous.inv₀ d04_criticalChi_ne_zero

private theorem d04_shifted_zeta_nonpole {T : ℝ} {s z : ℂ}
    (hL : 1 ≤ Real.log T) (hs : 1 < |s.im|) (hz : z ∈ sphere (0 : ℂ) 1) :
    s + z / (Real.log T : ℂ) ≠ 1 := by
  have hLp : 0 < Real.log T := zero_lt_one.trans_le hL
  have hzim : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans
    (mem_sphere_zero_iff_norm.mp hz).le
  intro h
  have hi := congrArg Complex.im h
  simp only [add_im, Complex.div_ofReal_im, one_im] at hi
  have habs : |s.im| = |z.im| / Real.log T := by
    have he : s.im = -(z.im / Real.log T) := by linarith
    rw [he, abs_neg, abs_div, abs_of_pos hLp]
  have hdiv : |z.im| / Real.log T ≤ 1 :=
    (div_le_iff₀ hLp).mpr (by simpa using hzim.trans hL)
  linarith

private theorem d04_profileDirichletSum_continuous {T : ℝ} (hT : 1 < T)
    (f : ℝ → ℝ) (a : ℝ) (hf : tsupport f ⊆ Icc 0 a) :
    Continuous (profileDirichletSum T f) := by
  have hz : ∀ x : ℝ, a < x → f x = 0 := by
    intro x hx
    by_contra hn
    exact (not_le_of_gt hx) (hf (subset_tsupport f hn)).2
  have he := profileDirichletSum_eq_finite hT a f hz
  change Continuous (fun s : ℂ => profileDirichletSum T f s)
  simp_rw [he]
  apply continuous_finsetSum
  intro n hn
  have hne : (n + 1 : ℂ) ≠ 0 := by
    have hp : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    exact_mod_cast hp.ne'
  simp_rw [Complex.cpow_def_of_ne_zero hne]
  have hden (s : ℂ) : Complex.exp (Complex.log (n + 1 : ℂ) * s) ≠ 0 :=
    Complex.exp_ne_zero _
  fun_prop

theorem d04UnbalancedAmplifier_continuous {T : ℝ} (hT : 1 < T)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i)) :
    Continuous (fun t => d04UnbalancedAmplifier T t ρ) := by
  have hp (i : Fin 4) := d04_profileDirichletSum_continuous hT (ρ i) (A i) (hρsupport i)
  unfold d04UnbalancedAmplifier
  have hc : Continuous criticalLinePoint := by unfold criticalLinePoint; fun_prop
  exact (((hp 0).comp hc).mul ((hp 1).comp hc)).mul
    ((hp 2).comp hc) |>.mul
      ((hp 3).comp (continuous_const.sub hc))

/-- The actual zeta factors are jointly continuous on the supported t window
and both unit circles because their arguments cannot meet the zeta pole. -/
theorem d04UnbalancedShiftedIntegrand_continuousOn {T : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    ContinuousOn (fun y : ℂ × (ℂ × ℝ) => (Φ (y.2.2 / T) : ℂ) * (criticalChi y.2.2)⁻¹ *
      zetaCPlus T y.2.2 y.1 * zetaCMinus T y.2.2 y.2.1 *
      d04UnbalancedAmplifier T y.2.2 ρ)
      (sphere (0 : ℂ) 1 ×ˢ (sphere (0 : ℂ) 1 ×ˢ Icc T (2 * T))) := by
  have hplus : ContinuousOn (fun y : ℂ × (ℂ × ℝ) => zetaCPlus T y.2.2 y.1)
      (sphere (0 : ℂ) 1 ×ˢ (sphere (0 : ℂ) 1 ×ˢ Icc T (2 * T))) := by
    intro y hy
    unfold zetaCPlus shiftedZetaGenerator
    have ht : 1 < |(criticalLinePoint y.2.2).im| := by
      rw [criticalLinePoint_im, abs_of_pos (zero_lt_one.trans (hT.trans_le hy.2.2.1))]
      exact hT.trans_le hy.2.2.1
    have hz := (differentiableAt_riemannZeta
      (d04_shifted_zeta_nonpole hL ht hy.1)).continuousAt
    have hmap : ContinuousWithinAt (fun u : ℂ × (ℂ × ℝ) =>
        criticalLinePoint u.2.2 + u.1 / (Real.log T : ℂ))
        (sphere (0 : ℂ) 1 ×ˢ (sphere (0 : ℂ) 1 ×ˢ Icc T (2 * T))) y := by
      unfold criticalLinePoint
      fun_prop
    exact (by fun_prop : ContinuousWithinAt
      (fun y : ℂ × (ℂ × ℝ) => Complex.exp (y.1 / 2)) _ y).mul
      (hz.comp_continuousWithinAt (f := fun u : ℂ × (ℂ × ℝ) =>
        criticalLinePoint u.2.2 + u.1 / (Real.log T : ℂ)) (x := y) hmap)
  have hminus : ContinuousOn (fun y : ℂ × (ℂ × ℝ) => zetaCMinus T y.2.2 y.2.1)
      (sphere (0 : ℂ) 1 ×ˢ (sphere (0 : ℂ) 1 ×ˢ Icc T (2 * T))) := by
    intro y hy
    unfold zetaCMinus shiftedZetaGenerator
    have ht : 1 < |(1 - criticalLinePoint y.2.2).im| := by
      simp only [sub_im, one_im, criticalLinePoint_im, zero_sub, abs_neg]
      rw [abs_of_pos (zero_lt_one.trans (hT.trans_le hy.2.2.1))]
      exact hT.trans_le hy.2.2.1
    have hz := (differentiableAt_riemannZeta
      (d04_shifted_zeta_nonpole hL ht hy.2.1)).continuousAt
    have hmap : ContinuousWithinAt (fun u : ℂ × (ℂ × ℝ) =>
        1 - criticalLinePoint u.2.2 + u.2.1 / (Real.log T : ℂ))
        (sphere (0 : ℂ) 1 ×ˢ (sphere (0 : ℂ) 1 ×ˢ Icc T (2 * T))) y := by
      unfold criticalLinePoint
      fun_prop
    exact (by fun_prop : ContinuousWithinAt
      (fun y : ℂ × (ℂ × ℝ) => Complex.exp (y.2.1 / 2)) _ y).mul
      (hz.comp_continuousWithinAt (f := fun u : ℂ × (ℂ × ℝ) =>
        1 - criticalLinePoint u.2.2 + u.2.1 / (Real.log T : ℂ)) (x := y) hmap)
  have ham := d04UnbalancedAmplifier_continuous hT ρ A hρsupport
  have hcut : Continuous (fun y : ℂ × (ℂ × ℝ) =>
      (Φ (y.2.2 / T) : ℂ) * (criticalChi y.2.2)⁻¹) := by
    apply Continuous.mul (by fun_prop)
    exact d04_criticalChi_inv_continuous.comp (by fun_prop)
  exact ((hcut.continuousOn.mul hplus).mul hminus).mul
    ((ham.comp (by fun_prop : Continuous (fun y : ℂ × (ℂ × ℝ) => y.2.2))).continuousOn)

private theorem d04_height_cutoff_zero {T t : ℝ} (hT : 0 < T)
    (Φ : ℝ → ℝ) (hΦs : tsupport Φ ⊆ Icc 1 2) (ht : t ∉ Icc T (2 * T)) :
    Φ (t / T) = 0 := by
  by_contra hn
  have hx := hΦs (subset_tsupport Φ hn)
  apply ht
  constructor
  · simpa using (le_div_iff₀ hT).mp hx.1
  · exact (div_le_iff₀ hT).mp hx.2


theorem d04UnbalancedShiftedMoment_eq_window_integral {T : ℝ} (hT : 0 < T)
    (σ : Fin 2 → ℂ) (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ)
    (hΦs : tsupport Φ ⊆ Icc 1 2) :
    d04UnbalancedShiftedMoment T σ ρ Φ = ∫ t in Icc T (2 * T),
      (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * zetaCPlus T t (σ 0) * zetaCMinus T t (σ 1) *
        d04UnbalancedAmplifier T t ρ := by
  unfold d04UnbalancedShiftedMoment
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Icc T (2 * T)
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht]
    rw [d04_height_cutoff_zero hT Φ hΦs ht]
    simp


/-- The actual supported height integrand is integrable for the Cauchy shifts. -/
theorem d04UnbalancedShiftedMoment_integrable_of_mem_circles {T : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T) {z w : ℂ}
    (hz : z ∈ sphere (0 : ℂ) 1) (hw : w ∈ sphere (0 : ℂ) 1)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    Integrable (fun t : ℝ => (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * zetaCPlus T t z *
      zetaCMinus T t w * d04UnbalancedAmplifier T t ρ) := by
  have hc := (d04UnbalancedShiftedIntegrand_continuousOn hT hL ρ A hρsupport Φ hΦ).comp
    (by fun_prop : ContinuousOn (fun t : ℝ => (z,(w,t))) (Icc T (2 * T)))
    (fun t ht => ⟨hz,hw,ht⟩)
  have hci : IntegrableOn (fun t : ℝ => (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * zetaCPlus T t z *
      zetaCMinus T t w * d04UnbalancedAmplifier T t ρ) (Icc T (2 * T)) volume :=
    hc.integrableOn_compact isCompact_Icc
  have hi := hci.integrable_indicator measurableSet_Icc
  apply hi.congr
  filter_upwards [] with t
  by_cases ht : t ∈ Icc T (2 * T)
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht]
    rw [d04_height_cutoff_zero (zero_lt_one.trans hT) Φ hΦs ht]
    simp

/-- Continuity of the actual height moment in both Cauchy shifts follows from
joint compact regularity; no convergence hypothesis is needed. -/
theorem d04UnbalancedShiftedMoment_continuousOn_two_circles {T : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ContinuousOn (fun y : ℂ × ℂ => d04UnbalancedShiftedMoment T ![y.1,y.2] ρ Φ)
      (sphere (0 : ℂ) 1 ×ˢ sphere (0 : ℂ) 1) := by
  let S : Set (ℂ × ℂ) := sphere (0 : ℂ) 1 ×ˢ sphere (0 : ℂ) 1
  let E : Set ℝ := Icc T (2 * T)
  let τ : ℝ → ℝ := fun t => max T (min t (2 * T))
  have hτ (t : ℝ) : τ t ∈ E := by
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_right _ _)
  have hτeq (t : ℝ) (ht : t ∈ E) : τ t = t := by
    dsimp [τ]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  let F : S → ℝ → ℂ := fun y t => (Φ (τ t / T) : ℂ) * (criticalChi (τ t))⁻¹ *
    zetaCPlus T (τ t) y.val.1 * zetaCMinus T (τ t) y.val.2 *
      d04UnbalancedAmplifier T (τ t) ρ
  have hc : Continuous (Function.uncurry F) := by
    change Continuous (fun y : S × ℝ => (Φ (τ y.2 / T) : ℂ) *
      (criticalChi (τ y.2))⁻¹ * zetaCPlus T (τ y.2) y.1.val.1 *
        zetaCMinus T (τ y.2) y.1.val.2 * d04UnbalancedAmplifier T (τ y.2) ρ)
    exact (d04UnbalancedShiftedIntegrand_continuousOn hT hL ρ A hρsupport Φ hΦ).comp_continuous
      (f := fun y : S × ℝ => (y.1.val.1,(y.1.val.2,τ y.2)))
      (by dsimp [τ]; fun_prop : Continuous
        (fun y : S × ℝ => (y.1.val.1,(y.1.val.2,τ y.2))))
      (fun y => ⟨y.1.property.1, y.1.property.2, hτ y.2⟩)
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    ((isCompact_sphere _ _).prod (isCompact_sphere _ _))
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (S.domRestrict (fun y : ℂ × ℂ =>
      d04UnbalancedShiftedMoment T ![y.1,y.2] ρ Φ)) = fun y : S => ∫ t in E, F y t := by
    funext y
    change d04UnbalancedShiftedMoment T ![y.val.1,y.val.2] ρ Φ = _
    rw [d04UnbalancedShiftedMoment_eq_window_integral (zero_lt_one.trans hT) _ ρ Φ hΦs]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only [F]
    rw [hτeq t ht]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [heq]
  exact continuous_parametric_integral_of_continuous hc isCompact_Icc

theorem d04UnbalancedShiftedMoment_eventually_continuousOn_two_circles
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ∀ᶠ T : ℝ in atTop, ContinuousOn
      (fun y : ℂ × ℂ => d04UnbalancedShiftedMoment T ![y.1,y.2] ρ Φ)
      (sphere (0 : ℂ) 1 ×ˢ sphere (0 : ℂ) 1) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with T hT hL
  exact d04UnbalancedShiftedMoment_continuousOn_two_circles hT hL ρ A hρsupport Φ hΦ.continuous hΦs

/-- Literal Cauchy extraction of the actual height moment, with compact
integrability proved rather than assumed. -/
theorem d04UnbalancedPolynomialMoment_eq_two_circle {T : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    d04UnbalancedPolynomialMoment T p q ρ Φ =
      d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
        d04UnbalancedShiftedMoment T ![z,w] ρ Φ)) := by
  let E : Set ℝ := Icc T (2 * T)
  let F : ℂ → ℂ → ℝ → ℂ := fun z w t => (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ *
    zetaCPlus T t z * zetaCMinus T t w * d04UnbalancedAmplifier T t ρ
  have hzero (z w : ℂ) : (∫ t : ℝ, F z w t) = ∫ t in E, F z w t := by
    simpa only [d04UnbalancedShiftedMoment, F, E, Matrix.cons_val_zero,
      Matrix.cons_val_one] using d04UnbalancedShiftedMoment_eq_window_integral
        (zero_lt_one.trans hT) ![z,w] ρ Φ hΦs
  have hm : d04UnbalancedPolynomialMoment T p q ρ Φ =
      ∫ t in E, (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * zetaCp T t p *
        zetaPolynomialDerivative T q (1 - criticalLinePoint t) * d04UnbalancedAmplifier T t ρ := by
    unfold d04UnbalancedPolynomialMoment
    change (∫ t : ℝ, (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * zetaCp T t p *
      zetaPolynomialDerivative T q (1 - criticalLinePoint t) * d04UnbalancedAmplifier T t ρ) =
      ∫ t in Icc T (2 * T), (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * zetaCp T t p *
        zetaPolynomialDerivative T q (1 - criticalLinePoint t) * d04UnbalancedAmplifier T t ρ
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ∈ Icc T (2 * T)
    · simp only [indicator_of_mem ht]
    · simp only [indicator_of_notMem ht]
      rw [d04_height_cutoff_zero (zero_lt_one.trans hT) Φ hΦs ht]
      simp
  have hc := d02PolynomialCircle_two_real_setIntegral p q E isCompact_Icc F
    (d04UnbalancedShiftedIntegrand_continuousOn hT hL ρ A hρsupport Φ hΦ)
  have hfactor (t : ℝ) : d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => F z w t)) =
      (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * d02PolynomialCircle p (zetaCPlus T t) *
        d02PolynomialCircle q (zetaCMinus T t) * d04UnbalancedAmplifier T t ρ := by
    dsimp only [F]
    simp_rw [d02PolynomialCircle_mul_const, d02PolynomialCircle_const_mul,
      d02PolynomialCircle_mul_const]
    rw [d02PolynomialCircle_const_mul]
  rw [hm]
  symm
  unfold d04UnbalancedShiftedMoment
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => ∫ t : ℝ, F z w t)) = _
  simp_rw [hzero]
  rw [hc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  change d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => F z w t)) =
    (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * zetaCp T t p *
      zetaPolynomialDerivative T q (1 - criticalLinePoint t) * d04UnbalancedAmplifier T t ρ
  have ht' : 1 < |t| := by
    rw [abs_of_pos (zero_lt_one.trans (hT.trans_le ht.1))]
    exact hT.trans_le ht.1
  rw [hfactor t, ← d02_zetaCp_eq_circle hT hL ht',
    ← d02_lower_zetaPolynomial_eq_circle hT hL ht']

/-- The preceding exact identity applies eventually to the actual T family. -/
theorem d04UnbalancedPolynomialMoment_eventually_eq_two_circle (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ∀ᶠ T : ℝ in atTop, d04UnbalancedPolynomialMoment T p q ρ Φ =
      d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
        d04UnbalancedShiftedMoment T ![z,w] ρ Φ)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with T hT hL
  exact d04UnbalancedPolynomialMoment_eq_two_circle hT hL p q ρ A hρsupport Φ hΦ.continuous hΦs

/-- Pointwise shifted height limits and a bounded shift box imply the actual
polynomial height limit through the two proved Cauchy contour swaps. -/
theorem d04UnbalancedPolynomialMoment_tendsto_of_pointwise_shifted
    (p q : ℝ[X]) (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (g : ℂ → ℂ → ℂ) (C : ℝ)
    (hbound : ∀ᶠ T : ℝ in atTop, ∀ z ∈ sphere (0 : ℂ) 1,
      ∀ w ∈ sphere (0 : ℂ) 1,
      ‖d04UnbalancedShiftedMoment T ![z,w] ρ Φ / (T * (Real.log T)^9 : ℂ)‖ ≤ C)
    (hlim : ∀ z ∈ sphere (0 : ℂ) 1, ∀ w ∈ sphere (0 : ℂ) 1,
      Tendsto (fun T : ℝ => d04UnbalancedShiftedMoment T ![z,w] ρ Φ /
        (T * (Real.log T)^9 : ℂ)) atTop (𝓝 (g z w))) :
    Tendsto (fun T : ℝ => d04UnbalancedPolynomialMoment T p q ρ Φ /
      (T * (Real.log T)^9 : ℂ)) atTop
      (𝓝 (d02PolynomialCircle p (fun z => d02PolynomialCircle q (g z)))) := by
  have hc : ∀ᶠ T : ℝ in atTop, ContinuousOn
      (fun y : ℂ × ℂ => d04UnbalancedShiftedMoment T ![y.1,y.2] ρ Φ /
        (T * (Real.log T)^9 : ℂ))
      (sphere (0 : ℂ) 1 ×ˢ sphere (0 : ℂ) 1) := by
    filter_upwards [d04UnbalancedShiftedMoment_eventually_continuousOn_two_circles
      ρ A hρsupport Φ hΦ hΦs] with T hT
    simp only [div_eq_mul_inv]
    exact hT.mul continuousOn_const
  have ht := d02PolynomialCircle_two_tendsto_of_dominated p q hc hbound hlim
  apply ht.congr'
  filter_upwards [d04UnbalancedPolynomialMoment_eventually_eq_two_circle
    p q ρ A hρsupport Φ hΦ hΦs] with T hT
  rw [hT]
  simp_rw [div_eq_mul_inv, d02PolynomialCircle_mul_const]

end
end Sechstmoment
