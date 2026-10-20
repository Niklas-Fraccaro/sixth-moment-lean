import Sechstmoment.Denominator.Gram.PhaseDefinitions
import Sechstmoment.Denominator.Unbalanced.ActualMomentRegularity

namespace Sechstmoment
open MeasureTheory Set Complex Polynomial Filter Metric
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

private theorem d06_shifted_zeta_nonpole {T : ℝ} {s z : ℂ}
    (hL : 1≤Real.log T) (hs : 1< |s.im|) (hz : z∈sphere (0:ℂ) 1) :
    s+z/(Real.log T : ℂ)≠1 :=
  d04_shifted_zeta_nonpole_of_norm_le hL hs
    ((mem_sphere_zero_iff_norm.mp hz).le.trans hL)

theorem d06ExtremeMinusShiftedIntegrand_continuousOn {T : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    ContinuousOn (fun y : ℂ × (ℂ × ℝ) => (Φ (y.2.2 / T) : ℂ) * (criticalChi y.2.2)⁻¹ * (criticalChi y.2.2)⁻¹ *
      zetaCPlus T y.2.2 y.1 * zetaCMinus T y.2.2 y.2.1 *
      d06AllPositiveAmplifier T y.2.2 ρ)
      (sphere (0 : ℂ) 1 ×ˢ (sphere (0 : ℂ) 1 ×ˢ Icc T (2 * T))) := by
  have hplus : ContinuousOn (fun y : ℂ × (ℂ × ℝ) => zetaCPlus T y.2.2 y.1)
      (sphere (0 : ℂ) 1 ×ˢ (sphere (0 : ℂ) 1 ×ˢ Icc T (2 * T))) := by
    intro y hy
    unfold zetaCPlus shiftedZetaGenerator
    have ht : 1 < |(criticalLinePoint y.2.2).im| := by
      rw [criticalLinePoint_im, abs_of_pos (zero_lt_one.trans (hT.trans_le hy.2.2.1))]
      exact hT.trans_le hy.2.2.1
    have hz := (differentiableAt_riemannZeta
      (d06_shifted_zeta_nonpole hL ht hy.1)).continuousAt
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
      (d06_shifted_zeta_nonpole hL ht hy.2.1)).continuousAt
    have hmap : ContinuousWithinAt (fun u : ℂ × (ℂ × ℝ) =>
        1 - criticalLinePoint u.2.2 + u.2.1 / (Real.log T : ℂ))
        (sphere (0 : ℂ) 1 ×ˢ (sphere (0 : ℂ) 1 ×ˢ Icc T (2 * T))) y := by
      unfold criticalLinePoint
      fun_prop
    exact (by fun_prop : ContinuousWithinAt
      (fun y : ℂ × (ℂ × ℝ) => Complex.exp (y.2.1 / 2)) _ y).mul
      (hz.comp_continuousWithinAt (f := fun u : ℂ × (ℂ × ℝ) =>
        1 - criticalLinePoint u.2.2 + u.2.1 / (Real.log T : ℂ)) (x := y) hmap)
  have ham := d06AllPositiveAmplifier_continuous hT ρ A hρsupport
  have hcut : Continuous (fun y : ℂ × (ℂ × ℝ) =>
      (Φ (y.2.2 / T) : ℂ) * (criticalChi y.2.2)⁻¹ * (criticalChi y.2.2)⁻¹) := by
    exact ((by fun_prop : Continuous (fun y : ℂ × (ℂ × ℝ) => (Φ (y.2.2 / T) : ℂ))).mul
      (d04_criticalChi_inv_continuous.comp (by fun_prop))).mul
      (d04_criticalChi_inv_continuous.comp (by fun_prop))
  exact ((hcut.continuousOn.mul hplus).mul hminus).mul
    ((ham.comp (by fun_prop : Continuous (fun y : ℂ × (ℂ × ℝ) => y.2.2))).continuousOn)

private theorem d06_height_cutoff_zero {T t : ℝ} (hT : 0 < T)
    (Φ : ℝ → ℝ) (hΦs : tsupport Φ ⊆ Icc 1 2) (ht : t ∉ Icc T (2 * T)) :
    Φ (t / T) = 0 := by
  by_contra hn
  have hx := hΦs (subset_tsupport Φ hn)
  apply ht
  constructor
  · simpa using (le_div_iff₀ hT).mp hx.1
  · exact (div_le_iff₀ hT).mp hx.2


theorem d06ExtremeMinusShiftedMoment_eq_window_integral {T : ℝ} (hT : 0 < T)
    (σ : Fin 2 → ℂ) (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ)
    (hΦs : tsupport Φ ⊆ Icc 1 2) :
    d06ExtremeMinusShiftedMoment T σ ρ Φ = ∫ t in Icc T (2 * T),
      (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * (criticalChi t)⁻¹ * zetaCPlus T t (σ 0) * zetaCMinus T t (σ 1) *
        d06AllPositiveAmplifier T t ρ := by
  unfold d06ExtremeMinusShiftedMoment
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Icc T (2 * T)
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht]
    rw [d06_height_cutoff_zero hT Φ hΦs ht]
    simp


theorem d06ExtremeMinusShiftedMoment_integrable_of_mem_circles {T : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T) {z w : ℂ}
    (hz : z ∈ sphere (0 : ℂ) 1) (hw : w ∈ sphere (0 : ℂ) 1)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    Integrable (fun t : ℝ => (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * (criticalChi t)⁻¹ * zetaCPlus T t z *
      zetaCMinus T t w * d06AllPositiveAmplifier T t ρ) := by
  have hc := (d06ExtremeMinusShiftedIntegrand_continuousOn hT hL ρ A hρsupport Φ hΦ).comp
    (by fun_prop : ContinuousOn (fun t : ℝ => (z,(w,t))) (Icc T (2 * T)))
    (fun t ht => ⟨hz,hw,ht⟩)
  have hci : IntegrableOn (fun t : ℝ => (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * (criticalChi t)⁻¹ * zetaCPlus T t z *
      zetaCMinus T t w * d06AllPositiveAmplifier T t ρ) (Icc T (2 * T)) volume :=
    hc.integrableOn_compact isCompact_Icc
  have hi := hci.integrable_indicator measurableSet_Icc
  apply hi.congr
  filter_upwards [] with t
  by_cases ht : t ∈ Icc T (2 * T)
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht]
    rw [d06_height_cutoff_zero (zero_lt_one.trans hT) Φ hΦs ht]
    simp

theorem d06ExtremeMinusShiftedMoment_continuousOn_two_circles {T : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ContinuousOn (fun y : ℂ × ℂ => d06ExtremeMinusShiftedMoment T ![y.1,y.2] ρ Φ)
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
  let F : S → ℝ → ℂ := fun y t => (Φ (τ t / T) : ℂ) * (criticalChi (τ t))⁻¹ * (criticalChi (τ t))⁻¹ *
    zetaCPlus T (τ t) y.val.1 * zetaCMinus T (τ t) y.val.2 *
      d06AllPositiveAmplifier T (τ t) ρ
  have hc : Continuous (Function.uncurry F) := by
    change Continuous (fun y : S × ℝ => (Φ (τ y.2 / T) : ℂ) *
      (criticalChi (τ y.2))⁻¹ * (criticalChi (τ y.2))⁻¹ * zetaCPlus T (τ y.2) y.1.val.1 *
        zetaCMinus T (τ y.2) y.1.val.2 * d06AllPositiveAmplifier T (τ y.2) ρ)
    exact (d06ExtremeMinusShiftedIntegrand_continuousOn hT hL ρ A hρsupport Φ hΦ).comp_continuous
      (f := fun y : S × ℝ => (y.1.val.1,(y.1.val.2,τ y.2)))
      (by dsimp [τ]; fun_prop : Continuous
        (fun y : S × ℝ => (y.1.val.1,(y.1.val.2,τ y.2))))
      (fun y => ⟨y.1.property.1, y.1.property.2, hτ y.2⟩)
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    ((isCompact_sphere _ _).prod (isCompact_sphere _ _))
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (S.domRestrict (fun y : ℂ × ℂ =>
      d06ExtremeMinusShiftedMoment T ![y.1,y.2] ρ Φ)) = fun y : S => ∫ t in E, F y t := by
    funext y
    change d06ExtremeMinusShiftedMoment T ![y.val.1,y.val.2] ρ Φ = _
    rw [d06ExtremeMinusShiftedMoment_eq_window_integral (zero_lt_one.trans hT) _ ρ Φ hΦs]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only [F]
    rw [hτeq t ht]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [heq]
  exact continuous_parametric_integral_of_continuous hc isCompact_Icc

theorem d06ExtremeMinusShiftedMoment_eventually_continuousOn_two_circles
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ∀ᶠ T : ℝ in atTop, ContinuousOn
      (fun y : ℂ × ℂ => d06ExtremeMinusShiftedMoment T ![y.1,y.2] ρ Φ)
      (sphere (0 : ℂ) 1 ×ˢ sphere (0 : ℂ) 1) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with T hT hL
  exact d06ExtremeMinusShiftedMoment_continuousOn_two_circles hT hL ρ A hρsupport Φ hΦ.continuous hΦs

theorem d06ExtremeMinusPolynomialMoment_eq_two_circle {T : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    d06ExtremeMinusPolynomialMoment T p q ρ Φ =
      d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
        d06ExtremeMinusShiftedMoment T ![z,w] ρ Φ)) := by
  let E : Set ℝ := Icc T (2 * T)
  let F : ℂ → ℂ → ℝ → ℂ := fun z w t => (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * (criticalChi t)⁻¹ *
    zetaCPlus T t z * zetaCMinus T t w * d06AllPositiveAmplifier T t ρ
  have hzero (z w : ℂ) : (∫ t : ℝ, F z w t) = ∫ t in E, F z w t := by
    simpa only [d06ExtremeMinusShiftedMoment, F, E, Matrix.cons_val_zero,
      Matrix.cons_val_one] using d06ExtremeMinusShiftedMoment_eq_window_integral
        (zero_lt_one.trans hT) ![z,w] ρ Φ hΦs
  have hm : d06ExtremeMinusPolynomialMoment T p q ρ Φ =
      ∫ t in E, (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * (criticalChi t)⁻¹ * zetaCp T t p *
        zetaPolynomialDerivative T q (1 - criticalLinePoint t) * d06AllPositiveAmplifier T t ρ := by
    unfold d06ExtremeMinusPolynomialMoment
    change (∫ t : ℝ, (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * (criticalChi t)⁻¹ * zetaCp T t p *
      zetaPolynomialDerivative T q (1 - criticalLinePoint t) * d06AllPositiveAmplifier T t ρ) =
      ∫ t in Icc T (2 * T), (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * (criticalChi t)⁻¹ * zetaCp T t p *
        zetaPolynomialDerivative T q (1 - criticalLinePoint t) * d06AllPositiveAmplifier T t ρ
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ∈ Icc T (2 * T)
    · simp only [indicator_of_mem ht]
    · simp only [indicator_of_notMem ht]
      rw [d06_height_cutoff_zero (zero_lt_one.trans hT) Φ hΦs ht]
      simp
  have hc := d02PolynomialCircle_two_real_setIntegral p q E isCompact_Icc F
    (d06ExtremeMinusShiftedIntegrand_continuousOn hT hL ρ A hρsupport Φ hΦ)
  have hfactor (t : ℝ) : d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => F z w t)) =
      (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * (criticalChi t)⁻¹ * d02PolynomialCircle p (zetaCPlus T t) *
        d02PolynomialCircle q (zetaCMinus T t) * d06AllPositiveAmplifier T t ρ := by
    dsimp only [F]
    simp_rw [d02PolynomialCircle_mul_const, d02PolynomialCircle_const_mul,
      d02PolynomialCircle_mul_const]
    rw [d02PolynomialCircle_const_mul]
  rw [hm]
  symm
  unfold d06ExtremeMinusShiftedMoment
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => ∫ t : ℝ, F z w t)) = _
  simp_rw [hzero]
  rw [hc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  change d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => F z w t)) =
    (Φ (t / T) : ℂ) * (criticalChi t)⁻¹ * (criticalChi t)⁻¹ * zetaCp T t p *
      zetaPolynomialDerivative T q (1 - criticalLinePoint t) * d06AllPositiveAmplifier T t ρ
  have ht' : 1 < |t| := by
    rw [abs_of_pos (zero_lt_one.trans (hT.trans_le ht.1))]
    exact hT.trans_le ht.1
  rw [hfactor t, ← d02_zetaCp_eq_circle hT hL ht',
    ← d02_lower_zetaPolynomial_eq_circle hT hL ht']

theorem d06ExtremeMinusPolynomialMoment_eventually_eq_two_circle (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ∀ᶠ T : ℝ in atTop, d06ExtremeMinusPolynomialMoment T p q ρ Φ =
      d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
        d06ExtremeMinusShiftedMoment T ![z,w] ρ Φ)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with T hT hL
  exact d06ExtremeMinusPolynomialMoment_eq_two_circle hT hL p q ρ A hρsupport Φ hΦ.continuous hΦs

theorem d06ExtremeMinusPolynomialMoment_tendsto_of_pointwise_shifted
    (p q : ℝ[X]) (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (g : ℂ → ℂ → ℂ) (C : ℝ)
    (hbound : ∀ᶠ T : ℝ in atTop, ∀ z ∈ sphere (0 : ℂ) 1,
      ∀ w ∈ sphere (0 : ℂ) 1,
      ‖d06ExtremeMinusShiftedMoment T ![z,w] ρ Φ / (T * (Real.log T)^9 : ℂ)‖ ≤ C)
    (hlim : ∀ z ∈ sphere (0 : ℂ) 1, ∀ w ∈ sphere (0 : ℂ) 1,
      Tendsto (fun T : ℝ => d06ExtremeMinusShiftedMoment T ![z,w] ρ Φ /
        (T * (Real.log T)^9 : ℂ)) atTop (𝓝 (g z w))) :
    Tendsto (fun T : ℝ => d06ExtremeMinusPolynomialMoment T p q ρ Φ /
      (T * (Real.log T)^9 : ℂ)) atTop
      (𝓝 (d02PolynomialCircle p (fun z => d02PolynomialCircle q (g z)))) := by
  have hc : ∀ᶠ T : ℝ in atTop, ContinuousOn
      (fun y : ℂ × ℂ => d06ExtremeMinusShiftedMoment T ![y.1,y.2] ρ Φ /
        (T * (Real.log T)^9 : ℂ))
      (sphere (0 : ℂ) 1 ×ˢ sphere (0 : ℂ) 1) := by
    filter_upwards [d06ExtremeMinusShiftedMoment_eventually_continuousOn_two_circles
      ρ A hρsupport Φ hΦ hΦs] with T hT
    simp only [div_eq_mul_inv]
    exact hT.mul continuousOn_const
  have ht := d02PolynomialCircle_two_tendsto_of_dominated p q hc hbound hlim
  apply ht.congr'
  filter_upwards [d06ExtremeMinusPolynomialMoment_eventually_eq_two_circle
    p q ρ A hρsupport Φ hΦ hΦs] with T hT
  rw [hT]
  simp_rw [div_eq_mul_inv, d02PolynomialCircle_mul_const]

end
end Sechstmoment
