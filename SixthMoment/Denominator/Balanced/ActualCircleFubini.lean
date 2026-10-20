import Mathlib.MeasureTheory.Integral.Prod
import SixthMoment.Denominator.Balanced.MomentDefinitions
import SixthMoment.Zeta.PolynomialCircle

namespace SixthMoment
open MeasureTheory Set Complex Polynomial Filter Metric
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

theorem d02CircleExtract_continuousOn_compact_parameter {A : Type*}
    [TopologicalSpace A] [FirstCountableTopology A] [T2Space A]
    (S : Set A) (hS : IsCompact S) (m : ℕ) (F : A → ℂ → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (S ×ˢ sphere (0 : ℂ) 1)) :
    ContinuousOn (fun a => d02CircleExtract m (F a)) S := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (fun y : S × ℝ => F y.1 (circleMap 0 1 y.2)) :=
    hF.comp_continuous (by fun_prop : Continuous
      (fun y : S × ℝ => ((y.1 : A), circleMap 0 1 y.2)))
      (fun y => ⟨y.1.property, circleMap_mem_sphere 0 (by norm_num) y.2⟩)
  have hw : Continuous (fun y : S × ℝ => deriv (circleMap 0 1) y.2 *
      (1 / (circleMap 0 1 y.2) ^ (m + 1))) := by
    have hne (y : S × ℝ) : circleMap 0 1 y.2 ≠ 0 :=
      circleMap_ne_center (by norm_num : (1 : ℝ) ≠ 0)
    have hpow (y : S × ℝ) : circleMap 0 1 y.2 ^ (m + 1) ≠ 0 :=
      pow_ne_zero _ (hne y)
    simp_rw [deriv_circleMap]
    fun_prop
  unfold d02CircleExtract
  simp_rw [circleIntegral_def_Icc, smul_eq_mul, ← mul_assoc]
  apply continuous_const.mul
  exact continuous_parametric_integral_of_continuous (hw.mul hc) isCompact_Icc

theorem d02PolynomialCircle_continuousOn_compact_parameter {A : Type*}
    [TopologicalSpace A] [FirstCountableTopology A] [T2Space A]
    (S : Set A) (hS : IsCompact S) (p : ℝ[X]) (F : A → ℂ → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (S ×ˢ sphere (0 : ℂ) 1)) :
    ContinuousOn (fun a => d02PolynomialCircle p (F a)) S := by
  unfold d02PolynomialCircle Polynomial.sum
  apply continuousOn_finsetSum
  intro m hm
  exact continuousOn_const.mul
    (d02CircleExtract_continuousOn_compact_parameter S hS m F hF)

theorem d02CircleExtract_real_setIntegral (m : ℕ) (E : Set ℝ)
    (hE : IsCompact E) (F : ℂ → ℝ → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (sphere (0 : ℂ) 1 ×ˢ E)) :
    d02CircleExtract m (fun z => ∫ t in E, F z t) =
      ∫ t in E, d02CircleExtract m (fun z => F z t) := by
  let B : Set ℝ := Icc 0 (2 * Real.pi)
  let g : ℝ × ℝ → ℂ := fun y => deriv (circleMap 0 1) y.1 *
    (1 / (circleMap 0 1 y.1) ^ (m + 1)) * F (circleMap 0 1 y.1) y.2
  have hne (y : ℝ × ℝ) : circleMap 0 1 y.1 ≠ 0 :=
    circleMap_ne_center (by norm_num : (1 : ℝ) ≠ 0)
  have hpow (y : ℝ × ℝ) : circleMap 0 1 y.1 ^ (m + 1) ≠ 0 :=
    pow_ne_zero _ (hne y)
  have hg : ContinuousOn g (B ×ˢ E) := by
    have hc : ContinuousOn (fun y : ℝ × ℝ => F (circleMap 0 1 y.1) y.2)
        (B ×ˢ E) := hF.comp (by fun_prop : ContinuousOn
          (fun y : ℝ × ℝ => (circleMap 0 1 y.1, y.2)) (B ×ˢ E))
      (fun y hy => ⟨circleMap_mem_sphere 0 (by norm_num) y.1, hy.2⟩)
    have hw : Continuous (fun y : ℝ × ℝ => deriv (circleMap 0 1) y.1 *
        (1 / (circleMap 0 1 y.1) ^ (m + 1))) := by
      simp_rw [deriv_circleMap]
      fun_prop
    exact hw.continuousOn.mul hc
  have hi : Integrable g ((volume.restrict B).prod (volume.restrict E)) := by
    rw [Measure.prod_restrict]
    exact hg.integrableOn_compact ((isCompact_Icc : IsCompact B).prod hE)
  unfold d02CircleExtract
  simp_rw [circleIntegral_def_Icc, smul_eq_mul]
  calc
    _ = (m.factorial : ℂ) / (2 * Real.pi * I) *
        (∫ θ in B, ∫ t in E, g (θ,t)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with θ
      dsimp [g]
      rw [integral_const_mul]
      ring
    _ = (m.factorial : ℂ) / (2 * Real.pi * I) *
        (∫ t in E, ∫ θ in B, g (θ,t)) := by rw [integral_integral_swap hi]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      congr 1
      apply integral_congr_ae
      filter_upwards [] with θ
      dsimp [g]
      ring

theorem d02PolynomialCircle_real_setIntegral (p : ℝ[X]) (E : Set ℝ)
    (hE : IsCompact E) (F : ℂ → ℝ → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (sphere (0 : ℂ) 1 ×ˢ E)) :
    d02PolynomialCircle p (fun z => ∫ t in E, F z t) =
      ∫ t in E, d02PolynomialCircle p (fun z => F z t) := by
  unfold d02PolynomialCircle Polynomial.sum
  simp_rw [d02CircleExtract_real_setIntegral _ E hE F hF, ← integral_const_mul]
  rw [integral_finsetSum]
  intro m hm
  apply ContinuousOn.integrableOn_compact hE
  exact continuousOn_const.mul
    (d02CircleExtract_continuousOn_compact_parameter E hE m (fun t z => F z t)
      (hF.comp (by fun_prop : ContinuousOn
        (fun y : ℝ × ℂ => (y.2,y.1)) (E ×ˢ sphere (0 : ℂ) 1))
        (fun y hy => ⟨hy.2,hy.1⟩)))

theorem d02PolynomialCircle_two_real_setIntegral (p q : ℝ[X]) (E : Set ℝ)
    (hE : IsCompact E) (F : ℂ → ℂ → ℝ → ℂ)
    (hF : ContinuousOn (fun y : ℂ × (ℂ × ℝ) => F y.1 y.2.1 y.2.2)
      (sphere (0 : ℂ) 1 ×ˢ (sphere (0 : ℂ) 1 ×ˢ E))) :
    d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => ∫ t in E, F z w t)) =
      ∫ t in E, d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => F z w t)) := by
  have hinner (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1) :
      ContinuousOn (Function.uncurry (F z)) (sphere (0 : ℂ) 1 ×ˢ E) :=
    hF.comp (by fun_prop : ContinuousOn (fun y : ℂ × ℝ => (z,y))
      (sphere (0 : ℂ) 1 ×ˢ E)) (fun y hy => ⟨hz,hy⟩)
  calc
    _ = d02PolynomialCircle p (fun z => ∫ t in E,
        d02PolynomialCircle q (fun w => F z w t)) := by
      apply d02PolynomialCircle_congr p
      intro z hz
      exact d02PolynomialCircle_real_setIntegral q E hE (F z) (hinner z hz)
    _ = _ := by
      apply d02PolynomialCircle_real_setIntegral p E hE
      exact d02PolynomialCircle_continuousOn_compact_parameter
        (sphere (0 : ℂ) 1 ×ˢ E) (isCompact_sphere _ _ |>.prod hE) q
        (fun y w => F y.1 w y.2)
        (hF.comp (by fun_prop : ContinuousOn
          (fun y : (ℂ × ℝ) × ℂ => (y.1.1,(y.2,y.1.2)))
          ((sphere (0 : ℂ) 1 ×ˢ E) ×ˢ sphere (0 : ℂ) 1))
          (fun y hy => ⟨hy.1.1,hy.2,hy.1.2⟩))

private theorem d02_shifted_zeta_nonpole {T : ℝ} {s z : ℂ}
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

private theorem d02_profileDirichletSum_continuous {T : ℝ} (hT : 1 < T)
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

theorem d02BalancedAmplifier_continuous {T : ℝ} (hT : 1 < T)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i)) :
    Continuous (fun t => d02BalancedAmplifier T t ρ) := by
  have hp (i : Fin 4) := d02_profileDirichletSum_continuous hT (ρ i) (A i) (hρsupport i)
  unfold d02BalancedAmplifier
  have hc : Continuous criticalLinePoint := by unfold criticalLinePoint; fun_prop
  exact (((hp 0).comp hc).mul ((hp 1).comp hc)).mul
    ((hp 2).comp (continuous_const.sub hc)) |>.mul
      ((hp 3).comp (continuous_const.sub hc))

theorem d02BalancedShiftedIntegrand_continuousOn {T : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    ContinuousOn (fun y : ℂ × (ℂ × ℝ) => (Φ (y.2.2 / T) : ℂ) *
      zetaCPlus T y.2.2 y.1 * zetaCMinus T y.2.2 y.2.1 *
      d02BalancedAmplifier T y.2.2 ρ)
      (sphere (0 : ℂ) 1 ×ˢ (sphere (0 : ℂ) 1 ×ˢ Icc T (2 * T))) := by
  have hplus : ContinuousOn (fun y : ℂ × (ℂ × ℝ) => zetaCPlus T y.2.2 y.1)
      (sphere (0 : ℂ) 1 ×ˢ (sphere (0 : ℂ) 1 ×ˢ Icc T (2 * T))) := by
    intro y hy
    unfold zetaCPlus shiftedZetaGenerator
    have ht : 1 < |(criticalLinePoint y.2.2).im| := by
      rw [criticalLinePoint_im, abs_of_pos (zero_lt_one.trans (hT.trans_le hy.2.2.1))]
      exact hT.trans_le hy.2.2.1
    have hz := (differentiableAt_riemannZeta
      (d02_shifted_zeta_nonpole hL ht hy.1)).continuousAt
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
      (d02_shifted_zeta_nonpole hL ht hy.2.1)).continuousAt
    have hmap : ContinuousWithinAt (fun u : ℂ × (ℂ × ℝ) =>
        1 - criticalLinePoint u.2.2 + u.2.1 / (Real.log T : ℂ))
        (sphere (0 : ℂ) 1 ×ˢ (sphere (0 : ℂ) 1 ×ˢ Icc T (2 * T))) y := by
      unfold criticalLinePoint
      fun_prop
    exact (by fun_prop : ContinuousWithinAt
      (fun y : ℂ × (ℂ × ℝ) => Complex.exp (y.2.1 / 2)) _ y).mul
      (hz.comp_continuousWithinAt (f := fun u : ℂ × (ℂ × ℝ) =>
        1 - criticalLinePoint u.2.2 + u.2.1 / (Real.log T : ℂ)) (x := y) hmap)
  have ham := d02BalancedAmplifier_continuous hT ρ A hρsupport
  have hcut : Continuous (fun y : ℂ × (ℂ × ℝ) => (Φ (y.2.2 / T) : ℂ)) := by fun_prop
  exact ((hcut.continuousOn.mul hplus).mul hminus).mul
    ((ham.comp (by fun_prop : Continuous (fun y : ℂ × (ℂ × ℝ) => y.2.2))).continuousOn)

private theorem d02_height_cutoff_zero {T t : ℝ} (hT : 0 < T)
    (Φ : ℝ → ℝ) (hΦs : tsupport Φ ⊆ Icc 1 2) (ht : t ∉ Icc T (2 * T)) :
    Φ (t / T) = 0 := by
  by_contra hn
  have hx := hΦs (subset_tsupport Φ hn)
  apply ht
  constructor
  · simpa using (le_div_iff₀ hT).mp hx.1
  · exact (div_le_iff₀ hT).mp hx.2


theorem d02BalancedShiftedMoment_eq_window_integral {T : ℝ} (hT : 0 < T)
    (σ : Fin 2 → ℂ) (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ)
    (hΦs : tsupport Φ ⊆ Icc 1 2) :
    d02BalancedShiftedMoment T σ ρ Φ = ∫ t in Icc T (2 * T),
      (Φ (t / T) : ℂ) * zetaCPlus T t (σ 0) * zetaCMinus T t (σ 1) *
        d02BalancedAmplifier T t ρ := by
  unfold d02BalancedShiftedMoment
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Icc T (2 * T)
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht]
    rw [d02_height_cutoff_zero hT Φ hΦs ht]
    simp


theorem d02BalancedShiftedMoment_integrable_of_mem_circles {T : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T) {z w : ℂ}
    (hz : z ∈ sphere (0 : ℂ) 1) (hw : w ∈ sphere (0 : ℂ) 1)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    Integrable (fun t : ℝ => (Φ (t / T) : ℂ) * zetaCPlus T t z *
      zetaCMinus T t w * d02BalancedAmplifier T t ρ) := by
  have hc := (d02BalancedShiftedIntegrand_continuousOn hT hL ρ A hρsupport Φ hΦ).comp
    (by fun_prop : ContinuousOn (fun t : ℝ => (z,(w,t))) (Icc T (2 * T)))
    (fun t ht => ⟨hz,hw,ht⟩)
  have hci : IntegrableOn (fun t : ℝ => (Φ (t / T) : ℂ) * zetaCPlus T t z *
      zetaCMinus T t w * d02BalancedAmplifier T t ρ) (Icc T (2 * T)) volume :=
    hc.integrableOn_compact isCompact_Icc
  have hi := hci.integrable_indicator measurableSet_Icc
  apply hi.congr
  filter_upwards [] with t
  by_cases ht : t ∈ Icc T (2 * T)
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht]
    rw [d02_height_cutoff_zero (zero_lt_one.trans hT) Φ hΦs ht]
    simp

theorem d02BalancedShiftedMoment_continuousOn_two_circles {T : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ContinuousOn (fun y : ℂ × ℂ => d02BalancedShiftedMoment T ![y.1,y.2] ρ Φ)
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
  let F : S → ℝ → ℂ := fun y t => (Φ (τ t / T) : ℂ) *
    zetaCPlus T (τ t) y.val.1 * zetaCMinus T (τ t) y.val.2 *
      d02BalancedAmplifier T (τ t) ρ
  have hc : Continuous (Function.uncurry F) :=
    (d02BalancedShiftedIntegrand_continuousOn hT hL ρ A hρsupport Φ hΦ).comp_continuous
      (by dsimp [τ]; fun_prop : Continuous
        (fun y : S × ℝ => (y.1.val.1,(y.1.val.2,τ y.2))))
      (fun y => ⟨y.1.property.1, y.1.property.2, hτ y.2⟩)
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    ((isCompact_sphere _ _).prod (isCompact_sphere _ _))
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (S.domRestrict (fun y : ℂ × ℂ =>
      d02BalancedShiftedMoment T ![y.1,y.2] ρ Φ)) = fun y : S => ∫ t in E, F y t := by
    funext y
    change d02BalancedShiftedMoment T ![y.val.1,y.val.2] ρ Φ = _
    rw [d02BalancedShiftedMoment_eq_window_integral (zero_lt_one.trans hT) _ ρ Φ hΦs]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp [F]
    rw [hτeq t ht]
  rw [heq]
  exact continuous_parametric_integral_of_continuous hc isCompact_Icc

theorem d02BalancedShiftedMoment_eventually_continuousOn_two_circles
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ∀ᶠ T : ℝ in atTop, ContinuousOn
      (fun y : ℂ × ℂ => d02BalancedShiftedMoment T ![y.1,y.2] ρ Φ)
      (sphere (0 : ℂ) 1 ×ˢ sphere (0 : ℂ) 1) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with T hT hL
  exact d02BalancedShiftedMoment_continuousOn_two_circles hT hL ρ A hρsupport Φ hΦ.continuous hΦs

theorem d02BalancedPolynomialMoment_eq_two_circle {T : ℝ}
    (hT : 1 < T) (hL : 1 ≤ Real.log T) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    d02BalancedPolynomialMoment T p q ρ Φ =
      d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
        d02BalancedShiftedMoment T ![z,w] ρ Φ)) := by
  let E : Set ℝ := Icc T (2 * T)
  let F : ℂ → ℂ → ℝ → ℂ := fun z w t => (Φ (t / T) : ℂ) *
    zetaCPlus T t z * zetaCMinus T t w * d02BalancedAmplifier T t ρ
  have hzero (z w : ℂ) : (∫ t : ℝ, F z w t) = ∫ t in E, F z w t := by
    simpa only [d02BalancedShiftedMoment, F, E, Matrix.cons_val_zero,
      Matrix.cons_val_one] using d02BalancedShiftedMoment_eq_window_integral
        (zero_lt_one.trans hT) ![z,w] ρ Φ hΦs
  have hm : d02BalancedPolynomialMoment T p q ρ Φ =
      ∫ t in E, (Φ (t / T) : ℂ) * zetaCp T t p *
        zetaPolynomialDerivative T q (1 - criticalLinePoint t) * d02BalancedAmplifier T t ρ := by
    unfold d02BalancedPolynomialMoment
    change (∫ t : ℝ, (Φ (t / T) : ℂ) * zetaCp T t p *
      zetaPolynomialDerivative T q (1 - criticalLinePoint t) * d02BalancedAmplifier T t ρ) =
      ∫ t in Icc T (2 * T), (Φ (t / T) : ℂ) * zetaCp T t p *
        zetaPolynomialDerivative T q (1 - criticalLinePoint t) * d02BalancedAmplifier T t ρ
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ∈ Icc T (2 * T)
    · simp only [indicator_of_mem ht]
    · simp only [indicator_of_notMem ht]
      rw [d02_height_cutoff_zero (zero_lt_one.trans hT) Φ hΦs ht]
      simp
  have hc := d02PolynomialCircle_two_real_setIntegral p q E isCompact_Icc F
    (d02BalancedShiftedIntegrand_continuousOn hT hL ρ A hρsupport Φ hΦ)
  have hfactor (t : ℝ) : d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => F z w t)) =
      (Φ (t / T) : ℂ) * d02PolynomialCircle p (zetaCPlus T t) *
        d02PolynomialCircle q (zetaCMinus T t) * d02BalancedAmplifier T t ρ := by
    dsimp [F]
    simp_rw [d02PolynomialCircle_mul_const, d02PolynomialCircle_const_mul,
      d02PolynomialCircle_mul_const]
    rw [d02PolynomialCircle_const_mul]
  rw [hm]
  symm
  unfold d02BalancedShiftedMoment
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => ∫ t : ℝ, F z w t)) = _
  simp_rw [hzero]
  rw [hc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  change d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => F z w t)) =
    (Φ (t / T) : ℂ) * zetaCp T t p *
      zetaPolynomialDerivative T q (1 - criticalLinePoint t) * d02BalancedAmplifier T t ρ
  have ht' : 1 < |t| := by
    rw [abs_of_pos (zero_lt_one.trans (hT.trans_le ht.1))]
    exact hT.trans_le ht.1
  rw [hfactor t, ← d02_zetaCp_eq_circle hT hL ht',
    ← d02_lower_zetaPolynomial_eq_circle hT hL ht']

theorem d02BalancedPolynomialMoment_eventually_eq_two_circle (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ∀ᶠ T : ℝ in atTop, d02BalancedPolynomialMoment T p q ρ Φ =
      d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
        d02BalancedShiftedMoment T ![z,w] ρ Φ)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with T hT hL
  exact d02BalancedPolynomialMoment_eq_two_circle hT hL p q ρ A hρsupport Φ hΦ.continuous hΦs

theorem d02BalancedPolynomialMoment_tendsto_of_pointwise_shifted
    (p q : ℝ[X]) (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    (g : ℂ → ℂ → ℂ) (C : ℝ)
    (hbound : ∀ᶠ T : ℝ in atTop, ∀ z ∈ sphere (0 : ℂ) 1,
      ∀ w ∈ sphere (0 : ℂ) 1,
      ‖d02BalancedShiftedMoment T ![z,w] ρ Φ / (T * (Real.log T)^9 : ℂ)‖ ≤ C)
    (hlim : ∀ z ∈ sphere (0 : ℂ) 1, ∀ w ∈ sphere (0 : ℂ) 1,
      Tendsto (fun T : ℝ => d02BalancedShiftedMoment T ![z,w] ρ Φ /
        (T * (Real.log T)^9 : ℂ)) atTop (𝓝 (g z w))) :
    Tendsto (fun T : ℝ => d02BalancedPolynomialMoment T p q ρ Φ /
      (T * (Real.log T)^9 : ℂ)) atTop
      (𝓝 (d02PolynomialCircle p (fun z => d02PolynomialCircle q (g z)))) := by
  have hc : ∀ᶠ T : ℝ in atTop, ContinuousOn
      (fun y : ℂ × ℂ => d02BalancedShiftedMoment T ![y.1,y.2] ρ Φ /
        (T * (Real.log T)^9 : ℂ))
      (sphere (0 : ℂ) 1 ×ˢ sphere (0 : ℂ) 1) := by
    filter_upwards [d02BalancedShiftedMoment_eventually_continuousOn_two_circles
      ρ A hρsupport Φ hΦ hΦs] with T hT
    simp only [div_eq_mul_inv]
    exact hT.mul continuousOn_const
  have ht := d02PolynomialCircle_two_tendsto_of_dominated p q hc hbound hlim
  apply ht.congr'
  filter_upwards [d02BalancedPolynomialMoment_eventually_eq_two_circle
    p q ρ A hρsupport Φ hΦ hΦs] with T hT
  rw [hT]
  simp_rw [div_eq_mul_inv, d02PolynomialCircle_mul_const]

end
end SixthMoment
