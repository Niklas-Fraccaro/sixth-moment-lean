import SixthMoment.Denominator.Gram.ChiFrequency

namespace SixthMoment
open Complex Filter Metric Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

def d06ChiReciprocalSymbol (T ℓ : ℝ) (x : ℂ) : ℂ :=
  (I*((ℓ : ℂ)+d06ComplexChiFrequency (complexHeightPoint T x)))⁻¹

theorem d06ChiReciprocalSymbol_ofReal (T ℓ x : ℝ) :
    d06ChiReciprocalSymbol T ℓ (x : ℂ) =
      (I*((ℓ+d06ChiFrequency (T*x) : ℝ) : ℂ))⁻¹ := by
  rw [d06ChiReciprocalSymbol, d06ComplexHeightPoint_ofReal,
    d06ComplexChiFrequency_criticalLine_real, Complex.ofReal_add]

theorem d06ChiFrequencyShift_uniform_nonzero {S : ℝ} (hS : S < 1) :
    ∀ᶠ T : ℝ in atTop, ∀ ℓ : ℝ, -S*Real.log T ≤ ℓ →
      ∀ x : ℂ, x.re ∈ Icc (3/4 : ℝ) (9/4) → |x.im| ≤ 1/4 →
      1 ≤ ‖(ℓ : ℂ)+d06ComplexChiFrequency (complexHeightPoint T x)‖ := by
  filter_upwards [d06ComplexChiFrequency_uniform_height_bound,
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop ((centeringUniformConstant 1+1)/(1-S)))] with T hb hL
  intro ℓ hℓ x hxre hxim
  have hscale : centeringUniformConstant 1+1 ≤ (1-S)*Real.log T := by
    simpa only [mul_comm] using (div_le_iff₀ (sub_pos.mpr hS)).mp hL
  have hbase : centeringUniformConstant 1+1 ≤ ℓ+Real.log T := by linarith
  have hbound := hb x hxre hxim
  have hn := norm_sub_norm_le ((ℓ+Real.log T : ℝ) : ℂ)
    ((ℓ : ℂ)+d06ComplexChiFrequency (complexHeightPoint T x))
  have he : ((ℓ+Real.log T : ℝ) : ℂ)-
      ((ℓ : ℂ)+d06ComplexChiFrequency (complexHeightPoint T x)) =
      - (d06ComplexChiFrequency (complexHeightPoint T x)-(Real.log T : ℂ)) := by
    push_cast
    ring
  rw [he, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hn
  have hab : ℓ+Real.log T ≤ |ℓ+Real.log T| := le_abs_self _
  linarith

theorem d06ChiReciprocalSymbol_uniform_height_bound {S : ℝ} (hS : S < 1) :
    ∀ᶠ T : ℝ in atTop, ∀ ℓ : ℝ, -S*Real.log T ≤ ℓ →
      ∀ x : ℂ, x.re ∈ Icc (3/4 : ℝ) (9/4) → |x.im| ≤ 1/4 →
      ‖d06ChiReciprocalSymbol T ℓ x‖ ≤ 1 := by
  filter_upwards [d06ChiFrequencyShift_uniform_nonzero hS] with T hT
  intro ℓ hℓ x hxre hxim
  have hn := hT ℓ hℓ x hxre hxim
  simp only [d06ChiReciprocalSymbol, norm_inv, norm_mul, norm_I, one_mul]
  exact inv_le_one_of_one_le₀ hn

theorem d06QuarterDisk_height_window {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2)
    {y : ℂ} (hy : y ∈ closedBall (x : ℂ) (1/4 : ℝ)) :
    y.re ∈ Icc (3/4 : ℝ) (9/4) ∧ |y.im| ≤ 1/4 := by
  have hn : ‖y-(x : ℂ)‖ ≤ 1/4 := by simpa only [mem_closedBall, dist_eq_norm] using hy
  have hre := (Complex.abs_re_le_norm (y-(x : ℂ))).trans hn
  have him := (Complex.abs_im_le_norm (y-(x : ℂ))).trans hn
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
  exact ⟨⟨by linarith [(abs_le.mp hre).1,hx.1],
    by linarith [(abs_le.mp hre).2,hx.2]⟩,him⟩

theorem d06ChiReciprocalSymbol_analyticAt {T ℓ : ℝ} {x : ℂ}
    (hs : (complexHeightPoint T x).im ≠ 0)
    (hn : (ℓ : ℂ)+d06ComplexChiFrequency (complexHeightPoint T x) ≠ 0) :
    AnalyticAt ℂ (d06ChiReciprocalSymbol T ℓ) x := by
  have hh : AnalyticAt ℂ (complexHeightPoint T) x := by
    unfold complexHeightPoint
    fun_prop
  change AnalyticAt ℂ (fun y => (I*((ℓ : ℂ)+
    d06ComplexChiFrequency (complexHeightPoint T y)))⁻¹) x
  exact (analyticAt_const.mul (analyticAt_const.add
    ((d06ComplexChiFrequency_analyticAt_nonreal hs).comp hh))).inv
      (mul_ne_zero I_ne_zero hn)

theorem d06ChiReciprocalSymbol_uniform_all_real_derivative_bounds
    {S : ℝ} (hS : S < 1) :
    ∀ᶠ T : ℝ in atTop, ∀ ℓ : ℝ, -S*Real.log T ≤ ℓ →
      ∀ n : ℕ, ∀ x : ℝ, x ∈ Icc (1 : ℝ) 2 →
      ‖iteratedDeriv n (fun y : ℝ =>
        (I*((ℓ+d06ChiFrequency (T*y) : ℝ) : ℂ))⁻¹) x‖ ≤
        (Nat.factorial n : ℝ)/(1/4 : ℝ)^n := by
  filter_upwards [d06ChiFrequencyShift_uniform_nonzero hS,
    d06ChiReciprocalSymbol_uniform_height_bound hS,
    eventually_gt_atTop (0 : ℝ)] with T hn hb hT
  intro ℓ hℓ n x hx
  have ha : AnalyticOnNhd ℂ (d06ChiReciprocalSymbol T ℓ)
      (closedBall (x : ℂ) (1/4 : ℝ)) := by
    intro y hy
    have hw := d06QuarterDisk_height_window hx hy
    have hs : (complexHeightPoint T y).im ≠ 0 := by
      rw [complexHeightPoint_im]
      exact mul_ne_zero hT.ne' (ne_of_gt (by linarith [hw.1.1]))
    have hz : (ℓ : ℂ)+d06ComplexChiFrequency (complexHeightPoint T y) ≠ 0 := by
      intro hz
      have hh := hn ℓ hℓ y hw.1 hw.2
      rw [hz,norm_zero] at hh
      linarith
    exact d06ChiReciprocalSymbol_analyticAt hs hz
  have hf : DiffContOnCl ℂ (d06ChiReciprocalSymbol T ℓ)
      (ball (x : ℂ) (1/4 : ℝ)) :=
    (ha.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
  have hm (y : ℂ) (hy : y ∈ sphere (x : ℂ) (1/4 : ℝ)) :
      ‖d06ChiReciprocalSymbol T ℓ y‖ ≤ 1 := by
    have hw := d06QuarterDisk_height_window hx (sphere_subset_closedBall hy)
    exact hb ℓ hℓ y hw.1 hw.2
  have he : (fun y : ℝ => d06ChiReciprocalSymbol T ℓ (y : ℂ)) =
      (fun y : ℝ => (I*((ℓ+d06ChiFrequency (T*y) : ℝ) : ℂ))⁻¹) :=
    funext (d06ChiReciprocalSymbol_ofReal T ℓ)
  rw [← he]
  simpa only [mul_one] using cauchy_real_iteratedDeriv_bound n (by norm_num) hf hm

theorem d06ChiReciprocalSymbol_uniform_real_derivative_bound (n : ℕ)
    {S : ℝ} (hS : S < 1) :
    ∀ᶠ T : ℝ in atTop, ∀ ℓ : ℝ, -S*Real.log T ≤ ℓ →
      ∀ x : ℝ, x ∈ Icc (1 : ℝ) 2 →
      ‖iteratedDeriv n (fun y : ℝ =>
        (I*((ℓ+d06ChiFrequency (T*y) : ℝ) : ℂ))⁻¹) x‖ ≤
        (Nat.factorial n : ℝ)/(1/4 : ℝ)^n :=
  (d06ChiReciprocalSymbol_uniform_all_real_derivative_bounds hS).mono
    (fun _ h ℓ hℓ => h ℓ hℓ n)

theorem d06ChiReciprocalSymbol_uniform_real_contDiffAt {S : ℝ} (hS : S < 1) :
    ∀ᶠ T : ℝ in atTop, ∀ ℓ : ℝ, -S*Real.log T ≤ ℓ →
      ∀ x : ℝ, x ∈ Icc (1 : ℝ) 2 →
        ContDiffAt ℝ ∞ (fun y : ℝ =>
          (I*((ℓ+d06ChiFrequency (T*y) : ℝ) : ℂ))⁻¹) x := by
  filter_upwards [d06ChiFrequencyShift_uniform_nonzero hS,
    eventually_gt_atTop (0 : ℝ)] with T hn hT
  intro ℓ hℓ x hx
  have hxre : (x : ℂ).re ∈ Icc (3/4 : ℝ) (9/4) := by
    simp only [Complex.ofReal_re]
    constructor <;> linarith [hx.1,hx.2]
  have hs : (complexHeightPoint T (x : ℂ)).im ≠ 0 := by
    rw [complexHeightPoint_im,Complex.ofReal_re]
    exact mul_ne_zero hT.ne' (ne_of_gt (by linarith [hx.1]))
  have hz : (ℓ : ℂ)+d06ComplexChiFrequency (complexHeightPoint T (x : ℂ)) ≠ 0 := by
    intro hz
    have hh := hn ℓ hℓ (x : ℂ) hxre (by simp)
    rw [hz,norm_zero] at hh
    linarith
  have ha := d06ChiReciprocalSymbol_analyticAt hs hz
  have he : (fun y : ℝ => d06ChiReciprocalSymbol T ℓ (y : ℂ)) =
      (fun y : ℝ => (I*((ℓ+d06ChiFrequency (T*y) : ℝ) : ℂ))⁻¹) :=
    funext (d06ChiReciprocalSymbol_ofReal T ℓ)
  rw [← he]
  exact (ha.restrictScalars (𝕜 := ℝ)).contDiffAt.comp x
    Complex.ofRealCLM.contDiff.contDiffAt

end
end SixthMoment
