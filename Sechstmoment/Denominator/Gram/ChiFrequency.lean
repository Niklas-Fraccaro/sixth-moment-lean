import Sechstmoment.Denominator.Gram.ChiFrequencyCore
import Sechstmoment.Zeta.Centering.Uniform

namespace Sechstmoment
open Complex Filter Metric Set
open scoped ComplexConjugate Topology
noncomputable section
set_option maxHeartbeats 0

theorem d06ComplexChiFrequency_analyticAt_nonreal {s : ℂ} (hs : s.im ≠ 0) :
    AnalyticAt ℂ d06ComplexChiFrequency s := by
  exact ((zetaChi_analyticAt_nonreal hs).deriv.div
    (zetaChi_analyticAt_nonreal hs) (zetaChi_ne_zero_nonreal hs)).neg

/-- Differentiating the normalized shift quotient identifies the actual frequency. -/
theorem d06CenteringFactorAt_deriv_zero (T : ℝ) {s : ℂ} (hs : s.im ≠ 0) :
    deriv (centeringFactorAt T s) 0 =
      1 - d06ComplexChiFrequency s / (Real.log T : ℂ) := by
  have hshift : HasDerivAt (fun z : ℂ => s + z / (Real.log T : ℂ))
      (1/(Real.log T : ℂ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).div_const (Real.log T : ℂ)).const_add s
  have hχ : HasDerivAt zetaChi (deriv zetaChi s) (s+0/(Real.log T : ℂ)) := by
    simpa using (zetaChi_analyticAt_nonreal hs).differentiableAt.hasDerivAt
  have hh := (((Complex.hasDerivAt_exp (0 : ℂ)).mul
    (hχ.comp 0 hshift)).div_const
      (zetaChi s)).deriv
  change deriv (centeringFactorAt T s) 0 = _ at hh
  rw [hh]
  simp only [Function.comp_def, zero_div, add_zero, Complex.exp_zero, one_mul,
    d06ComplexChiFrequency, add_div, div_self (zetaChi_ne_zero_nonreal hs)]
  ring

theorem d06ComplexHeightPoint_ofReal (T x : ℝ) :
    complexHeightPoint T (x : ℂ) = criticalLinePoint (T*x) := by
  unfold complexHeightPoint criticalLinePoint
  push_cast
  ring

/-- The actual logarithmic frequency is `log T + O(1)` on a complex height
window. This follows by differentiating the already proved shift bound. -/
theorem d06ComplexChiFrequency_uniform_height_bound :
    ∀ᶠ T : ℝ in atTop, ∀ x : ℂ,
      x.re ∈ Icc (3/4 : ℝ) (9/4) → |x.im| ≤ 1/4 →
      ‖d06ComplexChiFrequency (complexHeightPoint T x) - (Real.log T : ℂ)‖ ≤
        centeringUniformConstant 1 := by
  filter_upwards [centeringFactorAt_uniform_complex_height_bound 1,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (192*((1 : ℝ)+1^2)+8)] with T hb hL hT
  intro x hxre hxim
  have hL0 : 0 < Real.log T := by linarith
  have hs := (complexHeightPoint_shift_nonreal (R := 1) (z := 0)
    hxre.1 (by simp) hL hT).1
  let f : ℂ → ℂ := fun z => centeringFactorAt T (complexHeightPoint T x) z - 1
  have ha : AnalyticOnNhd ℂ f (closedBall 0 1) := by
    intro z hz
    have hn := (complexHeightPoint_shift_nonreal hxre.1 (by simpa using hz) hL hT).2
    exact (centeringFactorAt_analyticAt_shift T (complexHeightPoint T x) hn).sub
      analyticAt_const
  have hf : DiffContOnCl ℂ f (ball 0 1) :=
    (ha.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
  have hc := cauchy_iteratedDeriv_bound 1 (by norm_num : (0 : ℝ)<1) hf
    (fun z hz => hb x z hxre hxim (by simpa using (sphere_subset_closedBall hz)))
  simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_pow, div_one,
    one_mul, f, deriv_sub_const] at hc
  rw [d06CenteringFactorAt_deriv_zero T hs] at hc
  have he : d06ComplexChiFrequency (complexHeightPoint T x) - (Real.log T : ℂ) =
      -(Real.log T : ℂ)*(1-d06ComplexChiFrequency (complexHeightPoint T x)/
        (Real.log T : ℂ)) := by
    field_simp [Complex.ofReal_ne_zero.mpr hL0.ne']
    ring
  rw [he, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
  calc
    _ ≤ Real.log T*(centeringUniformConstant 1/Real.log T) :=
      mul_le_mul_of_nonneg_left hc hL0.le
    _ = _ := by field_simp

theorem d06ChiFrequency_uniform_dyadic_bound :
    ∀ᶠ T : ℝ in atTop, ∀ x : ℝ, x ∈ Icc (1 : ℝ) 2 →
      |d06ChiFrequency (T*x)-Real.log T| ≤ centeringUniformConstant 1 := by
  filter_upwards [d06ComplexChiFrequency_uniform_height_bound] with T hT
  intro x hx
  have h := hT (x : ℂ) (by simp only [Complex.ofReal_re]; constructor <;> linarith [hx.1,hx.2])
    (by simp)
  rw [d06ComplexHeightPoint_ofReal, d06ComplexChiFrequency_criticalLine_real,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end
end Sechstmoment
