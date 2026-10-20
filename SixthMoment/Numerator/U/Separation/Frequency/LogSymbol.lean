import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic
import SixthMoment.Analysis.Complex.RealDerivatives
import SixthMoment.Numerator.U.Separation.Frequency.LogFrequency

namespace SixthMoment
open Complex Real MeasureTheory Set Metric
open scoped ContDiff Topology
noncomputable section
set_option maxHeartbeats 1000000

def a03ComplexLogGapSymbol (T r s : ℝ) (w : ℂ) : ℂ :=
  (T : ℂ) * Complex.log (1 + ((s * r : ℝ) : ℂ) * Complex.exp w)

def a03RealLogGapSymbol (T r s : ℝ) (x : ℝ) : ℝ :=
  T * Real.log (1 + s * r * Real.exp x)

private theorem exponential_disk_norm {x : ℝ} (hx : Real.exp x ≤ 20)
    {z : ℂ} (hz : z ∈ closedBall (x : ℂ) (1 / 10)) :
    ‖Complex.exp z‖ ≤ 40 := by
  have hδ : Real.exp (1 / 10 : ℝ) ≤ 2 := by
    exact (Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1 / 10)
      (by norm_num : (1 / 10 : ℝ) < 1)).trans (by norm_num)
  have hdist : ‖z - (x : ℂ)‖ ≤ 1 / 10 := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hre := (Complex.re_le_norm (z - (x : ℂ))).trans hdist
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  rw [Complex.norm_exp]
  calc
    Real.exp z.re ≤ Real.exp (x + 1 / 10) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp x * Real.exp (1 / 10) := Real.exp_add _ _
    _ ≤ 20 * 2 := mul_le_mul hx hδ (Real.exp_pos _).le (by norm_num)
    _ = 40 := by norm_num

private theorem gap_perturbation_disk_norm {r s x : ℝ}
    (hr : 0 ≤ r) (hs : |s| ≤ 1) (hx : Real.exp x ≤ 20)
    {z : ℂ} (hz : z ∈ closedBall (x : ℂ) (1 / 10)) :
    ‖((s * r : ℝ) : ℂ) * Complex.exp z‖ ≤ 40 * r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hr]
  calc
    _ ≤ (1 * r) * 40 := mul_le_mul
      (mul_le_mul_of_nonneg_right hs hr) (exponential_disk_norm hx hz)
      (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem gap_perturbation_disk_half {r s x : ℝ}
    (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 100) (hs : |s| ≤ 1) (hx : Real.exp x ≤ 20)
    {z : ℂ} (hz : z ∈ closedBall (x : ℂ) (1 / 10)) :
    ‖((s * r : ℝ) : ℂ) * Complex.exp z‖ ≤ 1 / 2 := by
  exact (gap_perturbation_disk_norm hr hs hx hz).trans (by linarith)

theorem a03_log_gap_symbol_diffContOnCl {T r s x : ℝ}
    (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 100) (hs : |s| ≤ 1) (hx : Real.exp x ≤ 20) :
    DiffContOnCl ℂ (a03ComplexLogGapSymbol T r s) (ball (x : ℂ) (1 / 10)) := by
  have hd : DifferentiableOn ℂ (a03ComplexLogGapSymbol T r s)
      (closedBall (x : ℂ) (1 / 10)) := by
    intro z hz
    have hsl : 1 + ((s * r : ℝ) : ℂ) * Complex.exp z ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_of_norm_lt_one
        ((gap_perturbation_disk_half hr hr₁ hs hx hz).trans_lt (by norm_num))
    have hi : DifferentiableAt ℂ (fun w : ℂ => 1 + ((s * r : ℝ) : ℂ) * Complex.exp w) z := by
      fun_prop
    exact (((Complex.differentiableAt_log hsl).comp z hi).const_mul (T : ℂ)).differentiableWithinAt
  apply DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn

theorem a03_log_gap_symbol_disk_norm {T r s x : ℝ}
    (hT : 0 ≤ T) (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 100) (hs : |s| ≤ 1)
    (hx : Real.exp x ≤ 20) :
    ∀ z ∈ closedBall (x : ℂ) (1 / 10),
      ‖a03ComplexLogGapSymbol T r s z‖ ≤ 100 * T * r := by
  intro z hz
  unfold a03ComplexLogGapSymbol
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT]
  calc
    _ ≤ T * ((3 / 2) * ‖((s * r : ℝ) : ℂ) * Complex.exp z‖) :=
      mul_le_mul_of_nonneg_left
        (Complex.norm_log_one_add_half_le_self (gap_perturbation_disk_half hr hr₁ hs hx hz)) hT
    _ ≤ T * ((3 / 2) * (40 * r)) := by
      gcongr
      exact gap_perturbation_disk_norm hr hs hx hz
    _ ≤ 100 * T * r := by nlinarith [mul_nonneg hT hr]

theorem a03_log_gap_symbol_complex_derivative_bound {T r s x : ℝ}
    (hT : 0 ≤ T) (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 100) (hs : |s| ≤ 1)
    (hx : Real.exp x ≤ 20) (n : ℕ) :
    ‖iteratedDeriv n (a03ComplexLogGapSymbol T r s) (x : ℂ)‖ ≤
      (Nat.factorial n : ℝ) * 10 ^ n * 100 * T * r := by
  have hb := cauchy_iteratedDeriv_bound n (by norm_num : (0 : ℝ) < 1 / 10)
    (a03_log_gap_symbol_diffContOnCl hr hr₁ hs hx)
    (fun z hz => a03_log_gap_symbol_disk_norm hT hr hr₁ hs hx z (sphere_subset_closedBall hz))
  convert hb using 1
  rw [div_eq_mul_inv, ← inv_pow, one_div, inv_inv]
  ring

theorem a03_log_gap_symbol_real_restriction_derivative_bound {T r s x : ℝ}
    (hT : 0 ≤ T) (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 100) (hs : |s| ≤ 1)
    (hx : Real.exp x ≤ 20) (n : ℕ) :
    ‖iteratedDeriv n (fun y : ℝ => a03ComplexLogGapSymbol T r s (y : ℂ)) x‖ ≤
      (Nat.factorial n : ℝ) * 10 ^ n * 100 * T * r := by
  have hb := cauchy_real_iteratedDeriv_bound n (by norm_num : (0 : ℝ) < 1 / 10)
    (a03_log_gap_symbol_diffContOnCl hr hr₁ hs hx)
    (fun z hz => a03_log_gap_symbol_disk_norm hT hr hr₁ hs hx z (sphere_subset_closedBall hz))
  convert hb using 1
  rw [div_eq_mul_inv, ← inv_pow, one_div, inv_inv]
  ring

theorem a03_log_gap_symbol_real_part (T r s y : ℝ) :
    (a03ComplexLogGapSymbol T r s (y : ℂ)).re = a03RealLogGapSymbol T r s y := by
  unfold a03ComplexLogGapSymbol a03RealLogGapSymbol
  rw [← Complex.ofReal_exp]
  have he : (1 : ℂ) + ((s * r : ℝ) : ℂ) * (Real.exp y : ℂ) =
      ((1 + s * r * Real.exp y : ℝ) : ℂ) := by push_cast; rfl
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.log_ofReal_re]

theorem a03_log_gap_symbol_exact_real_restriction (T r s y : ℝ)
    (hy : 0 ≤ 1 + s * r * Real.exp y) :
    a03ComplexLogGapSymbol T r s (y : ℂ) = (a03RealLogGapSymbol T r s y : ℂ) := by
  unfold a03ComplexLogGapSymbol a03RealLogGapSymbol
  rw [← Complex.ofReal_exp]
  have he : (1 : ℂ) + ((s * r : ℝ) : ℂ) * (Real.exp y : ℂ) =
      ((1 + s * r * Real.exp y : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_log hy, Complex.ofReal_mul]

theorem a03_log_gap_symbol_real_argument_positive {r s x : ℝ}
    (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 100) (hs : |s| ≤ 1) (hx : Real.exp x ≤ 20) :
    0 < 1 + s * r * Real.exp x := by
  have hb : |s * r * Real.exp x| ≤ 1 / 2 := by
    have h := gap_perturbation_disk_half hr hr₁ hs hx
      (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1 / 10))
    rw [← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_eq_abs] at h
    exact h
  have hl := (neg_abs_le (s * r * Real.exp x)).trans'
    (neg_le_neg hb)
  linarith

theorem a03_log_gap_symbol_real_contDiffAt {T r s x : ℝ}
    (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 100) (hs : |s| ≤ 1) (hx : Real.exp x ≤ 20) :
    ContDiffAt ℝ ∞ (a03RealLogGapSymbol T r s) x := by
  have ha : AnalyticAt ℂ (a03ComplexLogGapSymbol T r s) (x : ℂ) :=
    (a03_log_gap_symbol_diffContOnCl hr hr₁ hs hx).differentiableOn.analyticAt
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 10)))
  have hc : ContDiffAt ℝ ∞ (fun y : ℝ => a03ComplexLogGapSymbol T r s (y : ℂ)) x :=
    (ha.contDiffAt.restrict_scalars ℝ).comp x Complex.ofRealCLM.contDiff.contDiffAt
  have he : (Complex.reCLM : ℂ → ℝ) ∘ (fun y : ℝ => a03ComplexLogGapSymbol T r s (y : ℂ)) =
      a03RealLogGapSymbol T r s := by
    funext y
    exact a03_log_gap_symbol_real_part T r s y
  rw [← he]
  exact Complex.reCLM.contDiff.contDiffAt.comp x hc

theorem a03_log_gap_symbol_real_derivative_bound {T r s x : ℝ}
    (hT : 0 ≤ T) (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 100) (hs : |s| ≤ 1)
    (hx : Real.exp x ≤ 20) (n : ℕ) :
    ‖iteratedDeriv n (a03RealLogGapSymbol T r s) x‖ ≤
      (Nat.factorial n : ℝ) * 10 ^ n * 100 * T * r := by
  have ha : AnalyticAt ℂ (a03ComplexLogGapSymbol T r s) (x : ℂ) :=
    (a03_log_gap_symbol_diffContOnCl hr hr₁ hs hx).differentiableOn.analyticAt
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 10)))
  have hc : ContDiffAt ℝ ∞ (fun y : ℝ => a03ComplexLogGapSymbol T r s (y : ℂ)) x :=
    (ha.contDiffAt.restrict_scalars ℝ).comp x Complex.ofRealCLM.contDiff.contDiffAt
  have he : (Complex.reCLM : ℂ → ℝ) ∘ (fun y : ℝ => a03ComplexLogGapSymbol T r s (y : ℂ)) =
      a03RealLogGapSymbol T r s := by
    funext y
    exact a03_log_gap_symbol_real_part T r s y
  have hn := Complex.reCLM.norm_iteratedFDeriv_comp_left hc (n := n) (by simp)
  rw [he, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hn
  have hnorm : ‖Complex.reCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound Complex.reCLM (by norm_num)
    intro z
    simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm z
  exact (hn.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))).trans
    (by simpa only [one_mul] using a03_log_gap_symbol_real_restriction_derivative_bound hT hr hr₁ hs hx n)

theorem a03_log_cutoff_box_scalar_range {yh yb yn₁ yn₂ : ℝ}
    (hh : yh ∈ Icc (-1 / 10 : ℝ) (11 / 10))
    (hb : yb ∈ Icc (-1 / 10 : ℝ) (11 / 10))
    (hn₁ : yn₁ ∈ Icc (-1 / 10 : ℝ) (11 / 10))
    (hn₂ : yn₂ ∈ Icc (-1 / 10 : ℝ) (11 / 10)) :
    yh - yb - yn₁ - yn₂ ∈ Icc (-4 : ℝ) 2 := by
  constructor <;> linarith [hh.1, hh.2, hb.1, hb.2, hn₁.1, hn₁.2, hn₂.1, hn₂.2]

theorem a03_log_box_exponential_range {x : ℝ} (hx : x ∈ Icc (-4 : ℝ) 2) :
    1 / 100 ≤ Real.exp x ∧ Real.exp x ≤ 20 := by
  have h₁ : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have h₄ : Real.exp 4 ≤ 81 := by
    calc
      Real.exp 4 = Real.exp 1 ^ 4 := by simp [← Real.exp_nat_mul]
      _ ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le h₁ 4
      _ = 81 := by norm_num
  have h₂ : Real.exp 2 ≤ 9 := by
    calc
      Real.exp 2 = Real.exp 1 ^ 2 := by simp [← Real.exp_nat_mul]
      _ ≤ 3 ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le h₁ 2
      _ = 9 := by norm_num
  have h₄low : (1 / 100 : ℝ) ≤ Real.exp (-4) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (le_div_iff₀ (Real.exp_pos 4)).mpr
    linarith
  exact ⟨h₄low.trans (Real.exp_le_exp.mpr hx.1),
    (Real.exp_le_exp.mpr hx.2).trans (h₂.trans (by norm_num))⟩

theorem a03_log_gap_symbol_scaled_frequency_lower {T r s x : ℝ}
    (hT : 0 ≤ T) (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 100) (hs : |s| = 1)
    (hxlo : 1 / 100 ≤ Real.exp x) (hxhi : Real.exp x ≤ 20) :
    T * r / 200 ≤ |a03RealLogGapSymbol T r s x| := by
  have habs : |s * r * Real.exp x| = r * Real.exp x := by
    rw [abs_mul, abs_mul, hs, abs_of_nonneg hr, abs_of_pos (Real.exp_pos _), one_mul]
  have hsmall : |s * r * Real.exp x| ≤ 1 / 2 := by
    rw [habs]
    have hm := mul_le_mul_of_nonneg_left hxhi hr
    nlinarith
  have hl := (phase_log_one_add_comparable hsmall).1
  rw [habs] at hl
  have hrlo := mul_le_mul_of_nonneg_left hxlo hr
  have hlo : r / 200 ≤ |Real.log (1 + s * r * Real.exp x)| := by linarith
  have h := mul_le_mul_of_nonneg_left hlo hT
  rw [a03RealLogGapSymbol, abs_mul, abs_of_nonneg hT]
  nlinarith

theorem a03_log_gap_symbol_one_add_frequency_lower {T r s x : ℝ}
    (hT : 0 ≤ T) (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 100) (hs : |s| = 1)
    (hxlo : 1 / 100 ≤ Real.exp x) (hxhi : Real.exp x ≤ 20) :
    1 + T * r ≤ 200 * (1 + |a03RealLogGapSymbol T r s x|) := by
  have h := a03_log_gap_symbol_scaled_frequency_lower hT hr hr₁ hs hxlo hxhi
  nlinarith

end
end SixthMoment
