import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import SixthMoment.Analysis.Complex.CauchyBounds


namespace SixthMoment

open Filter Metric Asymptotics

noncomputable section

def elementaryCenteredPhase (T x : ℝ) (z : ℂ) : ℂ :=
  Complex.exp z * ((T * x / (2 * Real.pi) : ℝ) : ℂ) ^
    (-z / (Real.log T : ℂ))

def elementaryPhaseLogBound : ℝ := Real.log 2 + |Real.log (2 * Real.pi)|

theorem elementaryPhaseLogBound_pos : 0 < elementaryPhaseLogBound := by
  unfold elementaryPhaseLogBound
  exact add_pos_of_pos_of_nonneg (Real.log_pos (by norm_num)) (abs_nonneg _)

theorem elementaryPhase_log_bound {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    |Real.log (x / (2 * Real.pi))| ≤ elementaryPhaseLogBound := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  have hpi0 : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [Real.log_div hx0.ne' hpi0.ne']
  calc
    |Real.log x - Real.log (2 * Real.pi)| ≤
        |Real.log x| + |Real.log (2 * Real.pi)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (Real.log x) 0 (Real.log (2 * Real.pi)))
    _ ≤ Real.log 2 + |Real.log (2 * Real.pi)| := by
      rw [abs_of_nonneg (Real.log_nonneg hx.1)]
      linarith [Real.log_le_log hx0 hx.2]
    _ = elementaryPhaseLogBound := rfl

theorem elementaryCenteredPhase_eq_exp {T x : ℝ} (z : ℂ)
    (hT : 0 < T) (hx : 0 < x) (hlog : Real.log T ≠ 0) :
    elementaryCenteredPhase T x z =
      Complex.exp (-z * (Real.log (x / (2 * Real.pi)) : ℂ) / (Real.log T : ℂ)) := by
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hbase : 0 < T * x / (2 * Real.pi) := div_pos (mul_pos hT hx) hpi
  have hratio : 0 < x / (2 * Real.pi) := div_pos hx hpi
  have heq : T * x / (2 * Real.pi) = T * (x / (2 * Real.pi)) := by ring
  have hlogs : Real.log (T * x / (2 * Real.pi)) =
      Real.log T + Real.log (x / (2 * Real.pi)) := by
    rw [heq, Real.log_mul hT.ne' hratio.ne']
  rw [elementaryCenteredPhase,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hbase.ne'),
    ← Complex.ofReal_log hbase.le, hlogs, Complex.ofReal_add, ← Complex.exp_add]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr hlog]
  ring

theorem elementaryCenteredPhase_differentiable {T x : ℝ}
    (hT : 0 < T) (hx : 0 < x) (hlog : Real.log T ≠ 0) :
    Differentiable ℂ (elementaryCenteredPhase T x) := by
  have heq : elementaryCenteredPhase T x = fun z =>
      Complex.exp (-z * (Real.log (x / (2 * Real.pi)) : ℂ) / (Real.log T : ℂ)) :=
    funext (fun z => elementaryCenteredPhase_eq_exp z hT hx hlog)
  rw [heq]
  fun_prop

theorem elementaryCenteredPhase_error_bound {T x R : ℝ} {z : ℂ}
    (hT : 0 < T) (hx : x ∈ Set.Icc (1 : ℝ) 2) (hz : ‖z‖ ≤ R)
    (hlog : max 1 (R * elementaryPhaseLogBound) ≤ Real.log T) :
    ‖elementaryCenteredPhase T x z - 1‖ ≤
      (2 * R * elementaryPhaseLogBound) / Real.log T := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have hL : 0 < Real.log T :=
    zero_lt_one.trans_le ((le_max_left 1 (R * elementaryPhaseLogBound)).trans hlog)
  rw [elementaryCenteredPhase_eq_exp z hT (zero_lt_one.trans_le hx.1) hL.ne']
  have hexponent :
      ‖-z * (Real.log (x / (2 * Real.pi)) : ℂ) / (Real.log T : ℂ)‖ ≤
        R * elementaryPhaseLogBound / Real.log T := by
    rw [norm_div, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL]
    apply div_le_div_of_nonneg_right _ hL.le
    exact mul_le_mul hz (elementaryPhase_log_bound hx) (abs_nonneg _) hR
  have hone : R * elementaryPhaseLogBound / Real.log T ≤ 1 :=
    (div_le_one hL).mpr ((le_max_right 1 (R * elementaryPhaseLogBound)).trans hlog)
  calc
    _ ≤ 2 * ‖-z * (Real.log (x / (2 * Real.pi)) : ℂ) / (Real.log T : ℂ)‖ :=
      Complex.norm_exp_sub_one_le (hexponent.trans hone)
    _ ≤ 2 * (R * elementaryPhaseLogBound / Real.log T) :=
      mul_le_mul_of_nonneg_left hexponent (by norm_num)
    _ = _ := by ring

theorem elementaryCenteredPhase_uniform_error_bound (R : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ x ∈ Set.Icc (1 : ℝ) 2, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖elementaryCenteredPhase T x z - 1‖ ≤
        (2 * R * elementaryPhaseLogBound) / Real.log T := by
  have hlog := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (R * elementaryPhaseLogBound)))
  filter_upwards [hlog, eventually_gt_atTop (0 : ℝ)] with T hLT hT
  intro x hx z hz
  exact elementaryCenteredPhase_error_bound hT hx hz hLT

theorem elementaryCenteredPhase_error_invLog_isBigO (R : ℝ)
    (x : ℝ → ℝ) (z : ℝ → ℂ)
    (hx : ∀ᶠ T in atTop, x T ∈ Set.Icc (1 : ℝ) 2)
    (hz : ∀ᶠ T in atTop, ‖z T‖ ≤ R) :
    (fun T => elementaryCenteredPhase T (x T) (z T) - 1) =O[atTop]
      (fun T => (Real.log T)⁻¹) := by
  apply IsBigO.of_bound (2 * R * elementaryPhaseLogBound)
  filter_upwards [elementaryCenteredPhase_uniform_error_bound R, hx, hz,
    eventually_gt_atTop (1 : ℝ)] with T hT hTx hTz hT1
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.log_pos hT1).le)]
  simpa only [div_eq_mul_inv] using hT (x T) hTx (z T) hTz

theorem elementaryCenteredPhase_remainder_iteratedDeriv_invLog_isBigO (n : ℕ)
    {R : ℝ} (hR : 0 < R) (x : ℝ → Set.Icc (1 : ℝ) 2) :
    (fun T => iteratedDeriv n (fun z => elementaryCenteredPhase T (x T) z - 1) 0)
      =O[atTop] (fun T => (Real.log T)⁻¹) := by
  apply uniform_cauchy_iteratedDeriv_invLog_isBigO n
    (fun T (b : Set.Icc (1 : ℝ) 2) z => elementaryCenteredPhase T b z - 1)
    (fun _ _ => 0) x hR
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    intro b
    exact ((elementaryCenteredPhase_differentiable (zero_lt_one.trans hT)
      (zero_lt_one.trans_le b.property.1) (Real.log_pos hT).ne').sub
        (differentiable_const (1 : ℂ))).diffContOnCl
  · filter_upwards [elementaryCenteredPhase_uniform_error_bound R] with T hT
    intro b z hz
    apply hT b b.property z
    have hz' : ‖z - (0 : ℂ)‖ = R := mem_sphere_iff_norm.mp hz
    simpa only [sub_zero] using hz'.le

end

end SixthMoment
