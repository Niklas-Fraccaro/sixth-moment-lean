import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.UniformSpace.UniformConvergence


namespace SixthMoment.Source.NoDPHarmonic
open Real Filter Set Metric
open scoped Topology BigOperators
noncomputable section

def harmonicMass (L x : ℝ) : ℝ :=
  (harmonic ⌊Real.exp (L*x)⌋₊ : ℝ) / L

theorem harmonicMass_error {L x : ℝ} (hL : 0 < L) (hx : 0 ≤ x) :
    0 ≤ harmonicMass L x - x ∧ harmonicMass L x - x ≤ 1/L := by
  have hX : 1 ≤ Real.exp (L*x) := Real.one_le_exp_iff.mpr (mul_nonneg hL.le hx)
  have hlo := log_le_harmonic_floor (Real.exp (L*x)) (Real.exp_pos _).le
  have hhi := harmonic_floor_le_one_add_log (Real.exp (L*x)) hX
  rw [Real.log_exp] at hlo hhi
  constructor
  · have h := (le_div_iff₀ hL).mpr (show x*L ≤ (harmonic ⌊Real.exp (L*x)⌋₊ : ℝ) by nlinarith)
    exact sub_nonneg.mpr h
  · have h := div_le_div_of_nonneg_right hhi hL.le
    rw [add_div, mul_div_cancel_left₀ x hL.ne'] at h
    dsimp only [harmonicMass]
    linarith

theorem harmonicMass_abs_error {L x : ℝ} (hL : 0 < L) (hx : 0 ≤ x) :
    |harmonicMass L x - x| ≤ 1/L := by
  rw [abs_of_nonneg (harmonicMass_error hL hx).1]
  exact (harmonicMass_error hL hx).2

theorem harmonicMass_uniformly :
    TendstoUniformlyOn (fun L x => harmonicMass L x - x) (fun _ => 0)
      atTop (Ici (0 : ℝ)) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have ht : Tendsto (fun L : ℝ => 1/L) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  filter_upwards [eventually_gt_atTop (0 : ℝ), (tendsto_order.mp ht).2 ε hε]
    with L hL hεL x hx
  rw [dist_zero_left, Real.norm_eq_abs]
  exact (harmonicMass_abs_error hL hx).trans_lt hεL

theorem harmonic_eq_real_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Finset.Icc 1 N, 1/(n:ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

theorem harmonic_Ico_bound (N : ℕ) :
    (∑ n ∈ Finset.Ico 1 N, 1/(n:ℝ)) ≤ 1 + Real.log N := by
  apply (show (∑ n ∈ Finset.Ico 1 N, 1/(n:ℝ)) ≤ (harmonic N : ℝ) from ?_).trans
    (harmonic_le_one_add_log N)
  rw [harmonic_eq_real_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hn).1, (Finset.mem_Ico.mp hn).2.le⟩
  · intro n _ _
    positivity

theorem log_cell_bounds {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ Real.log (n+1:ℕ) - Real.log n ∧
      Real.log (n+1:ℕ) - Real.log n ≤ 1/(n:ℝ) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hnp : (0:ℝ) < (n+1:ℕ) := by positivity
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hn0 (by exact_mod_cast Nat.le_succ n))
  · have h := Real.log_le_sub_one_of_pos (div_pos hnp hn0)
    rw [Real.log_div hnp.ne' hn0.ne'] at h
    apply h.trans_eq
    push_cast
    field_simp
    ring

end
end SixthMoment.Source.NoDPHarmonic
