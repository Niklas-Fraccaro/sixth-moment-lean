import Mathlib.Analysis.SpecificLimits.Basic
import Sechstmoment.Arithmetic.Factor.Convergence


namespace Sechstmoment
open Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1000000

def f01SixthMomentScale (T : ℝ) : ℝ :=
  (arithmeticFactor/(Nat.factorial 9 : ℝ))*T*(Real.log T)^9

theorem f01SixthMomentScale_pos {T : ℝ} (hT : 1 < T) :
    0 < f01SixthMomentScale T := by
  have ha := arithmeticFactor_wellDefined.2
  have hL := Real.log_pos hT
  unfold f01SixthMomentScale
  positivity

theorem f01LogRatio_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => Real.log (T/c)/Real.log T) atTop (𝓝 1) := by
  have h : Tendsto (fun T : ℝ => 1-Real.log c/Real.log T) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (Real.tendsto_log_atTop.const_div_atTop (Real.log c))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  rw [Real.log_div (zero_lt_one.trans hT).ne' hc.ne']
  field_simp [(Real.log_pos hT).ne']

theorem f01ScaleRatio_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => f01SixthMomentScale (T/c)/f01SixthMomentScale T)
      atTop (𝓝 (1/c)) := by
  have h := ((f01LogRatio_tendsto hc).pow 9).const_mul (1/c)
  simp only [one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have ha := arithmeticFactor_wellDefined.2
  simp only [f01SixthMomentScale, div_pow]
  field_simp [ha.ne', hc.ne', (zero_lt_one.trans hT).ne', (Real.log_pos hT).ne']

theorem f01DyadicMass (J : ℕ) :
    (∑ j ∈ Finset.range J, 1/(2 : ℝ)^(j+1)) = 1-(1/2 : ℝ)^J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, pow_succ, pow_succ, div_pow]
    ring

end
end Sechstmoment
