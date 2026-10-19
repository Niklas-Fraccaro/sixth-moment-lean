import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
Elementary asymptotic consequences of the rectangular exponent range.
The finite-block statements are transfer lemmas: they assume explicit uniform
block bounds, rather than the analytic estimate which would supply those bounds.
-/

namespace Sechstmoment

open Filter Asymptotics
open scoped Topology BigOperators

/-- A real power of exponent strictly below one is sublinear at infinity. -/
theorem rpow_isLittleO_id_of_lt_one {e : ℝ} (he : e < 1) :
    (fun T : ℝ => T ^ e) =o[atTop] (fun T : ℝ => T) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact fun hz => (hT.ne' hz).elim
  · have ht := tendsto_rpow_neg_atTop (sub_pos.mpr he)
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [show -(1 - e) = e - 1 by ring, Real.rpow_sub hT, Real.rpow_one]

/-- Every fixed natural power of the logarithm is smaller than a positive real power. -/
theorem log_pow_isLittleO_rpow (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (fun T : ℝ => (Real.log T) ^ n) =o[atTop] (fun T : ℝ => T ^ δ) := by
  simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (n : ℝ) hδ

/-- A fixed logarithmic loss preserves sublinearity of any power below one. -/
theorem polylog_mul_rpow_isLittleO_id (n : ℕ) {e : ℝ} (he : e < 1) :
    (fun T : ℝ => (Real.log T) ^ n * T ^ e) =o[atTop] (fun T : ℝ => T) := by
  have hp := (log_pow_isLittleO_rpow n (sub_pos.mpr he)).mul_isBigO
    (isBigO_refl (fun T : ℝ => T ^ e) atTop)
  refine hp.congr' (Eventually.of_forall fun _ => rfl) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [← Real.rpow_add hT, show 1 - e + e = 1 by ring, Real.rpow_one]

end Sechstmoment
