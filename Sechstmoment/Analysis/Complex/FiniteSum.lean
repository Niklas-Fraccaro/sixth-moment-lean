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

/-- The triangle inequality transfers a uniform bound to a finite complex sum. -/
theorem complex_finset_sum_norm_le_card_mul {ι : Type*} (s : Finset ι)
    (F : ι → ℂ) {B : ℝ} (hB : ∀ i ∈ s, ‖F i‖ ≤ B) :
    ‖∑ i ∈ s, F i‖ ≤ (s.card : ℝ) * B := by
  calc
    ‖∑ i ∈ s, F i‖ ≤ ∑ i ∈ s, ‖F i‖ := norm_sum_le s F
    _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum hB
    _ = (s.card : ℝ) * B := by simp

end Sechstmoment
