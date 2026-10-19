import Sechstmoment.Certificate.Kernels.Balanced.Knots
import Sechstmoment.Certificate.Kernels.Balanced.Nodes

namespace Sechstmoment

noncomputable def realEndpoint (k : Nat) : ℝ := (k : ℝ)/(Finite.base : ℝ)

theorem realEndpoint_nonneg (k : Nat) : 0 ≤ realEndpoint k := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem realEndpoint_mono {j k : Nat} (h : j ≤ k) : realEndpoint j ≤ realEndpoint k := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast h
  · exact Nat.cast_nonneg _

theorem realEndpoint_add (j k : Nat) : realEndpoint (j+k) = realEndpoint j+realEndpoint k := by
  simp [realEndpoint, Nat.cast_add, add_div]

theorem realEndpoint_min (j k : Nat) : realEndpoint (min j k) = min (realEndpoint j) (realEndpoint k) := by
  simp only [realEndpoint, Nat.cast_min]
  exact (min_div_div_right (by norm_num [Finite.base] : (0 : ℝ) ≤ Finite.base)
    (j : ℝ) (k : ℝ)).symm

theorem realEndpoint_scale (k : Nat) : realEndpoint k = 24*k/(Finite.scale : ℝ) := by
  norm_num [realEndpoint, Finite.scale, Finite.base]
  ring

theorem realEndpoint_zero : realEndpoint 0 = 0 := by simp [realEndpoint]

theorem normalized_knots_avoid {A B C D l u : Nat}
    (hp : (l,u) ∈ (integerD0Knots A B C D).zip (integerD0Knots A B C D).tail) :
    AvoidsDenominatorKnots (realEndpoint A) (realEndpoint B) (realEndpoint C) (realEndpoint D)
      (realEndpoint l) (realEndpoint u) := by
  have h (k : Nat) (hk : k ∈ [A,B,C,D,A+C,A+D,B+C,B+D]) :
      realEndpoint k ≤ realEndpoint l ∨ realEndpoint u ≤ realEndpoint k :=
    (integerD0Knots_avoids hp hk).imp realEndpoint_mono realEndpoint_mono
  intro k hk
  simp only [DenominatorKnots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h A (by simp)
  · exact h B (by simp)
  · exact h C (by simp)
  · exact h D (by simp)
  · rw [← realEndpoint_add]
    exact h (A+C) (by simp)
  · rw [← realEndpoint_add]
    exact h (A+D) (by simp)
  · rw [← realEndpoint_add]
    exact h (B+C) (by simp)
  · rw [← realEndpoint_add]
    exact h (B+D) (by simp)

theorem normalized_knots_order {A B C D l u : Nat}
    (hp : (l,u) ∈ (integerD0Knots A B C D).zip (integerD0Knots A B C D).tail) :
    realEndpoint l ≤ realEndpoint u :=
  realEndpoint_mono (adjacent_order _ (integerD0Knots_pairwise A B C D) hp)

theorem normalized_knot_upper {A B C D k : Nat} (hk : k ∈ integerD0Knots A B C D) :
    realEndpoint k ≤ min (realEndpoint A+realEndpoint B) (realEndpoint C+realEndpoint D) := by
  have h := realEndpoint_mono (integerD0Knots_bounds hk)
  simpa only [realEndpoint_min, realEndpoint_add] using h

end Sechstmoment
