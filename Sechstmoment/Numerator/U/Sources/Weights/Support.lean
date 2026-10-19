import Sechstmoment.Numerator.U.Separation.UnitActualSource

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

private theorem block_variable_support {S x : ℝ} (hS : 0<S)
    (hw : rectangularSmoothBlockWeight (x/S)≠0) : x∈Icc S (2*S) := by
  have hs := rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hw)
  exact ⟨by simpa using (le_div_iff₀ hS).mp hs.1,(div_le_iff₀ hS).mp hs.2⟩

/-- Every coordinate support is read from the actual nonzero coefficient
and actual smooth AFE/gap factors. -/
theorem phase_actual_source_tuple_support (T A B H : ℝ) (f g : ℝ → ℝ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) (k n : Fin 4 → ℕ) (a b h : ℕ)
    (ha : phaseActualAmplifierCoefficient T f A a≠0)
    (hb : phaseActualAmplifierCoefficient T g B b≠0)
    (hw : rectangularAFESmoothWeight k n≠0)
    (hh : rectangularSmoothBlockWeight ((h:ℝ)/H)≠0) :
    ∀ j, (rectangularAFESourceTuple a b n h j:ℝ)∈
      Icc ((phaseActualScales A B H k).size j) (2*(phaseActualScales A B H k).size j) := by
  have has : (a:ℝ)∈Icc A (2*A) := by
    by_contra h
    exact ha (phaseActualAmplifierCoefficient_support T f hA a h)
  have hbs : (b:ℝ)∈Icc B (2*B) := by
    by_contra h
    exact hb (phaseActualAmplifierCoefficient_support T g hB b h)
  have hhs := block_variable_support hH hh
  have hws (j : Fin 4) : (n j+1:ℝ)∈
      Icc (rectangularAFESmoothScale (k j)) (2*rectangularAFESmoothScale (k j)) := by
    rw [rectangularAFESmoothWeight_scaled_arguments] at hw
    exact block_variable_support (boundaryActual_scale_pos (k j))
      ((Finset.prod_ne_zero_iff.mp hw) j (Finset.mem_univ j))
  intro j
  fin_cases j <;> simp [rectangularAFESourceTuple,phaseActualScales,QuadraticScales.size]
  all_goals first
    | exact has
    | exact hbs
    | exact hhs
    | exact hws 0
    | exact hws 1
    | exact hws 2
    | exact hws 3

theorem phase_actual_source_tuple_positive (T A B H : ℝ) (f g : ℝ → ℝ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) (k n : Fin 4 → ℕ) (a b h : ℕ)
    (ha : phaseActualAmplifierCoefficient T f A a≠0)
    (hb : phaseActualAmplifierCoefficient T g B b≠0)
    (hw : rectangularAFESmoothWeight k n≠0)
    (hh : rectangularSmoothBlockWeight ((h:ℝ)/H)≠0) :
    ∀ j, 0 < rectangularAFESourceTuple a b n h j := by
  have hs := phase_actual_source_tuple_support T A B H f g hA hB hH k n a b h ha hb hw hh
  have hp := boundaryActual_scales_pos A B H k hA hB hH
  intro j
  have hx : 0 < (rectangularAFESourceTuple a b n h j:ℝ) := (hp j).trans_le (hs j).1
  exact_mod_cast hx

theorem phase_actual_source_tuple_index (T A B H : ℝ) (f g : ℝ → ℝ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) (k n : Fin 4 → ℕ) (a b h : ℕ)
    (ha : phaseActualAmplifierCoefficient T f A a≠0)
    (hb : phaseActualAmplifierCoefficient T g B b≠0)
    (hw : rectangularAFESmoothWeight k n≠0)
    (hh : rectangularSmoothBlockWeight ((h:ℝ)/H)≠0) :
    rectangularAFESourceTuple a b n h∈quadraticIndexSet (phaseActualScales A B H k) := by
  have hs := phase_actual_source_tuple_support T A B H f g hA hB hH k n a b h ha hb hw hh
  have hp := phase_actual_source_tuple_positive T A B H f g hA hB hH k n a b h ha hb hw hh
  apply Fintype.mem_piFinset.mpr
  intro j
  exact Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr (hp j),Nat.le_floor (hs j).2⟩

end
end Sechstmoment
