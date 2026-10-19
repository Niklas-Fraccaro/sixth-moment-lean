import Sechstmoment.Numerator.U.Reconstruction.RectangularSignedMoment

/-! Exact reindexing of the genuine finite AFE boxes by the literal signed
integer gap of the quadratic source. This does not estimate the resulting
weight or assume that hard dyadic indicators are smooth source weights. -/

namespace Sechstmoment
open Complex Source MeasureTheory Set
open scoped BigOperators Topology
open Classical
noncomputable section

def rectangularAFEGap (positive : Bool) (a b : ℕ) (n : Fin 4 → ℕ) : ℕ :=
  if positive then a*(n 0+1)*(n 1+1)-b*(n 2+1)*(n 3+1)
    else b*(n 2+1)*(n 3+1)-a*(n 0+1)*(n 1+1)

def rectangularAFESourceTuple (a b : ℕ) (n : Fin 4 → ℕ) (h : ℕ) : Fin 7 → ℕ :=
  ![a, b, n 0+1, n 1+1, n 2+1, n 3+1, h]

/-- Every genuine positive off-diagonal term has a positive natural gap. -/
theorem rectangular_AFE_gap_pos (positive : Bool) (a b : ℕ) (n : Fin 4 → ℕ)
    (hn : if positive then rectangularPositiveQuadGap a b n
      else rectangularNegativeQuadGap a b n) : 0 < rectangularAFEGap positive a b n := by
  cases positive <;> simp only [rectangularAFEGap, Bool.false_eq_true, ite_false, ite_true] at *
  · exact Nat.sub_pos_of_lt hn
  · exact Nat.sub_pos_of_lt hn

/-- The actual off-diagonal selection is exactly the oriented integer
relation appearing in the quadratic divisor source. -/
theorem rectangular_AFE_gap_source_relation (positive : Bool) (a b : ℕ) (n : Fin 4 → ℕ)
    (hn : if positive then rectangularPositiveQuadGap a b n
      else rectangularNegativeQuadGap a b n) :
    signedQuadraticRelation positive
      (rectangularAFESourceTuple a b n (rectangularAFEGap positive a b n)) := by
  cases positive
  · have hle : a*(n 0+1)*(n 1+1) ≤ b*(n 2+1)*(n 3+1) := le_of_lt hn
    simp [signedQuadraticRelation, rectangularAFESourceTuple, rectangularAFEGap,
      Nat.cast_sub hle]
  · have hle : b*(n 2+1)*(n 3+1) ≤ a*(n 0+1)*(n 1+1) := le_of_lt hn
    simp [signedQuadraticRelation, rectangularAFESourceTuple, rectangularAFEGap,
      Nat.cast_sub hle]

/-- The source relation determines the gap uniquely on each selected AFE
term; no spurious zero gap enters either signed off-diagonal. -/
theorem rectangular_AFE_gap_source_unique (positive : Bool) (a b : ℕ) (n : Fin 4 → ℕ)
    (hn : if positive then rectangularPositiveQuadGap a b n
      else rectangularNegativeQuadGap a b n) (h : ℕ) :
    signedQuadraticRelation positive (rectangularAFESourceTuple a b n h) ↔
      h = rectangularAFEGap positive a b n := by
  have he := rectangular_AFE_gap_source_relation positive a b n hn
  cases positive <;> simp [signedQuadraticRelation, rectangularAFESourceTuple] at *
  · rw [he]
    exact ⟨fun h => Nat.cast_injective (neg_injective h.symm), fun h => by rw [h]⟩
  · rw [he]
    exact ⟨fun h => Nat.cast_injective h.symm, fun h => by rw [h]⟩

def rectangularAFEGaps (positive : Bool) (a b : ℕ) (k : Fin 4 → ℕ) : Finset ℕ :=
  ((rectangularAFEDyadicBox k).filter fun n =>
    if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n).image
      (rectangularAFEGap positive a b)

theorem rectangular_AFE_gaps_positive (positive : Bool) (a b : ℕ) (k : Fin 4 → ℕ)
    (h : ℕ) (hh : h ∈ rectangularAFEGaps positive a b k) : 0 < h := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hh
  exact rectangular_AFE_gap_pos positive a b n (Finset.mem_filter.mp hn).2

/-- A finite actual AFE box is exactly a finite sum over its actual positive
gaps and the literal source relation. The coefficient `F` can be the actual
time integral or the actual Mellin kernel. -/
theorem rectangular_AFE_box_gap_reindex (positive : Bool) (a b : ℕ) (k : Fin 4 → ℕ)
    (F : (Fin 4 → ℕ) → ℂ) :
    (∑ n ∈ rectangularAFEDyadicBox k,
      if (if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n)
        then F n else 0) =
      ∑ h ∈ rectangularAFEGaps positive a b k,
        ∑ n ∈ (rectangularAFEDyadicBox k).filter (fun n =>
          if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n),
          if signedQuadraticRelation positive (rectangularAFESourceTuple a b n h) then F n else 0 := by
  let s := (rectangularAFEDyadicBox k).filter (fun n =>
    if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n)
  have hg : ∀ n ∈ s, rectangularAFEGap positive a b n ∈ rectangularAFEGaps positive a b k := by
    intro n hn
    exact Finset.mem_image_of_mem _ hn
  rw [← Finset.sum_filter]
  change (∑ n ∈ s, F n) = _
  rw [← Finset.sum_fiberwise_of_maps_to hg F]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [rectangular_AFE_gap_source_unique positive a b n (Finset.mem_filter.mp hn).2 h]
  by_cases heq : rectangularAFEGap positive a b n = h
  · simp [heq]
  · simp [heq, Ne.symm heq]

/-- The selected actual integrated blocks are literally indexed by the
source's positive gaps and signed quadratic relations. -/
theorem rectangular_actual_signed_AFE_blocks_gap_reindex (positive : Bool) (a b : ℕ)
    (G : ℂ → ℂ) (α : MomentShifts) (w : ℝ → ℂ) :
    rectangularAFESelectedBlocks G α w (fun n =>
      if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n) =
      ∑' k : Fin 4 → ℕ, ∑ h ∈ rectangularAFEGaps positive a b k,
        ∑ n ∈ (rectangularAFEDyadicBox k).filter (fun n =>
          if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n),
          if signedQuadraticRelation positive (rectangularAFESourceTuple a b n h)
            then ∫ t : ℝ, w t*bblrAFESummand G α t n else 0 := by
  unfold rectangularAFESelectedBlocks
  apply tsum_congr
  intro k
  convert rectangular_AFE_box_gap_reindex positive a b k
    (fun n => ∫ t : ℝ, w t*bblrAFESummand G α t n) using 1
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : if positive then rectangularPositiveQuadGap a b n
    else rectangularNegativeQuadGap a b n
  · simp [hp]
  · simp [hp]

end
end Sechstmoment
