import Mathlib.Algebra.BigOperators.Group.List.Basic
import SixthMoment.Certificate.Exact.GramEntries

namespace SixthMoment.Finite

theorem finite_sum_eq_list_sum (xs : List Int) : sum xs = xs.sum :=
  List.sum_eq_foldl.symm

theorem chunks_length {α : Type} (size n : Nat) (xs : List α) :
    (chunks size n xs).length = n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [chunks, ih]

theorem range_getD {α : Type} (xs : List α) (default : α) :
    (List.range xs.length).map (fun i => xs[i]?.getD default) = xs := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [h₂]

theorem block_indexing_complete : (List.range blockCount).map pairBlock = blocks := by
  have hl : blocks.length = blockCount := chunks_length blockSize blockCount pairs
  rw [← hl]
  exact range_getD blocks []

theorem block_sums_complete (f : Nat × Nat → Int) :
    sum ((List.range blockCount).map fun k => sum ((pairBlock k).map f)) =
      sum (pairs.map f) := by
  simp_rw [finite_sum_eq_list_sum]
  change ((List.range blockCount).map
    ((fun b : List (Nat × Nat) => (b.map f).sum) ∘ pairBlock)).sum = _
  rw [← List.map_map, block_indexing_complete, ← blocks_cover_pairs]
  simp [List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]

end SixthMoment.Finite
