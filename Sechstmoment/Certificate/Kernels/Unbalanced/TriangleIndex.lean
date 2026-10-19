import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic

/-! Reindexing the constrained three-dimensional moment sum by a triangle. -/

namespace Sechstmoment

open scoped BigOperators

theorem sum_range_third_eq (f : ℕ → ℕ → ℕ → ℝ) (m a b : ℕ) :
    (∑ c ∈ Finset.range (m + 1),
      if a + b + c = m then f a b c else 0) =
      if a + b ≤ m then f a b (m - a - b) else 0 := by
  by_cases h : a + b ≤ m
  · rw [ite_eq_left h]
    have hc : m - a - b ∈ Finset.range (m + 1) := by
      simp only [Finset.mem_range]
      omega
    rw [Finset.sum_eq_single_of_mem (m - a - b) hc]
    · rw [ite_eq_left (by omega)]
    · intro c _ hne
      rw [ite_eq_right (by omega)]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro c _
    rw [ite_eq_right (by omega)]

theorem sum_range_triangle_row (f : ℕ → ℕ → ℕ → ℝ) (m a : ℕ)
    (ha : a ≤ m) :
    (∑ b ∈ Finset.range (m + 1),
      if a + b ≤ m then f a b (m - a - b) else 0) =
      ∑ b ∈ Finset.range (m - a + 1), f a b (m - a - b) := by
  have hs : Finset.range (m - a + 1) ⊆ Finset.range (m + 1) := by
    apply Finset.range_mono
    omega
  calc
    _ = ∑ b ∈ Finset.range (m - a + 1),
        if a + b ≤ m then f a b (m - a - b) else 0 := by
      symm
      apply Finset.sum_subset hs
      intro b _ hb
      simp only [Finset.mem_range] at hb
      rw [ite_eq_right (by omega)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      simp only [Finset.mem_range] at hb
      rw [ite_eq_left (by omega)]

theorem sum_range_triple_eq_triangle (f : ℕ → ℕ → ℕ → ℝ) (m : ℕ) :
    (∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
      ∑ c ∈ Finset.range (m + 1),
        if a + b + c = m then f a b c else 0) =
      ∑ a ∈ Finset.range (m + 1),
        ∑ b ∈ Finset.range (m - a + 1), f a b (m - a - b) := by
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Finset.mem_range] at ha
  simp_rw [sum_range_third_eq]
  exact sum_range_triangle_row f m a (by omega)

theorem sum_fin_triple_eq_triangle (f : ℕ → ℕ → ℕ → ℝ) (m : ℕ) :
    (∑ a : Fin (m + 1), ∑ b : Fin (m + 1), ∑ c : Fin (m + 1),
      if a.val + b.val + c.val = m then f a.val b.val c.val else 0) =
      ∑ a ∈ Finset.range (m + 1),
        ∑ b ∈ Finset.range (m - a + 1), f a b (m - a - b) := by
  calc
    _ = ∑ a ∈ Finset.range (m + 1), ∑ b : Fin (m + 1), ∑ c : Fin (m + 1),
        if a + b.val + c.val = m then f a b.val c.val else 0 :=
      Fin.sum_univ_eq_sum_range
        (fun a => ∑ b : Fin (m + 1), ∑ c : Fin (m + 1),
          if a + b.val + c.val = m then f a b.val c.val else 0) (m + 1)
    _ = ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
        ∑ c : Fin (m + 1),
        if a + b + c.val = m then f a b c.val else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Fin.sum_univ_eq_sum_range
        (fun b => ∑ c : Fin (m + 1),
          if a + b + c.val = m then f a b c.val else 0) (m + 1)
    _ = ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
        ∑ c ∈ Finset.range (m + 1),
        if a + b + c = m then f a b c else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact Fin.sum_univ_eq_sum_range
        (fun c => if a + b + c = m then f a b c else 0) (m + 1)
    _ = _ := sum_range_triple_eq_triangle f m

end Sechstmoment
