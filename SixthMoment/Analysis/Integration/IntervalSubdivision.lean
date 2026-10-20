import Mathlib.Data.List.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace SixthMoment

theorem list_headD_eq_head {α : Type*} (ks : List α) (fallback : α) (h : ks ≠ []) :
    ks.headD fallback = ks.head h := by
  cases ks with
  | nil => contradiction
  | cons a ks => rfl

theorem list_getLastD_eq_getLast {α : Type*} (ks : List α) (fallback : α) (h : ks ≠ []) :
    ks.getLastD fallback = ks.getLast h := by
  cases ks with
  | nil => contradiction
  | cons a ks => simp only [List.getLastD_cons, List.getLast_eq_getLastD]

theorem interval_sum_consecutive {α : Type*} (f : ℝ → ℝ) (node : α → ℝ)
    (fallback : α) (ks : List α)
    (hint : ∀ a ∈ ks, ∀ b ∈ ks, IntervalIntegrable f MeasureTheory.volume (node a) (node b)) :
    ((ks.zip ks.tail).map (fun ab => ∫ t in node ab.1..node ab.2, f t)).sum =
      ∫ t in node (ks.headD fallback)..node (ks.getLastD fallback), f t := by
  induction ks with
  | nil => simp
  | cons a ks ih =>
      cases ks with
      | nil => simp [List.getLastD]
      | cons b ks =>
          have hit : ∀ x ∈ b::ks, ∀ y ∈ b::ks,
              IntervalIntegrable f MeasureTheory.volume (node x) (node y) := by
            intro x hx y hy
            exact hint x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
          simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.sum_cons]
          have hir := ih hit
          simp only [List.tail_cons, List.headD_cons] at hir
          rw [hir]
          simp only [List.headD_cons]
          have hl : (a::b::ks).getLastD fallback = (b::ks).getLastD fallback := by
            simp only [List.getLastD_cons]
          rw [hl]
          have hlast : (b::ks).getLastD fallback ∈ b::ks := by
            rw [List.getLastD_cons]
            exact List.getLastD_mem_cons
          exact intervalIntegral.integral_add_adjacent_intervals
            (hint a (by simp) b (by simp))
            (hint b (by simp) ((b::ks).getLastD fallback)
              (List.mem_cons_of_mem _ hlast))

end SixthMoment
