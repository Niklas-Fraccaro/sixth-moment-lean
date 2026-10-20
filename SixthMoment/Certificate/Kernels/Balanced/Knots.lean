import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Sort
import SixthMoment.Arithmetic.Exact.Polynomials

namespace SixthMoment

theorem insertSorted_eq_orderedInsert (a : Nat) (xs : List Nat) :
    Finite.insertSorted a xs = xs.orderedInsert (· ≤ ·) a := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [Finite.insertSorted, List.orderedInsert_cons, ih]

theorem sort_eq_insertionSort (xs : List Nat) :
    Finite.sort xs = xs.insertionSort (· ≤ ·) := by
  unfold Finite.sort List.insertionSort
  congr 1
  funext a xs
  exact insertSorted_eq_orderedInsert a xs

theorem sort_pairwise (xs : List Nat) : (Finite.sort xs).Pairwise (· ≤ ·) := by
  rw [sort_eq_insertionSort]
  exact List.pairwise_insertionSort _ _

theorem mem_sort (k : Nat) (xs : List Nat) : k ∈ Finite.sort xs ↔ k ∈ xs := by
  rw [sort_eq_insertionSort, List.mem_insertionSort]

theorem adjacent_no_intermediate {α : Type*} [LinearOrder α] (ks : List α)
    (hs : ks.Pairwise (· ≤ ·)) {l u k : α}
    (hp : (l,u) ∈ ks.zip ks.tail) (hk : k ∈ ks) : k ≤ l ∨ u ≤ k := by
  induction ks with
  | nil => simp at hp
  | cons a ks ih =>
      cases ks with
      | nil => simp at hp
      | cons b ks =>
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with hp | hp
          · have he := Prod.mk.inj hp
            rcases he with ⟨rfl,rfl⟩
            rcases List.mem_cons.mp hk with hk | hk
            · subst k
              exact Or.inl le_rfl
            · exact Or.inr (hs.of_cons.rel_head hk)
          · rcases List.mem_cons.mp hk with hk | hk
            · subst k
              exact Or.inl (List.rel_of_pairwise_cons hs (List.of_mem_zip hp).1)
            · exact ih hs.of_cons hp hk

theorem adjacent_order {α : Type*} [LinearOrder α] (ks : List α)
    (hs : ks.Pairwise (· ≤ ·)) {l u : α} (hp : (l,u) ∈ ks.zip ks.tail) : l ≤ u := by
  induction ks with
  | nil => simp at hp
  | cons a ks ih =>
      cases ks with
      | nil => simp at hp
      | cons b ks =>
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with hp | hp
          · rcases Prod.mk.inj hp with ⟨rfl,rfl⟩
            exact List.rel_of_pairwise_cons hs (by simp)
          · exact ih hs.of_cons hp

def integerD0Knots (A B C D : Nat) : List Nat :=
  let e := min (A+B) (C+D)
  Finite.sort (([0,e] ++ [A,B,C,D,A+C,A+D,B+C,B+D].filter
    (fun v => decide (0<v ∧ v<e))).eraseDups)

theorem integerD0Knots_pairwise (A B C D : Nat) :
    (integerD0Knots A B C D).Pairwise (· ≤ ·) := sort_pairwise _

theorem integerD0Knots_mem (A B C D k : Nat) :
    k ∈ integerD0Knots A B C D ↔
      k=0 ∨ k=min (A+B) (C+D) ∨
        (k ∈ [A,B,C,D,A+C,A+D,B+C,B+D] ∧ 0<k ∧ k<min (A+B) (C+D)) := by
  simp [integerD0Knots, mem_sort]

theorem integerD0Knots_bounds {A B C D k : Nat} (hk : k ∈ integerD0Knots A B C D) :
    k ≤ min (A+B) (C+D) := by
  rw [integerD0Knots_mem] at hk
  rcases hk with rfl | rfl | ⟨_,_,hk⟩
  · omega
  · exact le_rfl
  · exact hk.le

theorem integerD0Knots_nonempty (A B C D : Nat) : integerD0Knots A B C D ≠ [] := by
  apply List.ne_nil_of_mem (a := 0)
  rw [integerD0Knots_mem]
  exact Or.inl rfl

theorem integerD0Knots_endpoints (A B C D : Nat) :
    (integerD0Knots A B C D).head (integerD0Knots_nonempty A B C D) = 0 ∧
      (integerD0Knots A B C D).getLast (integerD0Knots_nonempty A B C D) =
        min (A+B) (C+D) := by
  have h0 : 0 ∈ integerD0Knots A B C D := by rw [integerD0Knots_mem]; exact Or.inl rfl
  have he : min (A+B) (C+D) ∈ integerD0Knots A B C D := by
    rw [integerD0Knots_mem]
    exact Or.inr (Or.inl rfl)
  constructor
  · exact Nat.eq_zero_of_le_zero ((integerD0Knots_pairwise A B C D).rel_head h0)
  · exact le_antisymm (integerD0Knots_bounds (List.getLast_mem _))
      ((integerD0Knots_pairwise A B C D).rel_getLast he)

theorem integerD0Knots_avoids {A B C D l u k : Nat}
    (hp : (l,u) ∈ (integerD0Knots A B C D).zip (integerD0Knots A B C D).tail)
    (hk : k ∈ [A,B,C,D,A+C,A+D,B+C,B+D]) : k ≤ l ∨ u ≤ k := by
  by_cases hm : 0<k ∧ k<min (A+B) (C+D)
  · apply adjacent_no_intermediate _ (integerD0Knots_pairwise A B C D) hp
    rw [integerD0Knots_mem]
    exact Or.inr (Or.inr ⟨hk,hm⟩)
  · have hu := integerD0Knots_bounds (List.mem_of_mem_tail (List.of_mem_zip hp).2)
    omega

end SixthMoment
