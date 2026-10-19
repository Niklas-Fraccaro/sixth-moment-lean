import Mathlib.Tactic

/-!
An elementary, unconditional count of actual positive factor pairs in a
short product interval. This is a counting component for the central BBLR
near-resonant error; it does not assert a moment or reconstruction bound.
-/

namespace Sechstmoment
open scoped BigOperators

def positiveFactorSlice (n Q L H : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Q).filter fun m => L ≤ n*m ∧ n*m ≤ L+H

theorem positiveFactorSlice_card_le {n : ℕ} (hn : 0 < n) (Q L H : ℕ) :
    (positiveFactorSlice n Q L H).card ≤ H+1 := by
  have hi : Function.Injective (fun m : ℕ => n*m) :=
    fun _ _ he => Nat.eq_of_mul_eq_mul_left hn he
  have hs : (positiveFactorSlice n Q L H).image (fun m => n*m) ⊆ Finset.Icc L (L+H) := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hm).2
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hi] at hc
  rw [Nat.card_Icc] at hc
  omega

def positiveShortFactorPairs (Q L H : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter fun p =>
    L ≤ p.1*p.2 ∧ p.1*p.2 ≤ L+H ∧ p.1*p.2 ≤ Q

theorem positiveShortFactorPairs_small_factor {Q L H K : ℕ} (hQ : Q ≤ K^2)
    {p : ℕ × ℕ} (hp : p ∈ positiveShortFactorPairs Q L H) :
    p.1 ≤ K ∨ p.2 ≤ K := by
  have hb := (Finset.mem_filter.mp hp).2.2.2
  by_contra hn
  push Not at hn
  have hm : K^2 < p.1*p.2 := by nlinarith
  omega

theorem positiveShortFactorPairs_card_le {Q L H K : ℕ} (hQ : Q ≤ K^2) :
    (positiveShortFactorPairs Q L H).card ≤ 2*K*(H+1) := by
  let S : Finset (ℕ × ℕ) := (Finset.Icc 1 K).biUnion fun n =>
    (positiveFactorSlice n Q L H).image fun m => (n,m)
  have hS : S.card ≤ K*(H+1) := by
    calc
      S.card ≤ ∑ n ∈ Finset.Icc 1 K,
          ((positiveFactorSlice n Q L H).image fun m => (n,m)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ n ∈ Finset.Icc 1 K, (H+1) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' : 0 < n := by have hh := (Finset.mem_Icc.mp hn).1; omega
        rw [Finset.card_image_of_injective _ (by intro x y he; exact (Prod.mk.inj he).2)]
        exact positiveFactorSlice_card_le hn' Q L H
      _ = K*(H+1) := by simp [Nat.card_Icc]
  have hsub : positiveShortFactorPairs Q L H ⊆ S ∪ S.image Prod.swap := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpair := Finset.mem_product.mp hp'.1
    rcases positiveShortFactorPairs_small_factor hQ hp with hfirst | hsecond
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨p.1, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hpair.1).1,hfirst⟩, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨p.2, Finset.mem_filter.mpr ⟨hpair.2,hp'.2.1,hp'.2.2.1⟩, ?_⟩
      exact Prod.mk.eta
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨p.swap, ?_, by simp⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨p.2, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hpair.2).1,hsecond⟩, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨p.1, Finset.mem_filter.mpr ⟨hpair.1, ?_⟩, rfl⟩
      simpa [Nat.mul_comm] using ⟨hp'.2.1,hp'.2.2.1⟩
  calc
    (positiveShortFactorPairs Q L H).card ≤ (S ∪ S.image Prod.swap).card :=
      Finset.card_le_card hsub
    _ ≤ S.card + (S.image Prod.swap).card := Finset.card_union_le _ _
    _ ≤ S.card + S.card := Nat.add_le_add_left (Finset.card_image_le) _
    _ ≤ 2*K*(H+1) := by nlinarith

end Sechstmoment
