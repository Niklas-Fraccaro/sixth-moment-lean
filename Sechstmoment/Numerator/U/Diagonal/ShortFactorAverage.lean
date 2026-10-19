import Mathlib.NumberTheory.Harmonic.Bounds
import Sechstmoment.Numerator.U.Diagonal.ShortFactorCount

/-!
# Averaged short-product interval count

The actual quotient H/n is retained in each positive first-factor fiber.
The two small-factor orientations therefore give H log Q rather than
H sqrt Q in the main count. These are unconditional finite counts.
-/
namespace Sechstmoment
open scoped BigOperators
open Classical

theorem positiveFactorSlice_card_le_quotient {n : ℕ} (hn : 0 < n) (Q L H : ℕ) :
    (positiveFactorSlice n Q L H).card ≤ H/n+1 := by
  by_cases hne : (positiveFactorSlice n Q L H).Nonempty
  · let m₀ := (positiveFactorSlice n Q L H).min' hne
    have hm₀ : m₀ ∈ positiveFactorSlice n Q L H := Finset.min'_mem _ _
    have hlow : L ≤ n*m₀ := (Finset.mem_filter.mp hm₀).2.1
    have hsub (m : ℕ) (hm : m ∈ positiveFactorSlice n Q L H) :
        m₀ ≤ m := Finset.min'_le _ _ hm
    have hrange : (positiveFactorSlice n Q L H).image (fun m => m-m₀) ⊆
        Finset.Icc 0 (H/n) := by
      intro d hd
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hd
      apply Finset.mem_Icc.mpr
      refine ⟨Nat.zero_le _, ?_⟩
      apply (Nat.le_div_iff_mul_le hn).mpr
      have hhigh : n*m ≤ L+H := (Finset.mem_filter.mp hm).2.2
      have hdecomp : n*m = n*m₀ + n*(m-m₀) := by
        rw [← Nat.mul_add, Nat.add_sub_of_le (hsub m hm)]
      nlinarith
    have hinj : Set.InjOn (fun m : ℕ => m-m₀) (positiveFactorSlice n Q L H) := by
      intro x hx y hy hxy
      change x-m₀ = y-m₀ at hxy
      calc
        x = (x-m₀)+m₀ := (Nat.sub_add_cancel (hsub x hx)).symm
        _ = (y-m₀)+m₀ := congrArg (fun z : ℕ => z+m₀) hxy
        _ = y := Nat.sub_add_cancel (hsub y hy)
    have hcard := Finset.card_le_card hrange
    rw [Finset.card_image_iff.mpr hinj, Nat.card_Icc] at hcard
    simpa using hcard
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

/-- The finite quotient sum in the small-first-factor orientation is
bounded by the exact harmonic sum, with the endpoint cost K retained. -/
theorem positiveFactorSlice_small_factor_sum_le_harmonic (K Q L H : ℕ) :
    (∑ n ∈ Finset.Icc 1 K, ((positiveFactorSlice n Q L H).card : ℝ)) ≤
      (H : ℝ)*(harmonic K : ℝ) + K := by
  have hH : (harmonic K : ℝ) = ∑ n ∈ Finset.Icc 1 K, 1/(n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 K, (((H/n : ℕ) : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' : 0 < n := by have hh := (Finset.mem_Icc.mp hn).1; omega
      exact_mod_cast positiveFactorSlice_card_le_quotient hn' Q L H
    _ ≤ ∑ n ∈ Finset.Icc 1 K, ((H : ℝ)/(n : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' : 0 < n := by have hh := (Finset.mem_Icc.mp hn).1; omega
      have hq : ((H/n : ℕ) : ℝ) ≤ (H : ℝ)/(n : ℝ) := by
        apply (le_div_iff₀ (by exact_mod_cast hn' : (0 : ℝ) < n)).mpr
        exact_mod_cast Nat.div_mul_le_self H n
      exact add_le_add hq le_rfl
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
        mul_one, div_eq_mul_inv]
      rw [← Finset.mul_sum, hH]
      simp only [one_div]

/-- The actual short factor-pair set has a harmonic averaged bound after
covering the two possible small-factor orientations. -/
theorem positiveShortFactorPairs_card_le_harmonic {Q L H K : ℕ} (hQ : Q ≤ K^2) :
    ((positiveShortFactorPairs Q L H).card : ℝ) ≤
      2*(H : ℝ)*(harmonic K : ℝ) + 2*K := by
  let S : Finset (ℕ × ℕ) := (Finset.Icc 1 K).biUnion fun n =>
    (positiveFactorSlice n Q L H).image fun m => (n,m)
  have hS : (S.card : ℝ) ≤ (H : ℝ)*(harmonic K : ℝ) + K := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 K,
          (((positiveFactorSlice n Q L H).image fun m => (n,m)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ = ∑ n ∈ Finset.Icc 1 K, ((positiveFactorSlice n Q L H).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.card_image_of_injective _ (by intro x y he; exact (Prod.mk.inj he).2)]
      _ ≤ _ := positiveFactorSlice_small_factor_sum_le_harmonic K Q L H
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
  have hc : (positiveShortFactorPairs Q L H).card ≤ 2*S.card := by
    calc
      _ ≤ (S ∪ S.image Prod.swap).card := Finset.card_le_card hsub
      _ ≤ S.card + (S.image Prod.swap).card := Finset.card_union_le _ _
      _ ≤ S.card + S.card := Nat.add_le_add_left Finset.card_image_le _
      _ = _ := by omega
  have hc' : ((positiveShortFactorPairs Q L H).card : ℝ) ≤ 2*(S.card : ℝ) := by
    exact_mod_cast hc
  nlinarith

/-- A quantitative short-product interval bound with a logarithmic H-term. -/
theorem positiveShortFactorPairs_card_le_log {Q L H K : ℕ} (hQ : Q ≤ K^2) :
    ((positiveShortFactorPairs Q L H).card : ℝ) ≤
      2*(H : ℝ)*(1+Real.log (K : ℝ)) + 2*K := by
  have hharm := harmonic_le_one_add_log K
  have hH : 0 ≤ (H : ℝ) := Nat.cast_nonneg _
  exact (positiveShortFactorPairs_card_le_harmonic hQ).trans (by
    nlinarith [mul_le_mul_of_nonneg_left hharm hH])

end Sechstmoment
