import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Actual reciprocal-minimum amplifier count

This is the elementary finite average used after a near-resonant estimate
with denominator min(u,v). Both genuine amplifier ranges are retained.
No moment error or divisor-growth hypothesis is assumed.
-/
namespace Sechstmoment
open scoped BigOperators

/-- The actual positive integer amplifier rectangle. -/
def positiveAmplifierRectangle (A B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 A) ×ˢ (Finset.Icc 1 B)

theorem positive_amplifier_reciprocal_min_le_add (u v : ℕ) :
    1/(min u v : ℝ) ≤ 1/(u : ℝ) + 1/(v : ℝ) := by
  rcases le_total u v with huv | hvu
  · have hreal : (u : ℝ) ≤ v := by exact_mod_cast huv
    rw [min_eq_left hreal]
    have hv : 0 ≤ 1/(v : ℝ) := by positivity
    linarith
  · have hreal : (v : ℝ) ≤ u := by exact_mod_cast hvu
    rw [min_eq_right hreal]
    have hu : 0 ≤ 1/(u : ℝ) := by positivity
    linarith

/-- Direct harmonic majorant for the complete positive amplifier rectangle. -/
theorem positive_amplifier_reciprocal_min_sum_le_harmonic (A B : ℕ) :
    (∑ p ∈ positiveAmplifierRectangle A B, 1/(min p.1 p.2 : ℝ)) ≤
      (B : ℝ)*(harmonic A : ℝ) + (A : ℝ)*(harmonic B : ℝ) := by
  have hH (N : ℕ) : (harmonic N : ℝ) = ∑ n ∈ Finset.Icc 1 N, 1/(n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  calc
    _ ≤ ∑ p ∈ positiveAmplifierRectangle A B, (1/(p.1 : ℝ) + 1/(p.2 : ℝ)) :=
      Finset.sum_le_sum (fun p _ => positive_amplifier_reciprocal_min_le_add p.1 p.2)
    _ = _ := by
      unfold positiveAmplifierRectangle
      rw [Finset.sum_add_distrib, Finset.sum_product, Finset.sum_product]
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [← Finset.mul_sum, hH, hH]

/-- The larger amplifier length controls both actual multiplicities. -/
theorem positive_amplifier_reciprocal_min_sum_le_max_harmonic (A B : ℕ) :
    (∑ p ∈ positiveAmplifierRectangle A B, 1/(min p.1 p.2 : ℝ)) ≤
      max (A : ℝ) (B : ℝ)*((harmonic A : ℝ) + (harmonic B : ℝ)) := by
  have hH (N : ℕ) : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hHA := hH A
  have hHB := hH B
  have hA := le_max_left (A : ℝ) (B : ℝ)
  have hB := le_max_right (A : ℝ) (B : ℝ)
  exact (positive_amplifier_reciprocal_min_sum_le_harmonic A B).trans (by
    nlinarith [mul_le_mul_of_nonneg_right hA hHB,
      mul_le_mul_of_nonneg_right hB hHA])

/-- A literal logarithmic bound, valid also for an empty zero-length range. -/
theorem positive_amplifier_reciprocal_min_sum_le_log (A B : ℕ) :
    (∑ p ∈ positiveAmplifierRectangle A B, 1/(min p.1 p.2 : ℝ)) ≤
      max (A : ℝ) (B : ℝ)*(2 + Real.log (A : ℝ) + Real.log (B : ℝ)) := by
  exact (positive_amplifier_reciprocal_min_sum_le_max_harmonic A B).trans
    (mul_le_mul_of_nonneg_left (by
      have hA := harmonic_le_one_add_log A
      have hB := harmonic_le_one_add_log B
      linarith) (by positivity))

/-- Restricting the actual rectangle, for example to smooth amplifier
supports, cannot enlarge this positive reciprocal-minimum average. -/
theorem positive_amplifier_reciprocal_min_subset_le_log (A B : ℕ)
    (s : Finset (ℕ × ℕ)) (hs : s ⊆ positiveAmplifierRectangle A B) :
    (∑ p ∈ s, 1/(min p.1 p.2 : ℝ)) ≤
      max (A : ℝ) (B : ℝ)*(2 + Real.log (A : ℝ) + Real.log (B : ℝ)) := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => by positivity)).trans
    (positive_amplifier_reciprocal_min_sum_le_log A B)

end Sechstmoment
