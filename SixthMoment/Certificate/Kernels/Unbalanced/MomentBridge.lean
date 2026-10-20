import SixthMoment.Certificate.Kernels.Unbalanced.IntegerMoments
import SixthMoment.Certificate.Kernels.Unbalanced.MaskMoments
import SixthMoment.Certificate.Kernels.Unbalanced.TriangleIndex

namespace SixthMoment
open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] minusBoxEvenMoment

private theorem list_sum_flatMap_real {α : Type*} (xs : List α) (f : α → List ℝ) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem list_sum_map_range_real (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

noncomputable def minusMomentMonomial (k : ℕ) (a b c H : ℝ) (d₁ d₂ d₃ : ℕ) : ℝ :=
  (Nat.factorial k : ℝ)*a^d₁*b^d₂*c^d₃*H^(k+5-d₁-d₂-d₃) /
    ((2 : ℝ)^k*(Nat.factorial d₁ : ℝ)*Nat.factorial d₂*Nat.factorial d₃*
      Nat.factorial (k+5-d₁-d₂-d₃))

theorem realMomentEval_normalized_expand {k mask : ℕ}
    (hk : k ∈ [0,2,4,6,8]) (hm : mask ∈ List.range 8) (a b c H : ℝ) :
    realMomentEval k mask a b c H / (256 * (Nat.factorial 13 : ℝ)) =
      ∑ l₁ ∈ Finset.range (k/2+1), ∑ l₂ ∈ Finset.range (k/2-l₁+1),
        ∑ d₁ ∈ Finset.range (if Finite.bit mask 0 then 2*l₁+2 else 1),
        ∑ d₂ ∈ Finset.range (if Finite.bit mask 1 then 2*l₂+2 else 1),
        ∑ d₃ ∈ Finset.range (if Finite.bit mask 2 then 2*(k/2-l₁-l₂)+2 else 1),
          minusMomentMonomial k a b c H d₁ d₂ d₃ := by
  rw [realMomentEval_normalized hk hm]
  simp only [Finite.momentTerms, List.map_flatMap, List.map_map, Function.comp_def,
    list_sum_flatMap_real, list_sum_map_range_real]
  rfl

theorem twice_fin_five_degree (m : Fin 5) : 2*m.val ∈ [0,2,4,6,8] := by
  fin_cases m <;> simp

theorem realMomentEval_normalized_even_expand (m : Fin 5) (mask : Fin 8)
    (a b c H : ℝ) :
    realMomentEval (2*m.val) mask.val a b c H / (Finite.dminusDenominator : ℝ) =
      ∑ l₁ ∈ Finset.range (m.val+1), ∑ l₂ ∈ Finset.range (m.val-l₁+1),
        ∑ d₁ ∈ Finset.range (if Finite.bit mask.val 0 then 2*l₁+2 else 1),
        ∑ d₂ ∈ Finset.range (if Finite.bit mask.val 1 then 2*l₂+2 else 1),
        ∑ d₃ ∈ Finset.range (if Finite.bit mask.val 2 then 2*(m.val-l₁-l₂)+2 else 1),
          minusMomentMonomial (2*m.val) a b c H d₁ d₂ d₃ := by
  rw [dminusDenominator_real]
  have he := realMomentEval_normalized_expand (twice_fin_five_degree m)
    (List.mem_range.mpr mask.isLt) a b c H
  simpa only [Nat.mul_div_right m.val (by norm_num : 0 < 2)] using he

theorem weightedMaskTriplet_eq_monomials (m l₁ l₂ l₃ : ℕ)
    (hl : l₁+l₂+l₃ = m) (mask : Fin 8) (a b c H : ℝ) :
    ((Nat.factorial (2*m) : ℝ)/(2 : ℝ)^(2*m)) *
        (translatedSimplexMonomialValue H
          (minusMaskCap a mask 0) (minusMaskCap b mask 1) (minusMaskCap c mask 2)
          (2*l₁+1) (2*l₂+1) (2*l₃+1) /
          ((Nat.factorial (2*l₁+1) : ℝ)*Nat.factorial (2*l₂+1)*Nat.factorial (2*l₃+1))) =
      ∑ d₁ ∈ Finset.range (if Finite.bit mask.val 0 then 2*l₁+2 else 1),
        ∑ d₂ ∈ Finset.range (if Finite.bit mask.val 1 then 2*l₂+2 else 1),
        ∑ d₃ ∈ Finset.range (if Finite.bit mask.val 2 then 2*l₃+2 else 1),
          minusMomentMonomial (2*m) a b c H d₁ d₂ d₃ := by
  calc
    _ = ((Nat.factorial (2*m) : ℝ) /
        ((2 : ℝ)^(2*m)*Nat.factorial (2*l₁+1)*Nat.factorial (2*l₂+1)*
          Nat.factorial (2*l₃+1))) *
        translatedSimplexMonomialValue H
          (minusMaskCap a mask 0) (minusMaskCap b mask 1) (minusMaskCap c mask 2)
          (2*l₁+1) (2*l₂+1) (2*l₃+1) := by ring
    _ = ((Nat.factorial (2*m) : ℝ)/(2 : ℝ)^(2*m)) *
        minusMaskMonomialSum H a b c mask (2*l₁+1) (2*l₂+1) (2*l₃+1) :=
      translatedSimplexMonomialValue_weighted_mask H a b c mask _ _ _ _
    _ = _ := by
      unfold minusMaskMonomialSum
      simp_rw [translatedSimplexExponent_even hl, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d₁ _
      apply Finset.sum_congr rfl
      intro d₂ _
      apply Finset.sum_congr rfl
      intro d₃ _
      unfold minusMomentMonomial
      ring

theorem minusMaskEvenMomentValue_eq_realMomentEval (m : Fin 5) (mask : Fin 8)
    (a b c H : ℝ) :
    minusMaskEvenMomentValue m.val mask a b c H =
      realMomentEval (2*m.val) mask.val a b c H / (Finite.dminusDenominator : ℝ) := by
  unfold minusMaskEvenMomentValue
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [sum_fin_triple_eq_triangle (fun l₁ l₂ l₃ =>
    ((Nat.factorial (2*m.val) : ℝ)/(2 : ℝ)^(2*m.val)) *
      (translatedSimplexMonomialValue H
        (minusMaskCap a mask 0) (minusMaskCap b mask 1) (minusMaskCap c mask 2)
        (2*l₁+1) (2*l₂+1) (2*l₃+1) /
        ((Nat.factorial (2*l₁+1) : ℝ)*Nat.factorial (2*l₂+1)*Nat.factorial (2*l₃+1))))
    m.val]
  rw [realMomentEval_normalized_even_expand]
  apply Finset.sum_congr rfl
  intro l₁ hl₁
  apply Finset.sum_congr rfl
  intro l₂ hl₂
  have hl : l₁+l₂+(m.val-l₁-l₂) = m.val := by
    have h₁ := Finset.mem_range.mp hl₁
    have h₂ := Finset.mem_range.mp hl₂
    omega
  exact weightedMaskTriplet_eq_monomials m.val l₁ l₂ (m.val-l₁-l₂) hl mask a b c H

theorem boundedSimplexSlice_minusBoxEvenMoment_integral {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : ℝ) (m : Fin 5) :
    (∫ r, (boundedSimplexSlice a b c H).indicator
      (fun r => minusBoxEvenMoment m.val (r 0) (r 1) (H-r 0-r 1)) r) =
      ∑ mask : Fin 8, simplexMaskSign mask *
        (if H-simplexMaskShift a b c mask ≤ 0 then 0 else
          realMomentEval (2*m.val) mask.val a b c (H-simplexMaskShift a b c mask) /
            (Finite.dminusDenominator : ℝ)) := by
  rw [boundedSimplexSlice_minusBoxEvenMoment_masks ha hb hc H m.val]
  simp_rw [minusMaskEvenMomentValue_eq_realMomentEval]

end SixthMoment
