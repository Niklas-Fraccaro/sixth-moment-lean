import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Sechstmoment.Certificate.Kernels.Balanced.NormalizedKnots


namespace Sechstmoment

open scoped BigOperators
open _root_.Sechstmoment.Finite

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem denominatorMinus_integer_shift (A B C D : ℤ) :
    (((Finite.scale - (24 * A + 24 * B + 24 * C - 24 * D)) / 2 : ℤ) : ℝ) =
      ((Finite.scale : ℝ) - (24 * A + 24 * B + 24 * C - 24 * D)) / 2 := by
  have h :
      (((Finite.scale - (24 * A + 24 * B + 24 * C - 24 * D)) / 2 : ℤ) : ℝ) * 2 =
        (Finite.scale : ℝ) - (24 * A + 24 * B + 24 * C - 24 * D) := by
    exact_mod_cast Finite.dminus_half_shift_exact A B C D
  linarith

theorem denominatorMinus_normalized_shift (A B C D : ℕ) :
    (((Finite.scale - (24 * (A : ℤ) + 24 * B + 24 * C - 24 * D)) / 2 : ℤ) : ℝ) /
        (Finite.scale : ℝ) =
      (1 - (realEndpoint A + realEndpoint B + realEndpoint C - realEndpoint D)) / 2 := by
  rw [denominatorMinus_integer_shift]
  simp only [realEndpoint_scale, Int.cast_natCast]
  have hs : (Finite.scale : ℝ) ≠ 0 := ne_of_gt scale_real_pos
  field_simp [hs]

theorem minus_integer_productCoefficient (p q : List ℤ) (t0 : ℤ) (k : Fin 9) :
    (coef (polyMul (shifted p (-t0) 1) (shifted q t0 1)) k.val : ℝ) =
      (Finite.scale : ℝ) ^ (8 - k.val) *
        productCoefficient
          (shiftedCoefficient (fun r => (coef p r.val : ℝ))
            (-(t0 : ℝ) / (Finite.scale : ℝ)) 1)
          (shiftedCoefficient (fun r => (coef q r.val : ℝ))
            ((t0 : ℝ) / (Finite.scale : ℝ)) 1) k := by
  fin_cases k <;>
    norm_num [polyMul, shifted, Finite.sum, coef, List.range_succ,
      Finite.choose, Finite.factorial, Finite.scale, Finite.base,
      productCoefficient, shiftedCoefficient, Fin.sum_univ_succ, Nat.choose] <;>
    ring

theorem minus_integer_productCoefficient_div (p q : List ℤ) (t0 : ℤ) (k : Fin 9) :
    (coef (polyMul (shifted p (-t0) 1) (shifted q t0 1)) k.val : ℝ) /
        (Finite.scale : ℝ) ^ (8 - k.val) =
      productCoefficient
        (shiftedCoefficient (fun r => (coef p r.val : ℝ))
          (-(t0 : ℝ) / (Finite.scale : ℝ)) 1)
        (shiftedCoefficient (fun r => (coef q r.val : ℝ))
          ((t0 : ℝ) / (Finite.scale : ℝ)) 1) k := by
  rw [minus_integer_productCoefficient]
  have hs : (Finite.scale : ℝ) ≠ 0 := by norm_num [Finite.scale, Finite.base]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hs)

theorem denominatorMinus_integer_productCoefficient (p q : List ℤ)
    (A B C D : ℕ) (k : Fin 9) :
    (coef (polyMul
      (shifted p (-((Finite.scale - (24 * (A : ℤ) + 24 * B + 24 * C - 24 * D)) / 2)) 1)
      (shifted q ((Finite.scale - (24 * (A : ℤ) + 24 * B + 24 * C - 24 * D)) / 2) 1))
        k.val : ℝ) /
        (Finite.scale : ℝ) ^ (8 - k.val) =
      productCoefficient
        (shiftedCoefficient (fun r => (coef p r.val : ℝ))
          (-((1 - (realEndpoint A + realEndpoint B + realEndpoint C - realEndpoint D)) / 2)) 1)
        (shiftedCoefficient (fun r => (coef q r.val : ℝ))
          ((1 - (realEndpoint A + realEndpoint B + realEndpoint C - realEndpoint D)) / 2) 1) k := by
  rw [minus_integer_productCoefficient_div]
  rw [neg_div, denominatorMinus_normalized_shift]

theorem minus_integer_normalized_sum (p q : List ℤ) (t0 : ℤ) (moments : Fin 9 → ℝ) :
    (∑ k : Fin 9,
      (coef (polyMul (shifted p (-t0) 1) (shifted q t0 1)) k.val : ℝ) * moments k) /
        (Finite.scale : ℝ) ^ 13 =
      ∑ k : Fin 9,
        productCoefficient
          (shiftedCoefficient (fun r => (coef p r.val : ℝ))
            (-(t0 : ℝ) / (Finite.scale : ℝ)) 1)
          (shiftedCoefficient (fun r => (coef q r.val : ℝ))
            ((t0 : ℝ) / (Finite.scale : ℝ)) 1) k *
          (moments k / (Finite.scale : ℝ) ^ (k.val + 5)) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [minus_integer_productCoefficient]
  have hdeg : 8 - k.val + (k.val + 5) = 13 := by omega
  have hp : (Finite.scale : ℝ) ^ 13 =
      (Finite.scale : ℝ) ^ (8 - k.val) * (Finite.scale : ℝ) ^ (k.val + 5) := by
    rw [← pow_add, hdeg]
  have hs : (Finite.scale : ℝ) ≠ 0 := by norm_num [Finite.scale, Finite.base]
  rw [hp]
  field_simp

theorem minus_integer_normalized_even_sum (p q : List ℤ) (t0 : ℤ)
    (moments : Fin 5 → ℝ) :
    (∑ j : Fin 5,
      (coef (polyMul (shifted p (-t0) 1) (shifted q t0 1)) (2 * j.val) : ℝ) * moments j) /
        (Finite.scale : ℝ) ^ 13 =
      ∑ j : Fin 5,
        productCoefficient
          (shiftedCoefficient (fun r => (coef p r.val : ℝ))
            (-(t0 : ℝ) / (Finite.scale : ℝ)) 1)
          (shiftedCoefficient (fun r => (coef q r.val : ℝ))
            ((t0 : ℝ) / (Finite.scale : ℝ)) 1) ⟨2 * j.val, by omega⟩ *
          (moments j / (Finite.scale : ℝ) ^ (2 * j.val + 5)) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hc := minus_integer_productCoefficient p q t0 (⟨2 * j.val, by omega⟩ : Fin 9)
  rw [hc]
  have hdeg : 8 - 2 * j.val + (2 * j.val + 5) = 13 := by omega
  have hp : (Finite.scale : ℝ) ^ 13 =
      (Finite.scale : ℝ) ^ (8 - 2 * j.val) * (Finite.scale : ℝ) ^ (2 * j.val + 5) := by
    rw [← pow_add, hdeg]
  have hs : (Finite.scale : ℝ) ≠ 0 := by norm_num [Finite.scale, Finite.base]
  rw [hp]
  field_simp

end Sechstmoment
