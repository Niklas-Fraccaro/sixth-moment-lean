import Sechstmoment.Certificate.Kernels.Unbalanced.BoxPolynomial
import Sechstmoment.Certificate.Kernels.Unbalanced.InclusionExclusion
import Sechstmoment.Certificate.Kernels.Unbalanced.IntegerMoments
import Sechstmoment.Certificate.Kernels.Unbalanced.PolynomialBridge


namespace Sechstmoment

open scoped BigOperators
open _root_.Sechstmoment.Finite

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

noncomputable def realMinusMaskEvaluator (p q : Fin 5 → ℝ)
    (shift a b c H : ℝ) : ℝ :=
  if H ≤ 0 then 0 else
    ∑ mask : Fin 8, simplexMaskSign mask *
      (if H - simplexMaskShift a b c mask ≤ 0 then 0 else
        ∑ j : Fin 5, minusBoxCoefficient p q shift (minusEvenIndex j) *
          realMomentEval (2 * j.val) mask.val a b c (H - simplexMaskShift a b c mask) /
            (Finite.dminusDenominator : ℝ))

def integerMinusMaskShift (a b c : ℤ) (mask : ℕ) : ℤ :=
  (if Finite.bit mask 0 then a else 0) +
  (if Finite.bit mask 1 then b else 0) +
  (if Finite.bit mask 2 then c else 0)

def integerMinusMaskEvaluator (p q : List ℤ) (t0 a b c H : ℤ) : ℤ :=
  let pq := polyMul (shifted p (-t0) 1) (shifted q t0 1)
  Finite.sum ((List.range 8).map fun mask =>
    let HH := H - integerMinusMaskShift a b c mask
    if HH ≤ 0 then 0 else
      let sign : ℤ := (-1)^((List.range 3).filter (Finite.bit mask)).length
      Finite.sum ((List.range 5).map fun j =>
        sign * coef pq (2*j) * integerMomentEval (2*j) mask a b c HH))

private theorem range_five_sum (f : ℕ → ℝ) :
    ((List.range 5).map f).sum = ∑ j : Fin 5, f j.val := by
  norm_num [List.range_succ, Fin.sum_univ_succ]

private theorem range_eight_sum (f : ℕ → ℝ) :
    ((List.range 8).map f).sum = ∑ j : Fin 8, f j.val := by
  norm_num [List.range_succ, Fin.sum_univ_succ]

private theorem integer_skip_zero (sign coeff moment : ℤ) :
    (if coeff = 0 then 0 else sign * coeff * moment) = sign * coeff * moment := by
  by_cases h : coeff = 0 <;> simp [h]

theorem dminus_eq_integerMinusMaskEvaluator (A B C D : ℕ) (p q : List ℤ) :
    Finite.dminus A B C D p q =
      if A + B + C ≤ D then 0 else
        integerMinusMaskEvaluator p q
          ((Finite.scale - (24 * (A : ℤ) + 24 * B + 24 * C - 24 * D)) / 2)
          (24*A) (24*B) (24*C) (24*(A : ℤ)+24*B+24*C-24*D) := by
  unfold Finite.dminus integerMinusMaskEvaluator
  simp only [integer_skip_zero]
  norm_num [integerMinusMaskShift, integerMomentEval, Finite.sum,
    List.range_succ, coef]

theorem integerMinusMaskShift_normalized (a b c : ℤ) (mask : Fin 8) :
    (integerMinusMaskShift a b c mask.val : ℝ) / (Finite.scale : ℝ) =
      simplexMaskShift ((a : ℝ)/(Finite.scale : ℝ))
        ((b : ℝ)/(Finite.scale : ℝ)) ((c : ℝ)/(Finite.scale : ℝ)) mask := by
  unfold integerMinusMaskShift simplexMaskShift
  simp only [Int.cast_add, Int.cast_ite, Int.cast_zero, add_div]
  split_ifs <;> simp

private theorem integerMinusDegree_normalized (p q : List ℤ) (t0 a b c HH : ℤ)
    (mask : Fin 8) (j : Fin 5) :
    ((coef (polyMul (shifted p (-t0) 1) (shifted q t0 1)) (2*j.val) *
        integerMomentEval (2*j.val) mask.val a b c HH : ℤ) : ℝ) /
        ((Finite.dminusDenominator : ℝ) * (Finite.scale : ℝ)^13) =
      minusBoxCoefficient (fun r => (coef p r.val : ℝ))
        (fun r => (coef q r.val : ℝ)) ((t0 : ℝ)/(Finite.scale : ℝ)) (minusEvenIndex j) *
        realMomentEval (2*j.val) mask.val ((a : ℝ)/(Finite.scale : ℝ))
          ((b : ℝ)/(Finite.scale : ℝ)) ((c : ℝ)/(Finite.scale : ℝ))
          ((HH : ℝ)/(Finite.scale : ℝ)) / (Finite.dminusDenominator : ℝ) := by
  have hk : 2*j.val ∈ [0,2,4,6,8] := by fin_cases j <;> decide
  have hm : mask.val ∈ List.range 8 := List.mem_range.mpr mask.isLt
  have hs : (Finite.scale : ℝ) ≠ 0 := ne_of_gt scale_real_pos
  have hd : (Finite.dminusDenominator : ℝ) ≠ 0 := by
    rw [dminusDenominator_real]
    positivity
  rw [Int.cast_mul, integerMomentEval_cast]
  have hcoef := minus_integer_productCoefficient p q t0 (minusEvenIndex j)
  simp only [minusEvenIndex] at hcoef
  rw [hcoef]
  rw [← realMomentEval_div_scale hk hm (Finite.scale : ℝ) _ _ _ _ hs]
  simp only [minusBoxCoefficient, minusEvenIndex, neg_div]
  have hdeg : 8 - 2*j.val + (2*j.val+5) = 13 := by omega
  have hp : (Finite.scale : ℝ)^13 =
      (Finite.scale : ℝ)^(8-2*j.val) * (Finite.scale : ℝ)^(2*j.val+5) := by
    rw [← pow_add, hdeg]
  rw [hp]
  field_simp

theorem integerMinusMaskEvaluator_normalized (p q : List ℤ) (t0 a b c H : ℤ) :
    (integerMinusMaskEvaluator p q t0 a b c H : ℝ) /
        ((Finite.dminusDenominator : ℝ) * (Finite.scale : ℝ)^13) =
      ∑ mask : Fin 8, simplexMaskSign mask *
        (if (H : ℝ)/(Finite.scale : ℝ) -
          simplexMaskShift ((a : ℝ)/(Finite.scale : ℝ))
            ((b : ℝ)/(Finite.scale : ℝ)) ((c : ℝ)/(Finite.scale : ℝ)) mask ≤ 0 then 0 else
          ∑ j : Fin 5,
            minusBoxCoefficient (fun r => (coef p r.val : ℝ)) (fun r => (coef q r.val : ℝ))
              ((t0 : ℝ)/(Finite.scale : ℝ)) (minusEvenIndex j) *
              realMomentEval (2*j.val) mask.val ((a : ℝ)/(Finite.scale : ℝ))
                ((b : ℝ)/(Finite.scale : ℝ)) ((c : ℝ)/(Finite.scale : ℝ))
                ((H : ℝ)/(Finite.scale : ℝ) - simplexMaskShift ((a : ℝ)/(Finite.scale : ℝ))
                  ((b : ℝ)/(Finite.scale : ℝ)) ((c : ℝ)/(Finite.scale : ℝ)) mask) /
                  (Finite.dminusDenominator : ℝ)) := by
  unfold integerMinusMaskEvaluator
  rw [finite_integer_sum_cast]
  simp only [List.map_map, Function.comp_def]
  rw [range_eight_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro mask hmask
  let HH : ℤ := H-integerMinusMaskShift a b c mask.val
  have hshift : (HH : ℝ)/(Finite.scale : ℝ) = (H : ℝ)/(Finite.scale : ℝ) -
      simplexMaskShift ((a : ℝ)/(Finite.scale : ℝ))
        ((b : ℝ)/(Finite.scale : ℝ)) ((c : ℝ)/(Finite.scale : ℝ)) mask := by
    dsimp [HH]
    rw [Int.cast_sub, sub_div, integerMinusMaskShift_normalized]
  have hcut : HH ≤ 0 ↔ (H : ℝ)/(Finite.scale : ℝ) -
      simplexMaskShift ((a : ℝ)/(Finite.scale : ℝ))
        ((b : ℝ)/(Finite.scale : ℝ)) ((c : ℝ)/(Finite.scale : ℝ)) mask ≤ 0 := by
    rw [← hshift, div_le_iff₀ scale_real_pos, zero_mul]
    norm_cast
  change (((if HH ≤ 0 then 0 else Finite.sum _) : ℤ) : ℝ) / _ = _
  by_cases hHH : HH ≤ 0
  · simp only [hHH, ite_true, Int.cast_zero, zero_div, hcut.mp hHH, mul_zero]
  · rw [ite_eq_right hHH, ite_eq_right (fun h => hHH (hcut.mpr h)), finite_integer_sum_cast]
    simp only [List.map_map, Function.comp_def, Int.cast_mul]
    rw [range_five_sum, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hdegree := integerMinusDegree_normalized p q t0 a b c HH mask j
    simp only [Int.cast_mul] at hdegree
    rw [mul_assoc, mul_div_assoc, hdegree, hshift]
    simp only [simplexMaskSign, Int.cast_pow, Int.cast_neg, Int.cast_one]

theorem dminus_normalized_eq_realMinusMaskEvaluator (A B C D : ℕ) (p q : List ℤ) :
    (Finite.dminus A B C D p q : ℝ) /
        ((Finite.dminusDenominator : ℝ) * (Finite.scale : ℝ)^13) =
      realMinusMaskEvaluator (fun r => (coef p r.val : ℝ)) (fun r => (coef q r.val : ℝ))
        ((1-(realEndpoint A+realEndpoint B+realEndpoint C-realEndpoint D))/2)
        (realEndpoint A) (realEndpoint B) (realEndpoint C)
        (realEndpoint A+realEndpoint B+realEndpoint C-realEndpoint D) := by
  have hbranch : A+B+C ≤ D ↔
      realEndpoint A+realEndpoint B+realEndpoint C-realEndpoint D ≤ 0 := by
    simp only [realEndpoint]
    have hb : (0 : ℝ) < (Finite.base : ℝ) := by norm_num [Finite.base]
    rw [← add_div, ← add_div, ← sub_div, div_le_iff₀ hb, zero_mul]
    rw [sub_nonpos]
    norm_cast
  rw [dminus_eq_integerMinusMaskEvaluator]
  by_cases h : A+B+C ≤ D
  · simp only [h, ite_true, Int.cast_zero, zero_div, realMinusMaskEvaluator,
      hbranch.mp h]
  · rw [ite_eq_right h, integerMinusMaskEvaluator_normalized]
    simp only [realMinusMaskEvaluator, ite_eq_right (fun h' => h (hbranch.mpr h'))]
    rw [denominatorMinus_normalized_shift]
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_add,
      Int.cast_sub, add_div, sub_div, ← realEndpoint_scale]

end Sechstmoment
