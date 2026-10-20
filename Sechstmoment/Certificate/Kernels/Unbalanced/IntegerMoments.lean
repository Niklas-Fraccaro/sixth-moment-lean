import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Sechstmoment.Certificate.Kernels.Balanced.IntegerNormalization


namespace Sechstmoment
open _root_.Sechstmoment.Finite

noncomputable def realMomentEval (k mask : ℕ) (a b c H : ℝ) : ℝ :=
  ((momentTerms k mask).map fun tr =>
    (tr.value : ℝ) * a^tr.i * b^tr.j * c^tr.l * H^tr.h).sum

def integerMomentEval (k mask : ℕ) (A B C HH : ℤ) : ℤ :=
  Finite.sum ((momentTerms k mask).map fun tr =>
    tr.value * A^tr.i * B^tr.j * C^tr.l * HH^tr.h)

theorem finite_integer_sum_cast (xs : List ℤ) :
    (Finite.sum xs : ℝ) = (xs.map fun (x : ℤ) => (x : ℝ)).sum := by
  rw [show Finite.sum xs = xs.sum from List.sum_eq_foldl.symm]
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem integerMomentEval_cast (k mask : ℕ) (A B C HH : ℤ) :
    (integerMomentEval k mask A B C HH : ℝ) =
      realMomentEval k mask (A : ℝ) (B : ℝ) (C : ℝ) (HH : ℝ) := by
  unfold integerMomentEval
  rw [finite_integer_sum_cast]
  simp only [realMomentEval, List.map_map, Function.comp_def, Int.cast_mul, Int.cast_pow]

theorem realMomentEval_homogeneous {k mask : ℕ}
    (hk : k ∈ [0,2,4,6,8]) (hm : mask ∈ List.range 8) (s a b c H : ℝ) :
    realMomentEval k mask (s*a) (s*b) (s*c) (s*H) =
      s^(k+5) * realMomentEval k mask a b c H := by
  unfold realMomentEval
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro tr htr
  have hd := moment_terms_degrees_exact k hk mask hm tr htr
  calc
    (tr.value : ℝ)*(s*a)^tr.i*(s*b)^tr.j*(s*c)^tr.l*(s*H)^tr.h =
        s^(tr.i+tr.j+tr.l+tr.h)*((tr.value : ℝ)*a^tr.i*b^tr.j*c^tr.l*H^tr.h) := by
      simp only [mul_pow, pow_add]
      ring
    _ = _ := by rw [hd]

theorem momentTerm_normalized_coefficient {k mask : ℕ}
    (hk : k ∈ [0,2,4,6,8]) (hm : mask ∈ List.range 8)
    (tr : Finite.MomentTerm) (htr : tr ∈ Finite.momentTerms k mask) :
    (tr.value : ℝ) / (256 * (Nat.factorial 13 : ℝ)) =
      (Nat.factorial k : ℝ) /
        ((2 : ℝ)^k * (Nat.factorial tr.i : ℝ) * (Nat.factorial tr.j : ℝ) *
          (Nat.factorial tr.l : ℝ) * (Nat.factorial tr.h : ℝ)) := by
  have hexact := Finite.moment_terms_divisions_exact k hk mask hm tr htr
  simp only [Finite.factorial_eq_natFactorial] at hexact
  have hcast :
      (Nat.factorial tr.i : ℝ) * (Nat.factorial tr.j : ℝ) *
        (Nat.factorial tr.l : ℝ) * (Nat.factorial tr.h : ℝ) * (tr.value : ℝ) =
      (Nat.factorial k : ℝ) * (2 : ℝ)^(8-k) * (Nat.factorial 13 : ℝ) := by
    exact_mod_cast hexact
  have hpow : (2 : ℝ)^k * (2 : ℝ)^(8-k) = 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> norm_num
  apply (div_eq_div_iff
    (by positivity : (256 : ℝ) * (Nat.factorial 13 : ℝ) ≠ 0)
    (by positivity :
      (2 : ℝ)^k * (Nat.factorial tr.i : ℝ) * (Nat.factorial tr.j : ℝ) *
        (Nat.factorial tr.l : ℝ) * (Nat.factorial tr.h : ℝ) ≠ 0)).2
  calc
    (tr.value : ℝ) * ((2 : ℝ)^k * (Nat.factorial tr.i : ℝ) *
        (Nat.factorial tr.j : ℝ) * (Nat.factorial tr.l : ℝ) *
        (Nat.factorial tr.h : ℝ)) =
      (2 : ℝ)^k * ((Nat.factorial tr.i : ℝ) * (Nat.factorial tr.j : ℝ) *
        (Nat.factorial tr.l : ℝ) * (Nat.factorial tr.h : ℝ) *
        (tr.value : ℝ)) := by ring
    _ = (2 : ℝ)^k * ((Nat.factorial k : ℝ) * (2 : ℝ)^(8-k) *
        (Nat.factorial 13 : ℝ)) := by rw [hcast]
    _ = ((Nat.factorial k : ℝ) * (Nat.factorial 13 : ℝ)) *
        ((2 : ℝ)^k * (2 : ℝ)^(8-k)) := by ring
    _ = (Nat.factorial k : ℝ) * (256 * (Nat.factorial 13 : ℝ)) := by
      rw [hpow]
      ring

theorem realMomentEval_normalized {k mask : ℕ}
    (hk : k ∈ [0,2,4,6,8]) (hm : mask ∈ List.range 8) (a b c H : ℝ) :
    realMomentEval k mask a b c H / (256 * (Nat.factorial 13 : ℝ)) =
      ((momentTerms k mask).map fun tr =>
        (Nat.factorial k : ℝ) * a^tr.i * b^tr.j * c^tr.l * H^tr.h /
          ((2 : ℝ)^k * (Nat.factorial tr.i : ℝ) * (Nat.factorial tr.j : ℝ) *
            (Nat.factorial tr.l : ℝ) * (Nat.factorial tr.h : ℝ))).sum := by
  unfold realMomentEval
  rw [div_eq_mul_inv, ← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro tr htr
  calc
    ((tr.value : ℝ) * a^tr.i * b^tr.j * c^tr.l * H^tr.h) *
        (256 * (Nat.factorial 13 : ℝ))⁻¹ =
      ((tr.value : ℝ) / (256 * (Nat.factorial 13 : ℝ))) *
        a^tr.i * b^tr.j * c^tr.l * H^tr.h := by ring
    _ = ((Nat.factorial k : ℝ) /
        ((2 : ℝ)^k * (Nat.factorial tr.i : ℝ) * (Nat.factorial tr.j : ℝ) *
          (Nat.factorial tr.l : ℝ) * (Nat.factorial tr.h : ℝ))) *
        a^tr.i * b^tr.j * c^tr.l * H^tr.h := by
      rw [momentTerm_normalized_coefficient hk hm tr htr]
    _ = _ := by ring

theorem realMomentEval_div_scale {k mask : ℕ}
    (hk : k ∈ [0,2,4,6,8]) (hm : mask ∈ List.range 8)
    (s a b c H : ℝ) (hs : s ≠ 0) :
    realMomentEval k mask a b c H / s^(k+5) =
      realMomentEval k mask (a/s) (b/s) (c/s) (H/s) := by
  have hh := realMomentEval_homogeneous hk hm s (a/s) (b/s) (c/s) (H/s)
  simp only [mul_div_cancel₀ _ hs] at hh
  rw [hh, mul_div_cancel_left₀ _ (pow_ne_zero _ hs)]

theorem integerMomentEval_scale_bridge {k mask : ℕ}
    (hk : k ∈ [0,2,4,6,8]) (hm : mask ∈ List.range 8) (A B C HH : ℤ) :
    (integerMomentEval k mask (24*A) (24*B) (24*C) HH : ℝ) /
        (256 * (Nat.factorial 13 : ℝ) * (Finite.scale : ℝ)^(k+5)) =
      realMomentEval k mask (24*(A : ℝ)/(Finite.scale : ℝ))
        (24*(B : ℝ)/(Finite.scale : ℝ)) (24*(C : ℝ)/(Finite.scale : ℝ))
        ((HH : ℝ)/(Finite.scale : ℝ)) / (256 * (Nat.factorial 13 : ℝ)) := by
  have hs : (Finite.scale : ℝ) ≠ 0 := by norm_num [Finite.scale, Finite.base]
  rw [integerMomentEval_cast]
  simp only [Int.cast_mul, Int.cast_ofNat]
  rw [mul_comm (256 * (Nat.factorial 13 : ℝ)), ← div_div]
  rw [realMomentEval_div_scale hk hm _ _ _ _ _ hs]

theorem dminusDenominator_real :
    (Finite.dminusDenominator : ℝ) = 256 * (Nat.factorial 13 : ℝ) := by
  norm_num [Finite.dminusDenominator, factorial_eq_natFactorial]

theorem integerMomentEval_normalized_exact {k mask : ℕ}
    (hk : k ∈ [0,2,4,6,8]) (hm : mask < 8) (A B C HH : ℤ) :
    (integerMomentEval k mask (24*A) (24*B) (24*C) HH : ℝ) /
        ((Finite.dminusDenominator : ℝ) * (Finite.scale : ℝ)^(k+5)) =
      ((momentTerms k mask).map fun tr =>
        (Nat.factorial k : ℝ) * (24*(A : ℝ)/(Finite.scale : ℝ))^tr.i *
          (24*(B : ℝ)/(Finite.scale : ℝ))^tr.j *
          (24*(C : ℝ)/(Finite.scale : ℝ))^tr.l *
          ((HH : ℝ)/(Finite.scale : ℝ))^tr.h /
          ((2 : ℝ)^k * (Nat.factorial tr.i : ℝ) * (Nat.factorial tr.j : ℝ) *
            (Nat.factorial tr.l : ℝ) * (Nat.factorial tr.h : ℝ))).sum := by
  rw [dminusDenominator_real,
    integerMomentEval_scale_bridge hk (List.mem_range.mpr hm),
    realMomentEval_normalized hk (List.mem_range.mpr hm)]

end Sechstmoment
