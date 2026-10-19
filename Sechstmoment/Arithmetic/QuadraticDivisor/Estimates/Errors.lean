import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Sechstmoment.Arithmetic.QuadraticDivisor.Estimates.BlockTransfer
import Sechstmoment.Arithmetic.QuadraticDivisor.Estimates.Exponents

/-!
The elementary absorption and sublinearity arguments for the additional errors.
The analytic identities and bounds supplying those errors remain separate inputs.
-/

namespace Sechstmoment

open Filter Asymptotics
open scoped Topology BigOperators

/-- The main-term contour error is absorbed by the first rectangular block error. -/
theorem rectangular_contour_coefficient_le {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    (A * B) ^ (1/4:ℝ) * (A ^ (1/2:ℝ) + B ^ (1/2:ℝ)) ≤ 2 * (A * B) := by
  have hQ : 1 ≤ A * B := by nlinarith
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have haq : A ≤ A * B := by nlinarith
  have hbq : B ≤ A * B := by nlinarith
  have ha : A ^ (1/2:ℝ) ≤ (A * B) ^ (3/4:ℝ) :=
    (Real.rpow_le_rpow hA0 haq (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ (by norm_num))
  have hb : B ^ (1/2:ℝ) ≤ (A * B) ^ (3/4:ℝ) :=
    (Real.rpow_le_rpow hB0 hbq (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ (by norm_num))
  calc
    _ ≤ (A * B) ^ (1/4:ℝ) * ((A * B) ^ (3/4:ℝ) + (A * B) ^ (3/4:ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add ha hb) (by positivity)
    _ = 2 * ((A * B) ^ (1/4:ℝ) * (A * B) ^ (3/4:ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add (by positivity : 0 < A * B)]; norm_num

/-- The `H₀²` Poisson error after the same reconstruction factor. -/
theorem rectangular_poisson_back_transfer {T Q X H K : ℝ}
    (hT : 0 < T) (hQ : 0 < Q) (hX : 0 < X) (hH : 0 ≤ H) (hK : 0 < K)
    (hH0 : H ≤ K * Q ^ (1/2:ℝ) * X / T) :
    T / (Q ^ (1/2:ℝ) * X) * H ^ 2 ≤ K ^ 2 * Q ^ (1/2:ℝ) * X / T := by
  have hbound : 0 ≤ K * Q ^ (1/2:ℝ) * X / T := by positivity
  have hp := pow_le_pow_left₀ hH hH0 2
  have hw : 0 ≤ T / (Q ^ (1/2:ℝ) * X) := by positivity
  have hq : 0 < Q ^ (1/2:ℝ) := Real.rpow_pos_of_pos hQ _
  calc
    _ ≤ T / (Q ^ (1/2:ℝ) * X) * (K * Q ^ (1/2:ℝ) * X / T) ^ 2 :=
      mul_le_mul_of_nonneg_left hp hw
    _ = _ := by field_simp

/-- Padding the diagonal term to length `B` still gives a strictly sublinear power. -/
theorem rectangular_auxiliary_exponents {a b : ℝ} (ha : 0 ≤ a) (_hab : a ≤ b)
    (h : 3*a + 5*b < 2) :
    1/2 + b/2 + rectangularSlack a b < 1 ∧
      b + rectangularSlack a b < 1 := by
  dsimp [rectangularSlack]
  constructor <;> linarith

/-- The actual diagonal and phase error powers, with any fixed logarithmic loss, are `o(T)`. -/
theorem rectangular_auxiliary_errors_isLittleO {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : 3*a + 5*b < 2) (n : ℕ) :
    (fun T : ℝ => (Real.log T)^n *
      (T ^ (1/2+b/2+rectangularSlack a b) + T ^ (b+rectangularSlack a b))) =o[atTop]
        (fun T : ℝ => T) := by
  obtain ⟨hd, hp⟩ := rectangular_auxiliary_exponents ha hab h
  simpa only [mul_add] using (polylog_mul_rpow_isLittleO_id n hd).add
    (polylog_mul_rpow_isLittleO_id n hp)

/-- The minimum in the phase error can be estimated by two reciprocal sums. -/
theorem rectangular_min_reciprocal_le {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (min u v)⁻¹ ≤ u⁻¹ + v⁻¹ := by
  rcases le_total u v with huv | hvu
  · rw [min_eq_left huv]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hv.le)
  · rw [min_eq_right hvu]
    exact le_add_of_nonneg_left (inv_nonneg.mpr hu.le)

/-- A logarithmic counting bound for the phase error, valid for rectangular lengths. -/
theorem rectangular_min_reciprocal_sum_le (A B : ℕ) (hA : 1 ≤ A) (hab : A ≤ B) :
    (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 B,
      (min (u:ℝ) (v:ℝ))⁻¹) ≤ 2 * (B:ℝ) * (1 + Real.log B) := by
  have hB : 1 ≤ B := hA.trans hab
  have hsumA : (∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹) ≤ 1 + Real.log B := by
    have ha := harmonic_le_one_add_log A
    have hlog : Real.log (A:ℝ) ≤ Real.log (B:ℝ) :=
      Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hA) (by exact_mod_cast hab)
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      ha.trans (add_le_add_right hlog 1)
  have hsumB : (∑ v ∈ Finset.Icc 1 B, (v:ℝ)⁻¹) ≤ 1 + Real.log B := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      harmonic_le_one_add_log B
  have hpos : 0 ≤ 1 + Real.log (B:ℝ) := by
    have := Real.log_nonneg (show (1:ℝ) ≤ B by exact_mod_cast hB)
    linarith
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 B, ((u:ℝ)⁻¹ + (v:ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      exact rectangular_min_reciprocal_le
        (by exact_mod_cast lt_of_lt_of_le (show (0:ℕ) < 1 by decide) (Finset.mem_Icc.mp hu).1)
        (by exact_mod_cast lt_of_lt_of_le (show (0:ℕ) < 1 by decide) (Finset.mem_Icc.mp hv).1)
    _ = (B:ℝ) * (∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹) +
        (A:ℝ) * (∑ v ∈ Finset.Icc 1 B, (v:ℝ)⁻¹) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        nsmul_eq_mul, Finset.mul_sum]
    _ ≤ (B:ℝ) * (1 + Real.log B) + (A:ℝ) * (1 + Real.log B) :=
      add_le_add (mul_le_mul_of_nonneg_left hsumA (by positivity))
        (mul_le_mul_of_nonneg_left hsumB (by positivity))
    _ ≤ (B:ℝ) * (1 + Real.log B) + (B:ℝ) * (1 + Real.log B) := by
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hpos
    _ = _ := by ring

end Sechstmoment
