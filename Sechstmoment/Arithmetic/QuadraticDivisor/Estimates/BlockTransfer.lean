import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic


namespace Sechstmoment

noncomputable def rectangularQuadraticMajorant (A B X H : ℝ) : ℝ :=
  (A * B * X ^ 2 * H ^ 2) ^ (1 / 4 : ℝ) *
    (A * B + H ^ (1 / 4 : ℝ) * (A * B) ^ (1 / 8 : ℝ) *
      max A B ^ (1 / 4 : ℝ) * (A * B * X ^ 2) ^ (1 / 8 : ℝ))

noncomputable def rectangularExpandedMajorant (Q P X H : ℝ) : ℝ :=
  H ^ (1 / 2 : ℝ) * (Q ^ (5 / 4 : ℝ) * X ^ (1 / 2 : ℝ)) +
    H ^ (3 / 4 : ℝ) * (Q ^ (1 / 2 : ℝ) * P ^ (1 / 4 : ℝ) * X ^ (3 / 4 : ℝ))

theorem rectangular_oriented_coefficient_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A ^ (3 / 8 : ℝ) * B ^ (1 / 8 : ℝ) ≤
      (A * B) ^ (1 / 8 : ℝ) * max A B ^ (1 / 4 : ℝ) := by
  rw [Real.mul_rpow hA hB]
  have h := Real.rpow_le_rpow hA (le_max_left A B) (by norm_num : (0 : ℝ) ≤ 1/4)
  have heq : A ^ (3/8:ℝ) = A ^ (1/8:ℝ) * A ^ (1/4:ℝ) := by
    rw [← Real.rpow_add_of_nonneg hA (by norm_num : (0:ℝ) ≤ 1/8)
      (by norm_num : (0:ℝ) ≤ 1/4)]
    norm_num
  rw [heq]
  calc
    A ^ (1/8:ℝ) * A ^ (1/4:ℝ) * B ^ (1/8:ℝ) =
      (A ^ (1/8:ℝ) * B ^ (1/8:ℝ)) * A ^ (1/4:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

theorem rectangular_small_d_coefficient_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A * B) ^ (1/4:ℝ) ≤ (A * B) ^ (1/8:ℝ) * max A B ^ (1/4:ℝ) := by
  have hp : 0 ≤ max A B := le_max_of_le_left hA
  have hq : A * B ≤ (max A B) ^ 2 := by
    calc
      _ ≤ max A B * max A B := mul_le_mul (le_max_left _ _) (le_max_right _ _) hB hp
      _ = _ := by ring
  have he := Real.rpow_le_rpow (mul_nonneg hA hB) hq (by norm_num : (0:ℝ) ≤ 1/8)
  rw [← Real.rpow_natCast_mul hp] at he
  norm_num at he
  calc
    _ = (A * B) ^ (1/8:ℝ) * (A * B) ^ (1/8:ℝ) := by
      rw [← Real.rpow_add_of_nonneg (mul_nonneg hA hB)
        (by norm_num : (0:ℝ) ≤ 1/8) (by norm_num : (0:ℝ) ≤ 1/8)]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

theorem rectangular_quadratic_majorant_expand {A B X H : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hX : 0 < X) (hH : 0 < H) :
    rectangularQuadraticMajorant A B X H =
      rectangularExpandedMajorant (A * B) (max A B) X H := by
  have hQ : 0 < A * B := mul_pos hA hB
  have hP : 0 < max A B := lt_of_lt_of_le hA (le_max_left _ _)
  dsimp [rectangularQuadraticMajorant, rectangularExpandedMajorant]
  rw [Real.mul_rpow (by positivity : 0 ≤ A * B * X ^ 2) (by positivity : 0 ≤ H ^ 2),
    Real.mul_rpow hQ.le (by positivity : 0 ≤ X ^ 2),
    Real.mul_rpow hQ.le (by positivity : 0 ≤ X ^ 2)]
  rw [← Real.rpow_natCast_mul hH.le, ← Real.rpow_natCast_mul hX.le,
    ← Real.rpow_natCast_mul hX.le]
  norm_num
  simp only [Real.rpow_def_of_pos hQ, Real.rpow_def_of_pos hP,
    Real.rpow_def_of_pos hX, Real.rpow_def_of_pos hH]
  rw [mul_add]
  congr 1
  · rw [show A * B = Real.exp (Real.log (A * B)) from (Real.exp_log hQ).symm]
    simp only [← Real.exp_add]
    congr 1
    simp only [Real.log_exp]
    ring
  · simp only [← Real.exp_add]
    congr 1
    ring

private theorem rectangular_first_transfer_identity {T Q X K : ℝ}
    (hT : 0 < T) (hQ : 0 < Q) (hX : 0 < X) (hK : 0 < K) :
    T / (Q ^ (1/2:ℝ) * X) * (K * Q ^ (1/2:ℝ) * X / T) ^ (1/2:ℝ) *
        (Q ^ (5/4:ℝ) * X ^ (1/2:ℝ)) =
      K ^ (1/2:ℝ) * T ^ (1/2:ℝ) * Q := by
  rw [Real.div_rpow (by positivity) hT.le,
    Real.mul_rpow (by positivity) hX.le, Real.mul_rpow hK.le (by positivity),
    ← Real.rpow_mul hQ.le]
  norm_num
  simp only [Real.rpow_def_of_pos hQ, Real.rpow_def_of_pos hX,
    Real.rpow_def_of_pos hT, Real.rpow_def_of_pos hK]
  rw [show T = Real.exp (Real.log T) from (Real.exp_log hT).symm,
    show X = Real.exp (Real.log X) from (Real.exp_log hX).symm,
    show Q = Real.exp (Real.log Q) from (Real.exp_log hQ).symm]
  simp only [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  simp only [Real.log_exp]
  ring

private theorem rectangular_second_transfer_identity {T Q P X K : ℝ}
    (hT : 0 < T) (hQ : 0 < Q) (hP : 0 < P) (hX : 0 < X) (hK : 0 < K) :
    T / (Q ^ (1/2:ℝ) * X) * (K * Q ^ (1/2:ℝ) * X / T) ^ (3/4:ℝ) *
        (Q ^ (1/2:ℝ) * P ^ (1/4:ℝ) * X ^ (3/4:ℝ)) =
      K ^ (3/4:ℝ) * T ^ (1/4:ℝ) * Q ^ (3/8:ℝ) * P ^ (1/4:ℝ) * X ^ (1/2:ℝ) := by
  rw [Real.div_rpow (by positivity) hT.le,
    Real.mul_rpow (by positivity) hX.le, Real.mul_rpow hK.le (by positivity),
    ← Real.rpow_mul hQ.le]
  norm_num
  simp only [Real.rpow_def_of_pos hQ, Real.rpow_def_of_pos hP,
    Real.rpow_def_of_pos hX, Real.rpow_def_of_pos hT, Real.rpow_def_of_pos hK]
  rw [show T = Real.exp (Real.log T) from (Real.exp_log hT).symm,
    show X = Real.exp (Real.log X) from (Real.exp_log hX).symm]
  simp only [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  simp only [Real.log_exp]
  ring

theorem rectangular_H0_back_transfer {T A B X H K : ℝ}
    (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) (hX : 0 < X) (hH : 0 < H)
    (hK : 0 < K) (hH0 : H ≤ K * (A * B) ^ (1/2:ℝ) * X / T) :
    T / ((A * B) ^ (1/2:ℝ) * X) * rectangularQuadraticMajorant A B X H ≤
      K ^ (1/2:ℝ) * T ^ (1/2:ℝ) * (A * B) +
        K ^ (3/4:ℝ) * T ^ (1/4:ℝ) * (A * B) ^ (3/8:ℝ) *
          max A B ^ (1/4:ℝ) * X ^ (1/2:ℝ) := by
  have hQ : 0 < A * B := mul_pos hA hB
  have hP : 0 < max A B := lt_of_lt_of_le hA (le_max_left _ _)
  rw [rectangular_quadratic_majorant_expand hA hB hX hH]
  dsimp [rectangularExpandedMajorant]
  rw [mul_add]
  apply add_le_add
  · have hp := Real.rpow_le_rpow hH.le hH0 (by norm_num : (0:ℝ) ≤ 1/2)
    calc
      _ ≤ T / ((A * B) ^ (1/2:ℝ) * X) *
        ((K * (A * B) ^ (1/2:ℝ) * X / T) ^ (1/2:ℝ) *
          ((A * B) ^ (5/4:ℝ) * X ^ (1/2:ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)
      _ = _ := by simpa only [mul_assoc] using rectangular_first_transfer_identity hT hQ hX hK
  · have hp := Real.rpow_le_rpow hH.le hH0 (by norm_num : (0:ℝ) ≤ 3/4)
    calc
      _ ≤ T / ((A * B) ^ (1/2:ℝ) * X) *
        ((K * (A * B) ^ (1/2:ℝ) * X / T) ^ (3/4:ℝ) *
          ((A * B) ^ (1/2:ℝ) * max A B ^ (1/4:ℝ) * X ^ (3/4:ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)
      _ = _ := by simpa only [mul_assoc] using rectangular_second_transfer_identity hT hQ hP hX hK

theorem rectangular_endpoint_coefficient_le {A₀ B₀ A B : ℝ}
    (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀) (hA : 0 ≤ A)
    (hAend : A₀ ≤ A) (hBend : B₀ ≤ B) (hab : A ≤ B) :
    (A₀ * B₀) ^ (3/8:ℝ) * max A₀ B₀ ^ (1/4:ℝ) ≤
      A ^ (3/8:ℝ) * B ^ (5/8:ℝ) := by
  have hB : 0 ≤ B := hA.trans hab
  have hQ : A₀ * B₀ ≤ A * B := mul_le_mul hAend hBend hB₀ hA
  have hP : max A₀ B₀ ≤ B := max_le (hAend.trans hab) hBend
  calc
    _ ≤ (A * B) ^ (3/8:ℝ) * B ^ (1/4:ℝ) :=
      mul_le_mul (Real.rpow_le_rpow (by positivity) hQ (by norm_num))
        (Real.rpow_le_rpow (le_max_of_le_left hA₀) hP (by norm_num))
        (by positivity) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hA hB]
      rw [mul_assoc, ← Real.rpow_add_of_nonneg hB (by norm_num : (0:ℝ) ≤ 3/8)
        (by norm_num : (0:ℝ) ≤ 1/4)]
      norm_num

theorem rectangular_error_back_transfer {T A B X H K C : ℝ} (E : ℂ)
    (hT : 0 < T) (hA : 0 < A) (hB : 0 < B) (hX : 0 < X) (hH : 0 < H)
    (hK : 0 < K) (hC : 0 ≤ C)
    (hH0 : H ≤ K * (A * B) ^ (1/2:ℝ) * X / T)
    (hE : ‖E‖ ≤ C * rectangularQuadraticMajorant A B X H) :
    ‖((T / ((A * B) ^ (1/2:ℝ) * X) : ℝ) : ℂ) * E‖ ≤ C *
      (K ^ (1/2:ℝ) * T ^ (1/2:ℝ) * (A * B) +
        K ^ (3/4:ℝ) * T ^ (1/4:ℝ) * (A * B) ^ (3/8:ℝ) *
          max A B ^ (1/4:ℝ) * X ^ (1/2:ℝ)) := by
  have hw : 0 ≤ T / ((A * B) ^ (1/2:ℝ) * X) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
  calc
    _ ≤ T / ((A * B) ^ (1/2:ℝ) * X) *
        (C * rectangularQuadraticMajorant A B X H) := mul_le_mul_of_nonneg_left hE hw
    _ = C * (T / ((A * B) ^ (1/2:ℝ) * X) *
        rectangularQuadraticMajorant A B X H) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (rectangular_H0_back_transfer hT hA hB hX hH hK hH0) hC

theorem rectangular_error_endpoint {T A₀ B₀ A B X H K C L Y : ℝ} (E : ℂ)
    (hT : 0 < T) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) (hX : 0 < X) (hH : 0 < H)
    (hK : 0 < K) (hC : 0 ≤ C) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (hAend : A₀ ≤ A) (hBend : B₀ ≤ B) (hab : A ≤ B) (hXend : X ≤ L * Y)
    (hH0 : H ≤ K * (A₀ * B₀) ^ (1/2:ℝ) * X / T)
    (hE : ‖E‖ ≤ C * rectangularQuadraticMajorant A₀ B₀ X H) :
    ‖((T / ((A₀ * B₀) ^ (1/2:ℝ) * X) : ℝ) : ℂ) * E‖ ≤ C *
      (K ^ (1/2:ℝ) * T ^ (1/2:ℝ) * (A * B) +
        K ^ (3/4:ℝ) * T ^ (1/4:ℝ) * A ^ (3/8:ℝ) * B ^ (5/8:ℝ) *
          L ^ (1/2:ℝ) * Y ^ (1/2:ℝ)) := by
  have hA : 0 ≤ A := hA₀.le.trans hAend
  have hB : 0 ≤ B := hB₀.le.trans hBend
  refine (rectangular_error_back_transfer E hT hA₀ hB₀ hX hH hK hC hH0 hE).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (mul_le_mul hAend hBend hB₀.le hA) (by positivity)
  · have he := rectangular_endpoint_coefficient_le hA₀.le hB₀.le hA hAend hBend hab
    have hx := Real.rpow_le_rpow hX.le hXend (by norm_num : (0:ℝ) ≤ 1/2)
    rw [Real.mul_rpow hL hY] at hx
    calc
      _ = (K ^ (3/4:ℝ) * T ^ (1/4:ℝ)) *
        ((A₀ * B₀) ^ (3/8:ℝ) * max A₀ B₀ ^ (1/4:ℝ)) * X ^ (1/2:ℝ) := by ring
      _ ≤ (K ^ (3/4:ℝ) * T ^ (1/4:ℝ)) *
        (A ^ (3/8:ℝ) * B ^ (5/8:ℝ)) * (L ^ (1/2:ℝ) * Y ^ (1/2:ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) hx (by positivity) (by positivity)
      _ = _ := by ring

theorem rectangular_first_power_normalize {T K : ℝ} (hT : 0 < T) (hK : 0 < K)
    (a b ε : ℝ) :
    T ^ ε * ((K * T ^ ε) ^ (1/2:ℝ) * T ^ (1/2:ℝ) * (T ^ a * T ^ b)) =
      K ^ (1/2:ℝ) * T ^ (1/2 + a + b + 3*ε/2) := by
  rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul hT.le]
  simp only [Real.rpow_def_of_pos hT, Real.rpow_def_of_pos hK, ← Real.exp_add]
  congr 1
  ring

theorem rectangular_second_power_normalize {T K : ℝ} (hT : 0 < T) (hK : 0 < K)
    (a b ε : ℝ) :
    T ^ ε * ((K * T ^ ε) ^ (3/4:ℝ) * T ^ (1/4:ℝ) *
      (T ^ a) ^ (3/8:ℝ) * (T ^ b) ^ (5/8:ℝ) * (T ^ (1+ε)) ^ (1/2:ℝ)) =
      K ^ (3/4:ℝ) * T ^ (3/4 + 3*a/8 + 5*b/8 + 9*ε/4) := by
  rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul hT.le,
    ← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le]
  simp only [Real.rpow_def_of_pos hT, Real.rpow_def_of_pos hK, ← Real.exp_add]
  congr 1
  ring

theorem rectangular_block_error_bound {T A₀ B₀ X H C K L a b ε : ℝ} (E : ℂ)
    (hT : 1 ≤ T) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) (hX : 0 < X) (hH : 0 < H)
    (hC : 0 ≤ C) (hK : 0 < K) (hL : 0 ≤ L) (hab : a ≤ b)
    (hAend : A₀ ≤ T ^ a) (hBend : B₀ ≤ T ^ b)
    (hXend : X ≤ L * T ^ (1+ε))
    (hH0 : H ≤ (K * T ^ ε) * (A₀ * B₀) ^ (1/2:ℝ) * X / T)
    (hE : ‖E‖ ≤ (C * T ^ ε) * rectangularQuadraticMajorant A₀ B₀ X H) :
    ‖((T / ((A₀ * B₀) ^ (1/2:ℝ) * X) : ℝ) : ℂ) * E‖ ≤
      (C * K ^ (1/2:ℝ)) * T ^ (1/2 + a + b + 3*ε/2) +
        (C * K ^ (3/4:ℝ) * L ^ (1/2:ℝ)) *
          T ^ (3/4 + 3*a/8 + 5*b/8 + 9*ε/4) := by
  have ht : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hT
  have hp : T ^ a ≤ T ^ b := Real.rpow_le_rpow_of_exponent_le hT hab
  have he := rectangular_error_endpoint E ht hA₀ hB₀ hX hH
    (mul_pos hK (Real.rpow_pos_of_pos ht _)) (mul_nonneg hC (by positivity))
    hL (Real.rpow_nonneg ht.le _) hAend hBend hp hXend hH0 hE
  refine he.trans_eq ?_
  rw [mul_add]
  congr 1
  · calc
      _ = C * (T ^ ε * ((K * T ^ ε) ^ (1/2:ℝ) * T ^ (1/2:ℝ) * (T ^ a * T ^ b))) := by ring
      _ = _ := by rw [rectangular_first_power_normalize ht hK]; ring
  · calc
      _ = (C * L ^ (1/2:ℝ)) * (T ^ ε * ((K * T ^ ε) ^ (3/4:ℝ) * T ^ (1/4:ℝ) *
        (T ^ a) ^ (3/8:ℝ) * (T ^ b) ^ (5/8:ℝ) * (T ^ (1+ε)) ^ (1/2:ℝ))) := by ring
      _ = _ := by rw [rectangular_second_power_normalize ht hK]; ring

end Sechstmoment
