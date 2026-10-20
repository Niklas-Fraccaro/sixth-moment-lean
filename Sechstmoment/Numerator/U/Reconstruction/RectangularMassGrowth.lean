import Mathlib.Tactic
import Sechstmoment.Arithmetic.QuadraticDivisor.Estimates.SourceAdapter


namespace Sechstmoment

theorem rectangular_mass_growth {T A B X H K L a b s : ℝ}
    (hT : 1 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : 0 ≤ X) (hH : 0 ≤ H)
    (_hK : 0 ≤ K) (_hL : 0 ≤ L) (hab : a+b ≤ 1/2) (hs : s ≤ 1/6)
    (hAend : A ≤ T^a) (hBend : B ≤ T^b) (hXend : X ≤ L*T^(1+s))
    (hH0 : H ≤ (K*T^s)*(A*B)^(1/2:ℝ)*X/T) :
    A*B*X^2 ≤ (L^2+K^2*L^4)*T^4 ∧
      A*B*X^2*H^2 ≤ (L^2+K^2*L^4)*T^4 := by
  have ht : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hT
  have hQ : A*B ≤ T^(a+b) := by
    rw [Real.rpow_add ht]
    exact mul_le_mul hAend hBend hB (Real.rpow_nonneg ht.le _)
  have hT4 : T^(4:ℕ) = T^(4:ℝ) := (Real.rpow_natCast T 4).symm
  have hx₂ := pow_le_pow_left₀ hX hXend 2
  have hx₄ := pow_le_pow_left₀ hX hXend 4
  have hq₂ := pow_le_pow_left₀ (mul_nonneg hA hB) hQ 2
  have hh₂ := pow_le_pow_left₀ hH hH0 2
  have hroot : ((A*B)^(1/2:ℝ))^2 = A*B := by
    rw [← Real.rpow_mul_natCast (mul_nonneg hA hB)]
    norm_num
  have hm : A*B*X^2 ≤ L^2*T^(a+b+2+2*s) := by
    calc
      _ ≤ T^(a+b)*(L*T^(1+s))^2 := mul_le_mul hQ hx₂ (sq_nonneg X) (by positivity)
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast ht.le]
        calc
          _ = L^2*(T^(a+b)*T^((1+s)*2)) := by ring
          _ = _ := by rw [← Real.rpow_add ht]; congr 1; ring
  have hmH : A*B*X^2*H^2 ≤ K^2*L^4*T^(2*(a+b)+2+6*s) := by
    have hfirst : A*B*X^2*H^2 ≤ K^2*T^(2*s)*(A*B)^2*X^4/T^2 := by
      calc
        _ ≤ A*B*X^2*((K*T^s)*(A*B)^(1/2:ℝ)*X/T)^2 :=
          mul_le_mul_of_nonneg_left hh₂ (by positivity)
        _ = _ := by
          rw [div_pow, mul_pow, mul_pow, mul_pow, hroot]
          rw [← Real.rpow_mul_natCast ht.le]
          field_simp
          ring
    refine hfirst.trans ?_
    calc
      _ ≤ K^2*T^(2*s)*(T^(a+b))^2*(L*T^(1+s))^4/T^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg T)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hq₂ (by positivity)) hx₄ (by positivity) (by positivity)
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast ht.le, ← Real.rpow_mul_natCast ht.le]
        have heq : T^(2*s)*T^((a+b)*2)*T^((1+s)*4)/T^2 =
            T^(2*(a+b)+2+6*s) := by
          rw [← Real.rpow_add ht, ← Real.rpow_add ht,
            ← Real.rpow_natCast T 2, ← Real.rpow_sub ht]
          congr 1
          ring
        calc
          _ = K^2*L^4*(T^(2*s)*T^((a+b)*2)*T^((1+s)*4)/T^2) := by ring
          _ = _ := by rw [heq]
  constructor
  · calc
      _ ≤ L^2*T^(4:ℝ) := hm.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hT (by linarith)) (sq_nonneg L))
      _ ≤ (L^2+K^2*L^4)*T^(4:ℝ) := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (by positivity)) (by positivity)
      _ = _ := by rw [hT4]
  · calc
      _ ≤ K^2*L^4*T^(4:ℝ) := hmH.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hT (by linarith)) (by positivity))
      _ ≤ (L^2+K^2*L^4)*T^(4:ℝ) := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (sq_nonneg L)) (by positivity)
      _ = _ := by rw [hT4]

end Sechstmoment
