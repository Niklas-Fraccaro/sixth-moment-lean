import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Sechstmoment

open MeasureTheory

theorem beta_nat_complex (i j : ℕ) :
    Complex.betaIntegral ((i : ℂ)+1) ((j : ℂ)+1) =
      (Nat.factorial i : ℂ) * Nat.factorial j / Nat.factorial (i+j+1) := by
  have hi : 0 < ((i : ℂ)+1).re := by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity
  have hj : 0 < ((j : ℂ)+1).re := by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity
  have hs : (i : ℂ)+1+((j : ℂ)+1) = ((i+j+1 : ℕ) : ℂ)+1 := by push_cast; ring
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hi hj, hs,
    Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial]

/-- The beta moment formula used for the polynomial profile masses. -/
theorem beta_nat_integral (i j : ℕ) :
    (∫ x in (0 : ℝ)..1, x^i*(1-x)^j) =
      (Nat.factorial i : ℝ) * Nat.factorial j / Nat.factorial (i+j+1) := by
  apply Complex.ofReal_injective
  have hb := beta_nat_complex i j
  simp only [Complex.betaIntegral, add_sub_cancel_right, Complex.cpow_natCast] at hb
  simp only [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, intervalIntegral.integral_ofReal] at hb
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast] using hb

theorem beta_nat_scaled {H : ℝ} (hH : 0 ≤ H) (i j : ℕ) :
    (∫ x in (0 : ℝ)..H, x^i*(H-x)^j) =
      (Nat.factorial i : ℝ) * Nat.factorial j / Nat.factorial (i+j+1) * H^(i+j+1) := by
  by_cases hz : H = 0
  · subst H
    simp
  have hp : 0 < H := lt_of_le_of_ne hH (Ne.symm hz)
  apply Complex.ofReal_injective
  have hb := Complex.betaIntegral_scaled (s := (i : ℂ)+1) (t := (j : ℂ)+1) hp
  have hs : (i : ℂ)+1+((j : ℂ)+1)-1 = ((i+j+1 : ℕ) : ℂ) := by push_cast; ring
  rw [hs, Complex.cpow_natCast, beta_nat_complex] at hb
  simp only [add_sub_cancel_right, Complex.cpow_natCast] at hb
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    intervalIntegral.integral_ofReal] at hb
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_pow, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hb

/-- Polynomial version, valid for every oriented interval endpoint H. -/
theorem beta_nat_polynomial_integral (H : ℝ) (i j : ℕ) :
    (∫ x in (0 : ℝ)..H, x^i*(H-x)^j) =
      (Nat.factorial i : ℝ) * Nat.factorial j / Nat.factorial (i+j+1) * H^(i+j+1) := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (f := fun x : ℝ => x^i*(H-x)^j) H
  simp only [mul_zero, mul_one] at h
  rw [← h]
  have he (x : ℝ) : (H*x)^i*(H-H*x)^j = H^(i+j)*(x^i*(1-x)^j) := by
    rw [show H-H*x = H*(1-x) by ring, mul_pow, mul_pow, pow_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, beta_nat_integral, pow_succ]
  ring

end Sechstmoment
