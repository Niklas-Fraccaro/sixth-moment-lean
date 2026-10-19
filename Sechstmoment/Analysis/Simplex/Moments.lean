import Mathlib.Tactic.FieldSimp
import Sechstmoment.Analysis.Beta.Integral

namespace Sechstmoment

theorem simplex_monomial_two (H : ℝ) (i j k : ℕ) :
    (∫ x in (0 : ℝ)..H, ∫ y in (0 : ℝ)..H-x,
      x^i*y^j*(H-x-y)^k) =
      (Nat.factorial i : ℝ)*Nat.factorial j*Nat.factorial k /
        Nat.factorial (i+j+k+2) * H^(i+j+k+2) := by
  have hx (x : ℝ) : (∫ y in (0 : ℝ)..H-x, x^i*y^j*(H-x-y)^k) =
      x^i*((Nat.factorial j : ℝ)*Nat.factorial k / Nat.factorial (j+k+1) *
        (H-x)^(j+k+1)) := by
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, beta_nat_polynomial_integral]
  simp_rw [hx]
  have he (x : ℝ) : x^i*((Nat.factorial j : ℝ)*Nat.factorial k /
      Nat.factorial (j+k+1) * (H-x)^(j+k+1)) =
      ((Nat.factorial j : ℝ)*Nat.factorial k / Nat.factorial (j+k+1)) *
        (x^i*(H-x)^(j+k+1)) := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, beta_nat_polynomial_integral]
  have hn : i+(j+k+1)+1 = i+j+k+2 := by omega
  rw [hn]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j+k+1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (i+j+k+2))]

theorem simplex_monomial_three (H : ℝ) (i j k l : ℕ) :
    (∫ x in (0 : ℝ)..H, ∫ y in (0 : ℝ)..H-x, ∫ z in (0 : ℝ)..H-x-y,
      x^i*y^j*z^k*(H-x-y-z)^l) =
      (Nat.factorial i : ℝ)*Nat.factorial j*Nat.factorial k*Nat.factorial l /
        Nat.factorial (i+j+k+l+3) * H^(i+j+k+l+3) := by
  have hz (x y : ℝ) : (∫ z in (0 : ℝ)..H-x-y, x^i*y^j*z^k*(H-x-y-z)^l) =
      ((Nat.factorial k : ℝ)*Nat.factorial l / Nat.factorial (k+l+1)) *
        (x^i*y^j*(H-x-y)^(k+l+1)) := by
    simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
    rw [beta_nat_polynomial_integral]
    ring
  simp_rw [hz, intervalIntegral.integral_const_mul]
  rw [simplex_monomial_two]
  have hn : i+j+(k+l+1)+2 = i+j+k+l+3 := by omega
  rw [hn]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k+l+1)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (i+j+k+l+3))]

noncomputable def simplexExpectation (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  6*(∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1-x, ∫ z in (0 : ℝ)..1-x-y, f x y z)

/-- Dirichlet-simplex moments, including the normalization of the uniform law. -/
theorem simplexExpectation_monomial (i j k l : ℕ) :
    simplexExpectation (fun x y z => x^i*y^j*z^k*(1-x-y-z)^l) =
      6*(Nat.factorial i : ℝ)*Nat.factorial j*Nat.factorial k*Nat.factorial l /
        Nat.factorial (i+j+k+l+3) := by
  rw [simplexExpectation, simplex_monomial_three]
  simp only [one_pow, mul_one]
  ring

theorem simplexExpectation_one : simplexExpectation (fun _ _ _ => 1) = 1 := by
  have h := simplexExpectation_monomial 0 0 0 0
  norm_num at h
  exact h

end Sechstmoment
