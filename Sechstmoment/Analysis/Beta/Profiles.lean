import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Sechstmoment.Analysis.Beta.Integral

namespace Sechstmoment

noncomputable def betaUnitProfile (n k : ℕ) (x : ℝ) : ℝ :=
  (n+1 : ℝ)*(Nat.choose n k : ℝ)*x^k*(1-x)^(n-k)

theorem betaUnit_mass {n k : ℕ} (hk : k ≤ n) :
    (∫ x in (0 : ℝ)..1, betaUnitProfile n k x) = 1 := by
  unfold betaUnitProfile
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  rw [beta_nat_integral, Nat.cast_choose ℝ hk]
  have hn : k+(n-k)+1 = n+1 := by omega
  rw [hn, Nat.factorial_succ]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n-k))]

theorem betaUnit_moment {n k : ℕ} (hk : k ≤ n) (r : ℕ) :
    (∫ x in (0 : ℝ)..1, x^r*betaUnitProfile n k x) =
      (n+1 : ℝ)*(Nat.choose n k : ℝ)*(Nat.factorial (r+k) : ℝ)*
        Nat.factorial (n-k)/Nat.factorial (n+r+1) := by
  have he (x : ℝ) : x^r*betaUnitProfile n k x =
      ((n+1 : ℝ)*(Nat.choose n k : ℝ))*(x^(r+k)*(1-x)^(n-k)) := by
    unfold betaUnitProfile
    rw [pow_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, beta_nat_integral]
  have hn : r+k+(n-k)+1 = n+r+1 := by omega
  rw [hn]
  ring

theorem betaUnit_mean {n k : ℕ} (hk : k ≤ n) :
    (∫ x in (0 : ℝ)..1, x*betaUnitProfile n k x) = (k+1 : ℝ)/(n+2) := by
  have h := betaUnit_moment hk 1
  simp only [pow_one] at h
  rw [h, Nat.cast_choose ℝ hk]
  have hk₁ : 1+k = k+1 := by omega
  have hn₁ : n+1+1 = n+2 := by omega
  rw [hk₁, hn₁, show n+2 = (n+1)+1 by omega,
    Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n-k))]
  ring

theorem betaUnit_second_moment {n k : ℕ} (hk : k ≤ n) :
    (∫ x in (0 : ℝ)..1, x^2*betaUnitProfile n k x) =
      (k+1 : ℝ)*(k+2)/((n+2)*(n+3)) := by
  rw [betaUnit_moment hk 2, Nat.cast_choose ℝ hk]
  rw [show 2+k = k+2 by omega, show n+2+1 = n+3 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n-k))]
  ring

theorem betaUnit_variance_algebra {n k : ℕ} (hk : k ≤ n) :
    (k+1 : ℝ)*(k+2)/((n+2)*(n+3)) - ((k+1 : ℝ)/(n+2))^2 =
      ((k : ℝ)+1)*(((n-k : ℕ) : ℝ)+1)/(((n : ℝ)+2)^2*((n : ℝ)+3)) := by
  rw [Nat.cast_sub hk]
  have hn₂ : (n+2 : ℝ) ≠ 0 := by positivity
  have hn₃ : (n+3 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem betaUnit_variance_bound {n k : ℕ} (hk : k ≤ n) :
    ((k : ℝ)+1)*(((n-k : ℕ) : ℝ)+1)/(((n : ℝ)+2)^2*((n : ℝ)+3)) ≤
      1/(4*((n : ℝ)+3)) := by
  rw [Nat.cast_sub hk]
  have hn₂ : 0 < (n : ℝ)+2 := by positivity
  have hn₃ : 0 < (n : ℝ)+3 := by positivity
  calc
    ((k : ℝ)+1)*((n : ℝ)-k+1)/(((n : ℝ)+2)^2*((n : ℝ)+3)) =
        (((k : ℝ)+1)*((n : ℝ)-k+1)/((n : ℝ)+2)^2)/((n : ℝ)+3) := by rw [div_div]
    _ ≤ (1/4)/((n : ℝ)+3) := by
      apply (div_le_div_iff_of_pos_right hn₃).mpr
      apply (div_le_iff₀ (sq_pos_of_pos hn₂)).mpr
      nlinarith [sq_nonneg ((k : ℝ)+1-((n : ℝ)-k+1))]
    _ = _ := by rw [div_div]

theorem betaUnit_variance {n k : ℕ} (hk : k ≤ n) :
    (∫ x in (0 : ℝ)..1, (x-(k+1 : ℝ)/(n+2))^2*betaUnitProfile n k x) =
      ((k : ℝ)+1)*(((n-k : ℕ) : ℝ)+1)/(((n : ℝ)+2)^2*((n : ℝ)+3)) := by
  let m : ℝ := (k+1 : ℝ)/(n+2)
  have he (x : ℝ) : (x-m)^2*betaUnitProfile n k x =
      x^2*betaUnitProfile n k x - 2*m*(x*betaUnitProfile n k x) +
        m^2*betaUnitProfile n k x := by ring
  change (∫ x in (0 : ℝ)..1, (x-m)^2*betaUnitProfile n k x) = _
  simp_rw [he]
  have h₁ : Continuous (fun x : ℝ => x^2*betaUnitProfile n k x) := by
    unfold betaUnitProfile
    fun_prop
  have h₂ : Continuous (fun x : ℝ => 2*m*(x*betaUnitProfile n k x)) := by
    unfold betaUnitProfile
    fun_prop
  have h₃ : Continuous (fun x : ℝ => m^2*betaUnitProfile n k x) := by
    unfold betaUnitProfile
    fun_prop
  have h₁₂ : Continuous (fun x : ℝ =>
      x^2*betaUnitProfile n k x-2*m*(x*betaUnitProfile n k x)) := by fun_prop
  rw [intervalIntegral.integral_add (h₁₂.intervalIntegrable 0 1) (h₃.intervalIntegrable 0 1),
    intervalIntegral.integral_sub (h₁.intervalIntegrable 0 1) (h₂.intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    betaUnit_second_moment hk, betaUnit_mean hk, betaUnit_mass hk]
  dsimp [m]
  rw [← betaUnit_variance_algebra hk]
  ring

end Sechstmoment
