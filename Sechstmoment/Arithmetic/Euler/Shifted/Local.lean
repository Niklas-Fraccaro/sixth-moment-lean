import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.LinearCombination
import Sechstmoment.Arithmetic.Factor.Convergence

/-!
# The actual unshifted local factor in the nine-pair polar extraction

The coefficient `d₃(p^m)` is the triangular number `choose (m+2) 2`.
Its squared generating series is summed, with convergence proved, and the nine
local polar factors are removed exactly. The resulting prime product is the
arithmetic factor in `MainGoal`. This file does not claim analyticity of the
multivariate shifted Euler remainder or any contour bound.
-/

namespace Sechstmoment

noncomputable section

def d3PrimePowerCoefficient (m : ℕ) : ℕ := (m+2).choose 2

private theorem rising_choose_two {K : Type*} [Field K] [CharZero K] (m : ℕ) :
    ((m+2).choose 2 : K) = (m+1:K)*(m+2)/2 := by
  have h : (2:K)*((m+2).choose 2 : K) = ((m+1).ascFactorial 2 : K) := by
    exact_mod_cast (Nat.ascFactorial_eq_factorial_mul_choose m 2).symm
  norm_num [Nat.ascFactorial] at h
  linear_combination h/2

private theorem rising_choose_three {K : Type*} [Field K] [CharZero K] (m : ℕ) :
    ((m+3).choose 3 : K) = (m+1:K)*(m+2)*(m+3)/6 := by
  have h : (6:K)*((m+3).choose 3 : K) = ((m+1).ascFactorial 3 : K) := by
    exact_mod_cast (Nat.ascFactorial_eq_factorial_mul_choose m 3).symm
  norm_num [Nat.ascFactorial] at h
  linear_combination h/6

private theorem rising_choose_four {K : Type*} [Field K] [CharZero K] (m : ℕ) :
    ((m+4).choose 4 : K) = (m+1:K)*(m+2)*(m+3)*(m+4)/24 := by
  have h : (24:K)*((m+4).choose 4 : K) = ((m+1).ascFactorial 4 : K) := by
    exact_mod_cast (Nat.ascFactorial_eq_factorial_mul_choose m 4).symm
  norm_num [Nat.ascFactorial] at h
  linear_combination h/24

theorem d3PrimePowerCoefficient_cast {K : Type*} [Field K] [CharZero K] (m : ℕ) :
    (d3PrimePowerCoefficient m : K) = (m+1:K)*(m+2)/2 :=
  rising_choose_two m

/-- The finite binomial decomposition which sums the quartic coefficients. -/
theorem d3PrimePowerCoefficient_sq {K : Type*} [Field K] [CharZero K] (m : ℕ) :
    (d3PrimePowerCoefficient m : K)^2 =
      6*((m+4).choose 4 : K) - 6*((m+3).choose 3 : K) + ((m+2).choose 2 : K) := by
  rw [d3PrimePowerCoefficient_cast, rising_choose_four, rising_choose_three, rising_choose_two]
  ring

/-- Convergent summation of the actual squared `d₃` local coefficients. -/
theorem hasSum_d3PrimePower_sq {K : Type*} [NormedField K] [CharZero K]
    [HasSummableGeomSeries K] {x : K} (hx : ‖x‖ < 1) :
    HasSum (fun m : ℕ => (d3PrimePowerCoefficient m : K)^2*x^m)
      ((1+4*x+x^2)/(1-x)^5) := by
  have h4 := (hasSum_choose_mul_geometric_of_norm_lt_one 4 hx).mul_left (6 : K)
  have h3 := (hasSum_choose_mul_geometric_of_norm_lt_one 3 hx).mul_left (6 : K)
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 hx
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, norm_one] at hx
    exact (lt_irrefl 1) hx
  have hd : 1-x ≠ 0 := sub_ne_zero.mpr hx1.symm
  convert (h4.sub h3).add h2 using 1
  · funext m
    rw [d3PrimePowerCoefficient_sq]
    ring
  · field_simp
    ring

theorem tsum_d3PrimePower_sq {K : Type*} [NormedField K] [CharZero K]
    [HasSummableGeomSeries K] {x : K} (hx : ‖x‖ < 1) :
    (∑' m : ℕ, (d3PrimePowerCoefficient m : K)^2*x^m) =
      (1+4*x+x^2)/(1-x)^5 :=
  (hasSum_d3PrimePower_sq hx).tsum_eq

/-- The local identity in §3.1, with the square of the displayed triangular
number rather than an unnamed coefficient sequence. -/
theorem d3_local_series_identity {K : Type*} [NormedField K] [CharZero K]
    [HasSummableGeomSeries K] {x : K} (hx : ‖x‖ < 1) :
    (1-x)^5 * (∑' m : ℕ, (((m+1:K)*(m+2)/2)^2)*x^m) = 1+4*x+x^2 := by
  simp_rw [← d3PrimePowerCoefficient_cast]
  rw [tsum_d3PrimePower_sq hx]
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, norm_one] at hx
    exact (lt_irrefl 1) hx
  have hd : 1-x ≠ 0 := sub_ne_zero.mpr hx1.symm
  exact mul_div_cancel₀ _ (pow_ne_zero _ hd)

/-- Removing all nine unshifted polar factors leaves the true local remainder. -/
theorem d3_nine_polar_factors {K : Type*} [NormedField K] [CharZero K]
    [HasSummableGeomSeries K] {x : K} (hx : ‖x‖ < 1) :
    (1-x)^9 * (∑' m : ℕ, (((m+1:K)*(m+2)/2)^2)*x^m) =
      (1-x)^4*(1+4*x+x^2) := by
  calc
    _ = (1-x)^4 * ((1-x)^5 * (∑' m : ℕ, (((m+1:K)*(m+2)/2)^2)*x^m)) := by ring
    _ = _ := by rw [d3_local_series_identity hx]

/-- The actual local prime series at all zero shifts. -/
def unshiftedPolarPrimeFactor (p : {n : ℕ // Nat.Prime n}) : ℝ :=
  (1-1/(p.val:ℝ))^9 *
    ∑' m : ℕ, (((m+1:ℝ)*(m+2)/2)^2)*(1/(p.val:ℝ))^m

theorem unshiftedPolarPrimeFactor_eq (p : {n : ℕ // Nat.Prime n}) :
    unshiftedPolarPrimeFactor p = eulerFactor (p.val:ℝ) := by
  have hp : (1:ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hx : ‖1/(p.val:ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_lt_one (by linarith)).mpr hp
  unfold unshiftedPolarPrimeFactor eulerFactor
  rw [d3_nine_polar_factors hx]
  ring

/-- The genuine unshifted Euler remainder, before identifying it with `a₃`. -/
def unshiftedPolarEulerRest : ℝ := ∏' p : {n : ℕ // Nat.Prime n}, unshiftedPolarPrimeFactor p

theorem unshiftedPolarEulerRest_eq_arithmeticFactor :
    unshiftedPolarEulerRest = arithmeticFactor := by
  unfold unshiftedPolarEulerRest arithmeticFactor
  apply tprod_congr
  exact unshiftedPolarPrimeFactor_eq

theorem unshiftedPolarPrimeFactor_multipliable :
    Multipliable (fun p : {n : ℕ // Nat.Prime n} => unshiftedPolarPrimeFactor p) := by
  simp_rw [unshiftedPolarPrimeFactor_eq]
  exact arithmeticFactor_wellDefined.1

theorem unshiftedPolarEulerRest_pos : 0 < unshiftedPolarEulerRest := by
  rw [unshiftedPolarEulerRest_eq_arithmeticFactor]
  exact arithmeticFactor_wellDefined.2

end

end Sechstmoment
