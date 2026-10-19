import Mathlib.Tactic
import Sechstmoment.Arithmetic.Euler.Shifted.Rest

/-!
# A genuine uniform quadratic tail bound for the diagonal local series

The constant is deliberately coarse. The bound is proved from the actual
prime coefficients and an absolutely convergent geometric majorant, rather
than from an assumed Euler-remainder estimate.
-/

namespace Sechstmoment

open Real Complex
open scoped BigOperators

noncomputable section

theorem d3PrimePowerCoefficient_add_two_le (m : ℕ) :
    (d3PrimePowerCoefficient (m+2):ℝ) ≤ 6*(d3PrimePowerCoefficient m:ℝ) := by
  rw [d3PrimePowerCoefficient_cast, d3PrimePowerCoefficient_cast]
  push_cast
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [sq_nonneg (m:ℝ)]

theorem d3PrimePowerCoefficient_add_two_sq_le (m : ℕ) :
    (d3PrimePowerCoefficient (m+2):ℝ)^2 ≤ 36*(d3PrimePowerCoefficient m:ℝ)^2 := by
  have h := d3PrimePowerCoefficient_add_two_le m
  have ha : (0:ℝ) ≤ d3PrimePowerCoefficient (m+2) := Nat.cast_nonneg _
  have hb : (0:ℝ) ≤ d3PrimePowerCoefficient m := Nat.cast_nonneg _
  nlinarith

/-- The exact constant of the convergent real majorant at `1/2`. -/
theorem hasSum_d3PrimePower_half :
    HasSum (fun m : ℕ => (d3PrimePowerCoefficient m:ℝ)^2*(1/2)^m) 104 := by
  convert hasSum_d3PrimePower_sq (x := (1/2:ℝ)) (by norm_num) using 1
  norm_num

theorem diagonalPrimeTail_norm_le {a b : Fin 3 → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : ∀ i : Fin 3, ‖a i‖ ≤ r) (hb : ∀ i : Fin 3, ‖b i‖ ≤ r)
    {x : ℂ} (hx : r^2*‖x‖ ≤ 1/2) :
    ‖∑' m : ℕ, triplePrimePowerCoefficient a (m+2) *
        triplePrimePowerCoefficient b (m+2) * x^(m+2)‖ ≤ 3744*(r^2*‖x‖)^2 := by
  let y : ℝ := r^2*‖x‖
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hmajorant : HasSum
      (fun m : ℕ => (36*y^2) * ((d3PrimePowerCoefficient m:ℝ)^2*(1/2)^m))
      (3744*y^2) := by
    convert hasSum_d3PrimePower_half.mul_left (36*y^2) using 1
    ring
  apply tsum_of_norm_bounded hmajorant
  intro m
  calc
    _ ≤ (d3PrimePowerCoefficient (m+2):ℝ)^2*y^(m+2) :=
      diagonalPrimeTerm_norm_le hr ha hb x (m+2)
    _ ≤ (36*(d3PrimePowerCoefficient m:ℝ)^2)*(y^m*y^2) := by
      rw [pow_add]
      gcongr
      exact d3PrimePowerCoefficient_add_two_sq_le m
    _ ≤ (36*(d3PrimePowerCoefficient m:ℝ)^2)*((1/2)^m*y^2) := by
      gcongr
    _ = _ := by ring

/-- Decomposition of the actual infinite series into its two polar terms
and the genuinely absolutely convergent tail. -/
theorem diagonalPrimeSeries_linear_tail {a b : Fin 3 → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : ∀ i : Fin 3, ‖a i‖ ≤ r) (hb : ∀ i : Fin 3, ‖b i‖ ≤ r)
    {x : ℂ} (hx : r^2*‖x‖ < 1) :
    (∑' m : ℕ, triplePrimePowerCoefficient a m * triplePrimePowerCoefficient b m * x^m) -
      1 - (∑ i : Fin 3, a i)*(∑ j : Fin 3, b j)*x =
      ∑' m : ℕ, triplePrimePowerCoefficient a (m+2) *
        triplePrimePowerCoefficient b (m+2) * x^(m+2) := by
  have h := (diagonalPrimeSeries_summable hr ha hb hx).sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    triplePrimePowerCoefficient_zero, triplePrimePowerCoefficient_one, pow_zero,
    pow_one, mul_one] at h
  rw [← h]
  ring

/-- Actual quadratic cancellation of the diagonal local series after its
constant and linear coefficients have been subtracted. -/
theorem diagonalPrimeSeries_sub_linear_norm_le {a b : Fin 3 → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : ∀ i : Fin 3, ‖a i‖ ≤ r) (hb : ∀ i : Fin 3, ‖b i‖ ≤ r)
    {x : ℂ} (hx : r^2*‖x‖ ≤ 1/2) :
    ‖(∑' m : ℕ, triplePrimePowerCoefficient a m * triplePrimePowerCoefficient b m * x^m) -
      1 - (∑ i : Fin 3, a i)*(∑ j : Fin 3, b j)*x‖ ≤ 3744*(r^2*‖x‖)^2 := by
  rw [diagonalPrimeSeries_linear_tail hr ha hb (lt_of_le_of_lt hx (by norm_num))]
  exact diagonalPrimeTail_norm_le hr ha hb hx

end

end Sechstmoment
