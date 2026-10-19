import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic
import Sechstmoment.Arithmetic.Euler.Shifted.Local

/-!
# Exact first-degree cancellation by the nine polar pairings

The actual three-variable complete homogeneous coefficients are defined by
their finite prime-power sum. Their diagonal generating series is a formal
power series. Multiplication by the nine local polar divisors has constant
coefficient one and no linear coefficient. This is the algebraic cancellation
behind the claimed `O(p⁻²)` Euler remainder; convergence in a shifted complex
neighborhood still requires a separate analytic bound.
-/

namespace Sechstmoment

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- The actual prime-power coefficient of a product of three geometric
factors, with its three exponents summing to `m`. -/
def triplePrimePowerCoefficient (a : Fin 3 → R) (m : ℕ) : R :=
  ∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (m+1-i),
    a 0^i * a 1^j * a 2^(m-i-j)

@[simp] theorem triplePrimePowerCoefficient_zero (a : Fin 3 → R) :
    triplePrimePowerCoefficient a 0 = 1 := by
  simp [triplePrimePowerCoefficient]

theorem triplePrimePowerCoefficient_one (a : Fin 3 → R) :
    triplePrimePowerCoefficient a 1 = ∑ i : Fin 3, a i := by
  simp [triplePrimePowerCoefficient, Finset.sum_range_succ, Fin.sum_univ_succ]
  ring

/-- At zero shifts these actual threefold prime coefficients are `d₃(p^m)`. -/
theorem triplePrimePowerCoefficient_const_one (m : ℕ) :
    triplePrimePowerCoefficient (fun _ : Fin 3 => (1:R)) m = (d3PrimePowerCoefficient m : R) := by
  simp only [triplePrimePowerCoefficient, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hreflect : (∑ i ∈ Finset.range (m+1), (m+1-i)) =
      ∑ i ∈ Finset.range (m+1), (i+1) := by
    calc
      _ = ∑ i ∈ Finset.range (m+1), (m-i+1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        omega
      _ = _ := by simpa using Finset.sum_range_reflect (fun i => i+1) (m+1)
  have hcount : (∑ i ∈ Finset.range (m+1), (m+1-i)) = d3PrimePowerCoefficient m := by
    rw [hreflect]
    simpa [d3PrimePowerCoefficient] using Nat.sum_range_add_choose m 1
  simpa only [Nat.cast_sum] using congrArg (fun n : ℕ => (n:R)) hcount

/-- The diagonal local series before extracting the nine zeta factors. -/
def diagonalLocalPowerSeries (a b : Fin 3 → R) : PowerSeries R :=
  PowerSeries.mk (fun m => triplePrimePowerCoefficient a m * triplePrimePowerCoefficient b m)

def nineLocalPolarRemover (a b : Fin 3 → R) : PowerSeries R :=
  ∏ ij : Fin 3 × Fin 3,
    (1-PowerSeries.C (a ij.1*b ij.2)*PowerSeries.X)

def diagonalPolarRemainderSeries (a b : Fin 3 → R) : PowerSeries R :=
  nineLocalPolarRemover a b * diagonalLocalPowerSeries a b

@[simp] theorem diagonalLocalPowerSeries_constantCoeff (a b : Fin 3 → R) :
    PowerSeries.constantCoeff (diagonalLocalPowerSeries a b) = 1 := by
  simp [diagonalLocalPowerSeries]

theorem diagonalLocalPowerSeries_coeff_one (a b : Fin 3 → R) :
    PowerSeries.coeff 1 (diagonalLocalPowerSeries a b) =
      ∑ ij : Fin 3 × Fin 3, a ij.1*b ij.2 := by
  simp only [diagonalLocalPowerSeries, PowerSeries.coeff_mk,
    triplePrimePowerCoefficient_one]
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

private theorem polar_remover_constantCoeff {ι : Type*} (s : Finset ι) (w : ι → R) :
    PowerSeries.constantCoeff (∏ i ∈ s, (1-PowerSeries.C (w i)*PowerSeries.X)) = 1 := by
  simp

private theorem polar_remover_coeff_one {ι : Type*} (s : Finset ι) (w : ι → R) :
    PowerSeries.coeff 1 (∏ i ∈ s, (1-PowerSeries.C (w i)*PowerSeries.X)) =
      -∑ i ∈ s, w i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PowerSeries.coeff_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, PowerSeries.coeff_one_mul,
      polar_remover_constantCoeff, ih, Finset.sum_insert hi]
    simp [PowerSeries.coeff_one]
    ring

@[simp] theorem nineLocalPolarRemover_constantCoeff (a b : Fin 3 → R) :
    PowerSeries.constantCoeff (nineLocalPolarRemover a b) = 1 :=
  polar_remover_constantCoeff _ _

theorem nineLocalPolarRemover_coeff_one (a b : Fin 3 → R) :
    PowerSeries.coeff 1 (nineLocalPolarRemover a b) =
      -∑ ij : Fin 3 × Fin 3, a ij.1*b ij.2 :=
  polar_remover_coeff_one _ _

/-- Nine pairings cancel exactly the entire degree-one diagonal coefficient. -/
theorem diagonalPolarRemainderSeries_coeff_one (a b : Fin 3 → R) :
    PowerSeries.coeff 1 (diagonalPolarRemainderSeries a b) = 0 := by
  unfold diagonalPolarRemainderSeries
  rw [PowerSeries.coeff_one_mul, nineLocalPolarRemover_coeff_one,
    diagonalLocalPowerSeries_constantCoeff, nineLocalPolarRemover_constantCoeff,
    diagonalLocalPowerSeries_coeff_one]
  ring

@[simp] theorem diagonalPolarRemainderSeries_constantCoeff (a b : Fin 3 → R) :
    PowerSeries.constantCoeff (diagonalPolarRemainderSeries a b) = 1 := by
  simp [diagonalPolarRemainderSeries]

/-- A precise algebraic rest statement: the remainder differs from one by a
multiple of `X²`. This is not an unproved analytic big-O assertion. -/
theorem diagonalPolarRemainderSeries_sub_one_dvd_X_sq (a b : Fin 3 → R) :
    (PowerSeries.X : PowerSeries R)^2 ∣ diagonalPolarRemainderSeries a b - 1 := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  interval_cases m
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp [diagonalPolarRemainderSeries_coeff_one, PowerSeries.coeff_one]

end

end Sechstmoment
