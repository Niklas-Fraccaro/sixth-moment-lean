import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Tactic
import Sechstmoment.Arithmetic.Euler.Shifted.Pairings
import Sechstmoment.Zeta.Regularized

/-!
# The actual shifted Euler remainder

The definition is the true prime-power diagonal series multiplied by its nine
local zeta divisors. Its value at zero is identified with `a₃`, using convergent
prime-power summation and the proved arithmetic Euler product. The finite
coefficient bound is also proved. Analyticity and uniform product convergence
away from zero are not consequences of the definition alone.
-/

namespace Sechstmoment

open Real Complex
open scoped BigOperators

noncomputable section

theorem triplePrimePowerCoefficient_norm_le {a : Fin 3 → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : ∀ i : Fin 3, ‖a i‖ ≤ r) (m : ℕ) :
    ‖triplePrimePowerCoefficient a m‖ ≤ (d3PrimePowerCoefficient m : ℝ)*r^m := by
  have hterm (i j : ℕ) (hi : i ∈ Finset.range (m+1))
      (hj : j ∈ Finset.range (m+1-i)) :
      ‖a 0^i*a 1^j*a 2^(m-i-j)‖ ≤ r^m := by
    rw [norm_mul, norm_mul, Complex.norm_pow, Complex.norm_pow, Complex.norm_pow]
    calc
      ‖a 0‖^i*‖a 1‖^j*‖a 2‖^(m-i-j) ≤ r^i*r^j*r^(m-i-j) := by
        gcongr <;> exact ha _
      _ = r^m := by
        rw [← pow_add, ← pow_add]
        congr 1
        have hi' := Finset.mem_range.mp hi
        have hj' := Finset.mem_range.mp hj
        omega
  calc
    _ ≤ ∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (m+1-i),
        ‖a 0^i*a 1^j*a 2^(m-i-j)‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (m+1-i), r^m := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hterm i j hi hj
    _ = _ := by
      rw [← triplePrimePowerCoefficient_const_one (R := ℝ) m]
      simp only [triplePrimePowerCoefficient, one_pow, mul_one, Finset.sum_mul, one_mul]

theorem diagonalPrimeTerm_norm_le {a b : Fin 3 → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : ∀ i : Fin 3, ‖a i‖ ≤ r) (hb : ∀ i : Fin 3, ‖b i‖ ≤ r)
    (x : ℂ) (m : ℕ) :
    ‖triplePrimePowerCoefficient a m * triplePrimePowerCoefficient b m * x^m‖ ≤
      (d3PrimePowerCoefficient m : ℝ)^2 * (r^2*‖x‖)^m := by
  rw [norm_mul, norm_mul, Complex.norm_pow]
  calc
    _ ≤ ((d3PrimePowerCoefficient m:ℝ)*r^m)*
        ((d3PrimePowerCoefficient m:ℝ)*r^m)*‖x‖^m := by
      gcongr
      · exact triplePrimePowerCoefficient_norm_le hr ha m
      · exact triplePrimePowerCoefficient_norm_le hr hb m
    _ = _ := by
      rw [show r^2 = r*r by ring, mul_pow, mul_pow]
      ring

/-- Absolute convergence of the genuine diagonal local series in its
geometric domain, deduced from the actual squared `d₃` coefficients. -/
theorem diagonalPrimeSeries_norm_summable {a b : Fin 3 → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : ∀ i : Fin 3, ‖a i‖ ≤ r) (hb : ∀ i : Fin 3, ‖b i‖ ≤ r)
    {x : ℂ} (hx : r^2*‖x‖ < 1) :
    Summable (fun m : ℕ => ‖triplePrimePowerCoefficient a m *
      triplePrimePowerCoefficient b m * x^m‖) := by
  have hy : ‖r^2*‖x‖‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hx
  apply (hasSum_d3PrimePower_sq hy).summable.of_norm_bounded
  intro m
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact diagonalPrimeTerm_norm_le hr ha hb x m

theorem diagonalPrimeSeries_summable {a b : Fin 3 → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : ∀ i : Fin 3, ‖a i‖ ≤ r) (hb : ∀ i : Fin 3, ‖b i‖ ≤ r)
    {x : ℂ} (hx : r^2*‖x‖ < 1) :
    Summable (fun m : ℕ => triplePrimePowerCoefficient a m *
      triplePrimePowerCoefficient b m * x^m) :=
  (diagonalPrimeSeries_norm_summable hr ha hb hx).of_norm

def primePolarWeights (p : {n : ℕ // Nat.Prime n}) (a : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => (p.val:ℂ)^(-a i)

theorem primePolarWeights_norm (p : {n : ℕ // Nat.Prime n}) (a : Fin 3 → ℂ)
    (i : Fin 3) : ‖primePolarWeights p a i‖ = (p.val:ℝ)^(-(a i).re) := by
  unfold primePolarWeights
  have hp : (0:ℝ) < p.val := by exact_mod_cast p.property.pos
  simpa only [neg_re, Complex.ofReal_natCast] using Complex.norm_cpow_eq_rpow_re_of_pos hp (-a i)

theorem primePolarWeights_norm_le (p : {n : ℕ // Nat.Prime n}) (a : Fin 3 → ℂ)
    {δ : ℝ} (ha : ∀ i : Fin 3, -δ ≤ (a i).re) :
    ∀ i : Fin 3, ‖primePolarWeights p a i‖ ≤ (p.val:ℝ)^δ := by
  intro i
  rw [primePolarWeights_norm]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast p.property.one_lt.le
  · linarith [ha i]

/-- The genuine diagonal prime-power series. -/
def shiftedDiagonalPrimeSeries (p : {n : ℕ // Nat.Prime n}) (a b : Fin 3 → ℂ) : ℂ :=
  ∑' m : ℕ, triplePrimePowerCoefficient (primePolarWeights p a) m *
    triplePrimePowerCoefficient (primePolarWeights p b) m * (1/(p.val:ℂ))^m

/-- The real half-space conditions prove absolute convergence of the actual
local complex series throughout a genuine neighborhood of the zero shifts. -/
theorem shiftedDiagonalPrimeSeries_norm_summable (p : {n : ℕ // Nat.Prime n})
    (a b : Fin 3 → ℂ) {δ : ℝ} (hδ : δ < 1/2)
    (ha : ∀ i : Fin 3, -δ ≤ (a i).re) (hb : ∀ i : Fin 3, -δ ≤ (b i).re) :
    Summable (fun m : ℕ => ‖triplePrimePowerCoefficient (primePolarWeights p a) m *
      triplePrimePowerCoefficient (primePolarWeights p b) m * (1/(p.val:ℂ))^m‖) := by
  have hp : (1:ℝ) < p.val := by exact_mod_cast p.property.one_lt
  apply diagonalPrimeSeries_norm_summable (Real.rpow_nonneg (by positivity) δ)
    (primePolarWeights_norm_le p a ha) (primePolarWeights_norm_le p b hb)
  rw [Complex.norm_div, norm_one, Complex.norm_natCast]
  have he : ((p.val:ℝ)^δ)^2 * (1/(p.val:ℝ)) = (p.val:ℝ)^(2*δ-1) := by
    rw [Real.rpow_sub_one (by positivity), mul_one_div,
      ← Real.rpow_mul_natCast (by positivity) δ 2]
    congr 2
    ring
  rw [he]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)

def shiftedPolarPrimeDivisors (p : {n : ℕ // Nat.Prime n}) (a b : Fin 3 → ℂ) : ℂ :=
  ∏ ij : Fin 3 × Fin 3, (1-(p.val:ℂ)^(-(1+a ij.1+b ij.2)))

def shiftedPolarPrimeRemainder (p : {n : ℕ // Nat.Prime n}) (a b : Fin 3 → ℂ) : ℂ :=
  shiftedPolarPrimeDivisors p a b * shiftedDiagonalPrimeSeries p a b

/-- The actual shifted arithmetic Euler remainder `A`, as a prime product. -/
def shiftedPolarEulerRest (a b : Fin 3 → ℂ) : ℂ :=
  ∏' p : {n : ℕ // Nat.Prime n}, shiftedPolarPrimeRemainder p a b

theorem shiftedPolarPrimeRemainder_zero (p : {n : ℕ // Nat.Prime n}) :
    shiftedPolarPrimeRemainder p (fun _ => 0) (fun _ => 0) =
      (eulerFactor (p.val:ℝ):ℂ) := by
  have hp : (1:ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hx : ‖1/(p.val:ℂ)‖ < 1 := by
    rw [Complex.norm_div, norm_one, Complex.norm_natCast]
    exact (div_lt_one (by linarith)).mpr hp
  have hweights : primePolarWeights p (fun _ => 0) = (fun _ => 1) := by
    funext i
    simp [primePolarWeights]
  unfold shiftedPolarPrimeRemainder shiftedPolarPrimeDivisors shiftedDiagonalPrimeSeries
  simp only [add_zero, Complex.cpow_neg_one,
    Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hweights]
  norm_num only
  simp_rw [triplePrimePowerCoefficient_const_one]
  have hsq (m : ℕ) : (d3PrimePowerCoefficient m:ℂ)*(d3PrimePowerCoefficient m:ℂ) =
      (d3PrimePowerCoefficient m:ℂ)^2 := by ring
  simp_rw [hsq]
  rw [tsum_d3PrimePower_sq hx]
  have hpn : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  unfold eulerFactor
  push_cast
  field_simp

/-- The genuine actual product at all zero shifts, with convergence proved. -/
theorem shiftedPolarEulerRest_zero :
    shiftedPolarEulerRest (fun _ => 0) (fun _ => 0) = (arithmeticFactor:ℂ) := by
  unfold shiftedPolarEulerRest
  simp_rw [shiftedPolarPrimeRemainder_zero]
  exact (arithmeticFactor_wellDefined.1.map_tprod Complex.ofRealHom Complex.continuous_ofReal).symm

theorem shiftedPolarPrimeRemainder_zero_multipliable :
    Multipliable (fun p : {n : ℕ // Nat.Prime n} =>
      shiftedPolarPrimeRemainder p (fun _ => 0) (fun _ => 0)) := by
  simp_rw [shiftedPolarPrimeRemainder_zero]
  exact arithmeticFactor_wellDefined.1.map Complex.ofRealHom Complex.continuous_ofReal

end

end Sechstmoment
