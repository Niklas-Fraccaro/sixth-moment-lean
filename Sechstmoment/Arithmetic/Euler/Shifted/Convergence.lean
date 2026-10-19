import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import Sechstmoment.Arithmetic.Euler.Shifted.RemainderBounds

/-!
# Convergence of the genuine shifted arithmetic product

The shifted diagonal local series and its nine actual zeta divisors have a
uniform quadratic remainder. Its prime majorant is a convergent p-series
throughout the six-dimensional half-space with shifts' real parts at least
`-δ`, `δ < 1/4`. No shifted Euler-product hypothesis is used.
-/

namespace Sechstmoment

open Real Complex Filter
open scoped BigOperators Topology

noncomputable section

theorem shiftedPolarPrimeDivisors_eq (p : {n : ℕ // Nat.Prime n})
    (a b : Fin 3 → ℂ) :
    shiftedPolarPrimeDivisors p a b =
      ∏ ij : Fin 3 × Fin 3,
        (1-primePolarWeights p a ij.1*primePolarWeights p b ij.2*(1/(p.val:ℂ))) := by
  apply Finset.prod_congr rfl
  intro ij _
  have hp : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have h : -(1+a ij.1+b ij.2) = -a ij.1 + -b ij.2 + (-1:ℂ) := by ring
  simp only [primePolarWeights, h, Complex.cpow_add _ _ hp, Complex.cpow_neg_one]
  simp only [one_div]

theorem primePolarGeometricRadius (p : {n : ℕ // Nat.Prime n}) (δ : ℝ) :
    ((p.val:ℝ)^δ)^2*‖1/(p.val:ℂ)‖ = (p.val:ℝ)^(2*δ-1) := by
  have hp : (0:ℝ) < p.val := by exact_mod_cast p.property.pos
  rw [Complex.norm_div, norm_one, Complex.norm_natCast,
    Real.rpow_sub_one hp.ne', mul_one_div, ← Real.rpow_mul_natCast hp.le δ 2]
  congr 2
  ring

theorem shiftedPolarPrimeRemainder_sub_one_bound
    (p : {n : ℕ // Nat.Prime n}) (a b : Fin 3 → ℂ) {δ : ℝ}
    (ha : ∀ i : Fin 3, -δ ≤ (a i).re) (hb : ∀ i : Fin 3, -δ ≤ (b i).re)
    (hpδ : (p.val:ℝ)^(2*δ-1) ≤ 1/2) :
    ‖shiftedPolarPrimeRemainder p a b-1‖ ≤ 2000000*(p.val:ℝ)^(4*δ-2) := by
  have hp : (0:ℝ) < p.val := by exact_mod_cast p.property.pos
  unfold shiftedPolarPrimeRemainder
  rw [shiftedPolarPrimeDivisors_eq]
  have h := diagonalPolarRemainder_norm_le (Real.rpow_nonneg hp.le δ)
    (primePolarWeights_norm_le p a ha) (primePolarWeights_norm_le p b hb)
    (x := 1/(p.val:ℂ)) (by rwa [primePolarGeometricRadius])
  unfold shiftedDiagonalPrimeSeries
  rw [primePolarGeometricRadius, ← Real.rpow_mul_natCast hp.le (2*δ-1) 2] at h
  have he : (2*δ-1)*(2:ℕ) = 4*δ-2 := by push_cast; ring
  simpa only [he] using h

theorem primePolarGeometricRadius_eventually {δ : ℝ} (hδ : δ < 1/2) :
    ∀ᶠ p : {n : ℕ // Nat.Prime n} in cofinite, (p.val:ℝ)^(2*δ-1) ≤ 1/2 := by
  have hpow : Tendsto (fun x : ℝ => x^(2*δ-1)) atTop (𝓝 0) := by
    have he : -(1-2*δ) = 2*δ-1 := by ring
    simpa only [he] using tendsto_rpow_neg_atTop (y := 1-2*δ) (by linarith)
  have hnat : Tendsto (fun n : ℕ => (n:ℝ)^(2*δ-1)) cofinite (𝓝 0) :=
    Nat.cofinite_eq_atTop ▸ hpow.comp tendsto_natCast_atTop_atTop
  exact Subtype.val_injective.tendsto_cofinite.eventually
    (hnat.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1/2)))

theorem shiftedPolarPrimeMajorant_summable {δ : ℝ} (hδ : δ < 1/4) :
    Summable (fun p : {n : ℕ // Nat.Prime n} => 2000000*(p.val:ℝ)^(4*δ-2)) := by
  exact ((Real.summable_nat_rpow.mpr (by linarith : 4*δ-2 < -1)).subtype Nat.Prime).mul_left _

/-- The actual local deviations are absolutely summable in a complex
neighborhood of zero shifts, uniformly over their imaginary parts. -/
theorem shiftedPolarPrimeRemainder_sub_one_norm_summable
    (a b : Fin 3 → ℂ) {δ : ℝ} (hδ : δ < 1/4)
    (ha : ∀ i : Fin 3, -δ ≤ (a i).re) (hb : ∀ i : Fin 3, -δ ≤ (b i).re) :
    Summable (fun p : {n : ℕ // Nat.Prime n} => ‖shiftedPolarPrimeRemainder p a b-1‖) := by
  apply (shiftedPolarPrimeMajorant_summable hδ).of_norm_bounded_eventually
  filter_upwards [primePolarGeometricRadius_eventually (by linarith : δ < 1/2)] with p hp
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact shiftedPolarPrimeRemainder_sub_one_bound p a b ha hb hp

/-- Convergence of the genuine shifted arithmetic Euler product. -/
theorem shiftedPolarEulerRest_multipliable
    (a b : Fin 3 → ℂ) {δ : ℝ} (hδ : δ < 1/4)
    (ha : ∀ i : Fin 3, -δ ≤ (a i).re) (hb : ∀ i : Fin 3, -δ ≤ (b i).re) :
    Multipliable (fun p : {n : ℕ // Nat.Prime n} => shiftedPolarPrimeRemainder p a b) := by
  have hs := shiftedPolarPrimeRemainder_sub_one_norm_summable a b hδ ha hb
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hs

end

end Sechstmoment
