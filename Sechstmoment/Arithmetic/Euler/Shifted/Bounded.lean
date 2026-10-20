import Mathlib.Tactic
import Sechstmoment.Arithmetic.Euler.Shifted.Uniform


namespace Sechstmoment

open Real Complex Filter
open scoped BigOperators Topology

noncomputable section

def shiftedPolarPrimeUniformMajorant (δ : ℝ) (p : {n : ℕ // Nat.Prime n}) : ℝ :=
  let y := (p.val:ℝ)^(2*δ-1)
  if y ≤ 1/2 then 2000000*(p.val:ℝ)^(4*δ-2)
  else (1+y)^9*((1+4*y+y^2)/(1-y)^5)+1

theorem shiftedPolarPrimeRemainder_sub_one_coarse_bound
    (p : {n : ℕ // Nat.Prime n}) (a b : Fin 3 → ℂ) {δ : ℝ} (hδ : δ < 1/2)
    (ha : ∀ i : Fin 3, -δ ≤ (a i).re) (hb : ∀ i : Fin 3, -δ ≤ (b i).re) :
    ‖shiftedPolarPrimeRemainder p a b-1‖ ≤
      (1+(p.val:ℝ)^(2*δ-1))^9 *
        ((1+4*(p.val:ℝ)^(2*δ-1)+((p.val:ℝ)^(2*δ-1))^2)/
          (1-(p.val:ℝ)^(2*δ-1))^5)+1 := by
  let r : ℝ := (p.val:ℝ)^δ
  let y : ℝ := (p.val:ℝ)^(2*δ-1)
  have hp : (0:ℝ) < p.val := by exact_mod_cast p.property.pos
  have hr : 0 ≤ r := Real.rpow_nonneg hp.le _
  have hy : 0 ≤ y := Real.rpow_nonneg hp.le _
  have hy1 : y < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.property.one_lt) (by linarith)
  have habs : ‖y‖ < 1 := by rwa [Real.norm_of_nonneg hy]
  have hD : ‖shiftedDiagonalPrimeSeries p a b‖ ≤ (1+4*y+y^2)/(1-y)^5 := by
    apply tsum_of_norm_bounded (hasSum_d3PrimePower_sq habs)
    intro m
    have h := diagonalPrimeTerm_norm_le hr (primePolarWeights_norm_le p a ha)
      (primePolarWeights_norm_le p b hb) (1/(p.val:ℂ)) m
    simpa only [r, primePolarGeometricRadius] using h
  have hP : ‖shiftedPolarPrimeDivisors p a b‖ ≤ (1+y)^9 := by
    rw [shiftedPolarPrimeDivisors_eq]
    have hw (ij : Fin 3 × Fin 3) :
        ‖primePolarWeights p a ij.1*primePolarWeights p b ij.2*(1/(p.val:ℂ))‖ ≤ y := by
      rw [norm_mul, norm_mul]
      calc
        _ ≤ r*r*‖1/(p.val:ℂ)‖ := by
          gcongr
          · exact primePolarWeights_norm_le p a ha _
          · exact primePolarWeights_norm_le p b hb _
        _ = y := by
          rw [← pow_two]
          exact primePolarGeometricRadius p δ
    simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using
      finitePolarProduct_norm_le Finset.univ _ hy (fun ij _ => hw ij)
  calc
    _ ≤ ‖shiftedPolarPrimeRemainder p a b‖+1 := by
      simpa only [norm_one] using norm_sub_le (shiftedPolarPrimeRemainder p a b) 1
    _ = ‖shiftedPolarPrimeDivisors p a b‖*‖shiftedDiagonalPrimeSeries p a b‖+1 := by
      rw [shiftedPolarPrimeRemainder, norm_mul]
    _ ≤ (1+y)^9*((1+4*y+y^2)/(1-y)^5)+1 := by
      gcongr

theorem shiftedPolarPrimeUniformMajorant_nonneg {δ : ℝ} (hδ : δ < 1/2)
    (p : {n : ℕ // Nat.Prime n}) : 0 ≤ shiftedPolarPrimeUniformMajorant δ p := by
  have hy : 0 ≤ (p.val:ℝ)^(2*δ-1) := Real.rpow_nonneg (by positivity) _
  have hy1 : (p.val:ℝ)^(2*δ-1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.property.one_lt) (by linarith)
  dsimp only [shiftedPolarPrimeUniformMajorant]
  split_ifs <;> positivity

theorem shiftedPolarPrimeUniformMajorant_summable {δ : ℝ} (hδ : δ < 1/4) :
    Summable (shiftedPolarPrimeUniformMajorant δ) := by
  apply (shiftedPolarPrimeMajorant_summable hδ).congr_cofinite
  filter_upwards [primePolarGeometricRadius_eventually (by linarith : δ < 1/2)]
    with p hp
  simp only [shiftedPolarPrimeUniformMajorant, hp, ite_true]

theorem shiftedPolarPrimeRemainder_sub_one_uniform_bound
    (p : {n : ℕ // Nat.Prime n}) (a b : Fin 3 → ℂ) {δ : ℝ} (hδ : δ < 1/2)
    (ha : ∀ i : Fin 3, -δ ≤ (a i).re) (hb : ∀ i : Fin 3, -δ ≤ (b i).re) :
    ‖shiftedPolarPrimeRemainder p a b-1‖ ≤ shiftedPolarPrimeUniformMajorant δ p := by
  dsimp only [shiftedPolarPrimeUniformMajorant]
  split_ifs with hp
  · exact shiftedPolarPrimeRemainder_sub_one_bound p a b ha hb hp
  · exact shiftedPolarPrimeRemainder_sub_one_coarse_bound p a b hδ ha hb

theorem shiftedPolarEulerRest_norm_uniform_bound
    (a b : Fin 3 → ℂ) {δ : ℝ} (hδ : δ < 1/4)
    (ha : ∀ i : Fin 3, -δ ≤ (a i).re) (hb : ∀ i : Fin 3, -δ ≤ (b i).re) :
    ‖shiftedPolarEulerRest a b‖ ≤
      Real.exp (∑' p : {n : ℕ // Nat.Prime n}, shiftedPolarPrimeUniformMajorant δ p) := by
  have hs := shiftedPolarPrimeUniformMajorant_summable hδ
  have hn (p : {n : ℕ // Nat.Prime n}) : 0 ≤ shiftedPolarPrimeUniformMajorant δ p :=
    shiftedPolarPrimeUniformMajorant_nonneg (by linarith) p
  have hlim := (shiftedPolarEulerRest_multipliable a b hδ ha hb).hasProd.norm
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro s
  calc
    _ ≤ ∏ p ∈ s, (1+shiftedPolarPrimeUniformMajorant δ p) := by
      apply Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
      intro p _
      calc
        _ = ‖1+(shiftedPolarPrimeRemainder p a b-1)‖ := by congr 1; ring
        _ ≤ 1+‖shiftedPolarPrimeRemainder p a b-1‖ := by
          simpa only [norm_one] using norm_add_le (1:ℂ) (shiftedPolarPrimeRemainder p a b-1)
        _ ≤ _ := add_le_add le_rfl
          (shiftedPolarPrimeRemainder_sub_one_uniform_bound p a b (by linarith) ha hb)
    _ ≤ Real.exp (∑ p ∈ s, shiftedPolarPrimeUniformMajorant δ p) :=
      Real.prod_one_add_le_exp_sum s hn
    _ ≤ _ := Real.exp_le_exp.mpr (hs.sum_le_tsum s (fun p _ => hn p))

end

end Sechstmoment
