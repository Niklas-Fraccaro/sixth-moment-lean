import Mathlib.Tactic
import Sechstmoment.Arithmetic.Euler.Shifted.Uniform


namespace Sechstmoment

open Real Complex Filter
open scoped BigOperators Topology

noncomputable section

theorem triplePrimePowerCoefficient_differentiableOn
    {U : Set ℂ} (a : ℂ → Fin 3 → ℂ)
    (ha : ∀ i : Fin 3, DifferentiableOn ℂ (fun z => a z i) U) (m : ℕ) :
    DifferentiableOn ℂ (fun z => triplePrimePowerCoefficient (a z) m) U := by
  unfold triplePrimePowerCoefficient
  apply DifferentiableOn.fun_sum
  intro i _
  apply DifferentiableOn.fun_sum
  intro j _
  exact (((ha 0).pow i).mul ((ha 1).pow j)).mul ((ha 2).pow (m-i-j))

theorem shiftedDiagonalPrimeSeries_differentiableOn
    (p : {n : ℕ // Nat.Prime n}) {U : Set ℂ} (hU : IsOpen U)
    (a b : ℂ → Fin 3 → ℂ) {δ : ℝ} (hδ : δ < 1/2)
    (ha : ∀ i : Fin 3, DifferentiableOn ℂ (fun z => a z i) U)
    (hb : ∀ i : Fin 3, DifferentiableOn ℂ (fun z => b z i) U)
    (haδ : ∀ z ∈ U, ∀ i : Fin 3, -δ ≤ (a z i).re)
    (hbδ : ∀ z ∈ U, ∀ i : Fin 3, -δ ≤ (b z i).re) :
    DifferentiableOn ℂ (fun z => shiftedDiagonalPrimeSeries p (a z) (b z)) U := by
  let r : ℝ := (p.val:ℝ)^δ
  let y : ℝ := r^2*‖1/(p.val:ℂ)‖
  have hp : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hy : ‖y‖ < 1 := by
    rw [Real.norm_of_nonneg (by dsimp [y]; positivity)]
    dsimp [y, r]
    rw [primePolarGeometricRadius]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt)
      (by linarith)
  unfold shiftedDiagonalPrimeSeries
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun m : ℕ => (d3PrimePowerCoefficient m:ℝ)^2*y^m)
    (hasSum_d3PrimePower_sq hy).summable
  · intro m
    have hA := triplePrimePowerCoefficient_differentiableOn
      (fun z => primePolarWeights p (a z))
      (fun i => (ha i).neg.const_cpow (.inl hp)) m
    have hB := triplePrimePowerCoefficient_differentiableOn
      (fun z => primePolarWeights p (b z))
      (fun i => (hb i).neg.const_cpow (.inl hp)) m
    exact (hA.mul hB).mul (differentiableOn_const _)
  · exact hU
  · intro m z hz
    exact diagonalPrimeTerm_norm_le hr
      (primePolarWeights_norm_le p (a z) (haδ z hz))
      (primePolarWeights_norm_le p (b z) (hbδ z hz)) _ m

theorem shiftedPolarPrimeDivisors_differentiableOn
    (p : {n : ℕ // Nat.Prime n}) {U : Set ℂ} (a b : ℂ → Fin 3 → ℂ)
    (ha : ∀ i : Fin 3, DifferentiableOn ℂ (fun z => a z i) U)
    (hb : ∀ i : Fin 3, DifferentiableOn ℂ (fun z => b z i) U) :
    DifferentiableOn ℂ (fun z => shiftedPolarPrimeDivisors p (a z) (b z)) U := by
  unfold shiftedPolarPrimeDivisors
  apply DifferentiableOn.fun_finsetProd
  intro ij _
  have hp : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  exact (differentiableOn_const _).sub
    ((((differentiableOn_const _).add (ha ij.1)).add
      (hb ij.2)).neg.const_cpow (.inl hp))

theorem shiftedPolarEulerRest_differentiableOn
    {U : Set ℂ} (hU : IsOpen U) (a b : ℂ → Fin 3 → ℂ)
    {δ : ℝ} (hδ : δ < 1/4)
    (ha : ∀ i : Fin 3, DifferentiableOn ℂ (fun z => a z i) U)
    (hb : ∀ i : Fin 3, DifferentiableOn ℂ (fun z => b z i) U)
    (haδ : ∀ z ∈ U, ∀ i : Fin 3, -δ < (a z i).re)
    (hbδ : ∀ z ∈ U, ∀ i : Fin 3, -δ < (b z i).re) :
    DifferentiableOn ℂ (fun z => shiftedPolarEulerRest (a z) (b z)) U := by
  have hmap : Set.MapsTo (fun z => (a z, b z)) U (polarShiftDomain δ) :=
    fun z hz => ⟨haδ z hz, hbδ z hz⟩
  have hcts : ContinuousOn (fun z => (a z, b z)) U :=
    (continuousOn_pi.mpr (fun i => (ha i).continuousOn)).prodMk
      (continuousOn_pi.mpr (fun i => (hb i).continuousOn))
  have hprod := (shiftedPolarEulerRest_hasProdLocallyUniformlyOn hδ).comp
    (fun z => (a z, b z)) hmap hcts
  apply hprod.differentiableOn _ hU
  apply Eventually.of_forall
  intro s
  apply DifferentiableOn.fun_finsetProd
  intro p _
  exact (shiftedPolarPrimeDivisors_differentiableOn p a b ha hb).mul
    (shiftedDiagonalPrimeSeries_differentiableOn p hU a b (by linarith)
      ha hb (fun z hz i => (haδ z hz i).le) (fun z hz i => (hbδ z hz i).le))

end

end Sechstmoment
