import Sechstmoment.Numerator.U.Sources.Weights.Superposition

/-! Exact finite quadratic reconstruction of an integrable tensor kernel.
No new discrepancy or source bound is postulated. -/
namespace Sechstmoment
open Source MeasureTheory Set
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def phaseIntegralTensorKernel {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c : Ω → ℂ) (W : Ω → Fin 5 → ℝ → ℂ) (x : Fin 5 → ℝ) : ℂ :=
  ∫ ν, c ν*∏ i, W ν i (x i) ∂μ

theorem phase_tensor_product_norm_le {Ω : Type*} (W : Ω → Fin 5 → ℝ → ℂ)
    {D : ℝ} (_hD : 0 ≤ D) (hW : ∀ ν i x, ‖W ν i x‖ ≤ D)
    (ν : Ω) (x : Fin 5 → ℝ) : ‖∏ i, W ν i (x i)‖ ≤ D^5 := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _i : Fin 5, D := Finset.prod_le_prod₀
      (fun i _ => norm_nonneg (W ν i (x i))) (fun i _ => hW ν i (x i))
    _ = _ := by simp

theorem phase_tensor_product_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : Ω → ℂ) (hc : Integrable c μ)
    (W : Ω → Fin 5 → ℝ → ℂ)
    (hWm : ∀ i x, AEStronglyMeasurable (fun ν => W ν i x) μ)
    {D : ℝ} (hD : 0 ≤ D) (hW : ∀ ν i x, ‖W ν i x‖ ≤ D)
    (x : Fin 5 → ℝ) : Integrable (fun ν => c ν*∏ i, W ν i (x i)) μ := by
  have hm : AEStronglyMeasurable (fun ν => ∏ i, W ν i (x i)) μ := by
    simp only [Fin.prod_univ_five]
    exact ((((hWm 0 (x 0)).mul (hWm 1 (x 1))).mul
      (hWm 2 (x 2))).mul (hWm 3 (x 3))).mul (hWm 4 (x 4))
  apply (hc.norm.const_mul (D^5)).mono' (hc.aestronglyMeasurable.mul hm)
  apply ae_of_all μ
  intro ν
  change ‖c ν*(∏ i, W ν i (x i))‖ ≤ D^5*‖c ν‖
  rw [norm_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (phase_tensor_product_norm_le W hD hW ν x) (norm_nonneg (c ν))

/-- Integrating the literal source sum reconstructs the coupled kernel
exactly, including every signed integer tuple in its original finite set. -/
theorem phase_integral_quadratic_tensor_kernel {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : Ω → ℂ) (hc : Integrable c μ)
    (W : Ω → Fin 5 → ℝ → ℂ)
    (hWm : ∀ i x, AEStronglyMeasurable (fun ν => W ν i x) μ)
    {D : ℝ} (hD : 0 ≤ D) (hW : ∀ ν i x, ‖W ν i x‖ ≤ D)
    (positive : Bool) (q : QuadraticScales) (α β : ℕ → ℂ) :
    (∫ ν, c ν*rectangularComplexQuadraticSum positive q α β (W ν) ∂μ) =
      ∑ n∈quadraticIndexSet q, if signedQuadraticRelation positive n then
        α (n 0)*β (n 1)*phaseIntegralTensorKernel μ c W
          (rectangularWeightArguments q n) else 0 := by
  let F (n : Fin 7 → ℕ) (ν : Ω) : ℂ :=
    if signedQuadraticRelation positive n then
      (α (n 0)*β (n 1))*(c ν*∏ i, W ν i (rectangularWeightArguments q n i)) else 0
  have hF (n : Fin 7 → ℕ) : Integrable (F n) μ := by
    by_cases hn : signedQuadraticRelation positive n
    · simpa only [F, hn, ite_true] using
        (phase_tensor_product_integrable μ c hc W hWm hD hW
          (rectangularWeightArguments q n)).const_mul (α (n 0)*β (n 1))
    · simp [F, hn]
  calc
    _ = ∫ ν, ∑ n∈quadraticIndexSet q, F n ν ∂μ := by
      apply integral_congr_ae
      apply ae_of_all μ
      intro ν
      dsimp only
      unfold rectangularComplexQuadraticSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : signedQuadraticRelation positive n
      · simp only [F, hn, ite_true]
        ring
      · simp only [F, hn, ite_false, mul_zero]
    _ = ∑ n∈quadraticIndexSet q, ∫ ν, F n ν ∂μ :=
      integral_finsetSum _ (fun n _ => hF n)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : signedQuadraticRelation positive n
      · simp only [F, hn, ite_true, phaseIntegralTensorKernel, integral_const_mul]
      · simp only [F, hn, ite_false, integral_zero]

end
end Sechstmoment
