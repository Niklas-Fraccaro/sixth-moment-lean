import Sechstmoment.Numerator.U.Separation.Tensor.DualKernel
import Sechstmoment.Numerator.U.Separation.Tensor.MellinBridge
import Sechstmoment.Numerator.U.Sources.Weights.TensorParameters

namespace Sechstmoment
open Complex Real Source MeasureTheory Set
open scoped ContDiff BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem a03_tensor_cutoff_source_summand (q : QuadraticScales) (n : Fin 7 → ℕ)
    (α β : ℕ → ℂ) (F : A03SixTensorSpace → ℂ)
    (hβ : ∀ b, β b ≠ 0 → rectangularSmoothBlockWeight ((b : ℝ) / q.B) ≠ 0) :
    α (n 0) * β (n 1) *
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments q n j) : ℂ)) *
        (a03TensorLogCutoff (a03SixTensorLogPoint (a03SixSourceArguments q n)) *
          F (a03SixTensorLogPoint (a03SixSourceArguments q n))) =
      α (n 0) * β (n 1) *
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments q n j) : ℂ)) *
        F (a03SixTensorLogPoint (a03SixSourceArguments q n)) := by
  by_cases hb : β (n 1) = 0
  · simp only [hb, mul_zero, zero_mul]
  by_cases hw : (∏ j : Fin 5,
      (rectangularSmoothBlockWeight (rectangularWeightArguments q n j) : ℂ)) = 0
  · simp only [hw, mul_zero, zero_mul]
  rw [a03TensorLogCutoff_logPoint_one (a03SixSourceArguments_smooth_support q n (hβ _ hb) hw), one_mul]

theorem a03_tensor_cutoff_finite_signed_source_reconstruction
    (f : SchwartzMap A03SixTensorSpace ℂ) (F : A03SixTensorSpace → ℂ)
    (hgraph : ∀ y, f y = a03TensorLogCutoff y * F y)
    (normalizer : A03SixTensorSpace → ℝ) (hm : Measurable normalizer)
    (hn : ∀ ν, 0 < normalizer ν) (hc : Integrable (a03SixTensorCoefficient f normalizer))
    {D : ℝ} (hD : 0 ≤ D) (hW : ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖ ≤ D)
    (positive : Bool) (q : QuadraticScales) (hB : 0 < q.B) (α β : ℕ → ℂ)
    (hβ : ∀ b, β b ≠ 0 → rectangularSmoothBlockWeight ((b : ℝ) / q.B) ≠ 0) :
    (∫ ν, a03SixTensorCoefficient f normalizer ν * rectangularComplexQuadraticSum positive q α
      (a03SixTensorBeta ν q.B β) (a03SixTensorWeight normalizer ν)) =
      ∑ n ∈ quadraticIndexSet q, if signedQuadraticRelation positive n then
        α (n 0) * β (n 1) *
          (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments q n j) : ℂ)) *
          F (a03SixTensorLogPoint (a03SixSourceArguments q n)) else 0 := by
  rw [a03SixTensor_finite_signed_source_reconstruction f normalizer hm hn hc hD hW positive q hB α β]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hr : signedQuadraticRelation positive n
  · simp only [hr, ite_true, hgraph]
    exact a03_tensor_cutoff_source_summand q n α β F hβ
  · simp only [hr, ite_false]

private theorem actual_beta_smooth_nonzero (T B : ℝ) (g : ℝ → ℝ) :
    ∀ b, phaseActualAmplifierCoefficient T g B b ≠ 0 →
      rectangularSmoothBlockWeight ((b : ℝ) / B) ≠ 0 := by
  intro b hb hz
  apply hb
  simp only [phaseActualAmplifierCoefficient, hz, Complex.ofReal_zero, zero_mul]

theorem a03_actual_tensor_finite_signed_source_reconstruction
    (T A B H c ε : ℝ) (σ α : MomentShifts) (v : ℝ) (k : Fin 4 → ℕ)
    (positive : Bool) (f g : ℝ → ℝ) (Φ : ℝ → ℂ) (hB : 0 < B)
    (kernel : SchwartzMap A03SixTensorSpace ℂ)
    (hgraph : ∀ y, kernel y = a03TensorLogCutoff y *
      a03ActualTensorNormalizedKernel Φ c ε (phaseActualNearTensorData T σ α v A B H k positive) y)
    (normalizer : A03SixTensorSpace → ℝ) (hm : Measurable normalizer)
    (hn : ∀ ν, 0 < normalizer ν) (hc : Integrable (a03SixTensorCoefficient kernel normalizer))
    {D : ℝ} (hD : 0 ≤ D) (hW : ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖ ≤ D) :
    (∫ ν, a03SixTensorCoefficient kernel normalizer ν *
      rectangularComplexQuadraticSum positive (phaseActualScales A B H k)
        (phaseActualAmplifierCoefficient T f A)
        (a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B))
        (a03SixTensorWeight normalizer ν)) =
      ∑ n ∈ quadraticIndexSet (phaseActualScales A B H k), if signedQuadraticRelation positive n then
        phaseActualAmplifierCoefficient T f A (n 0) *
          phaseActualAmplifierCoefficient T g B (n 1) *
          (∏ j : Fin 5, (rectangularSmoothBlockWeight
            (rectangularWeightArguments (phaseActualScales A B H k) n j) : ℂ)) *
          a03ActualTensorNormalizedKernel Φ c ε
            (phaseActualNearTensorData T σ α v A B H k positive)
            (a03SixTensorLogPoint (a03SixSourceArguments (phaseActualScales A B H k) n)) else 0 := by
  exact a03_tensor_cutoff_finite_signed_source_reconstruction kernel _ hgraph normalizer hm hn hc
    hD hW positive (phaseActualScales A B H k) hB
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
    (actual_beta_smooth_nonzero T B g)

theorem a03_actual_dual_tensor_finite_signed_source_reconstruction
    (T A B H c ε : ℝ) (σ α : MomentShifts) (v : ℝ) (k : Fin 4 → ℕ)
    (positive : Bool) (f g : ℝ → ℝ) (Φ : ℝ → ℂ) (hB : 0 < B)
    (kernel : SchwartzMap A03SixTensorSpace ℂ)
    (hgraph : ∀ y, kernel y = a03TensorLogCutoff y *
      a03ActualDualTensorNormalizedKernel Φ c ε (phaseActualNearTensorData T σ α v A B H k positive) y)
    (normalizer : A03SixTensorSpace → ℝ) (hm : Measurable normalizer)
    (hn : ∀ ν, 0 < normalizer ν) (hc : Integrable (a03SixTensorCoefficient kernel normalizer))
    {D : ℝ} (hD : 0 ≤ D) (hW : ∀ ν i x, ‖a03SixTensorWeight normalizer ν i x‖ ≤ D) :
    (∫ ν, a03SixTensorCoefficient kernel normalizer ν *
      rectangularComplexQuadraticSum positive (phaseActualScales A B H k)
        (phaseActualAmplifierCoefficient T f A)
        (a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B))
        (a03SixTensorWeight normalizer ν)) =
      ∑ n ∈ quadraticIndexSet (phaseActualScales A B H k), if signedQuadraticRelation positive n then
        phaseActualAmplifierCoefficient T f A (n 0) *
          phaseActualAmplifierCoefficient T g B (n 1) *
          (∏ j : Fin 5, (rectangularSmoothBlockWeight
            (rectangularWeightArguments (phaseActualScales A B H k) n j) : ℂ)) *
          a03ActualDualTensorNormalizedKernel Φ c ε
            (phaseActualNearTensorData T σ α v A B H k positive)
            (a03SixTensorLogPoint (a03SixSourceArguments (phaseActualScales A B H k) n)) else 0 := by
  exact a03_tensor_cutoff_finite_signed_source_reconstruction kernel _ hgraph normalizer hm hn hc
    hD hW positive (phaseActualScales A B H k) hB
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
    (actual_beta_smooth_nonzero T B g)

end
end Sechstmoment
