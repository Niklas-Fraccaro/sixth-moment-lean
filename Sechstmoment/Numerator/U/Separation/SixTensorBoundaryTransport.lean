import Sechstmoment.Numerator.U.Separation.SixTensorSource
import Sechstmoment.Numerator.U.Sources.Weights.MeasurableSuperposition
import Sechstmoment.Numerator.U.Sources.Weights.SixTensorAdmissibility

/-! Exact transport of the actual sixth Fourier character through every
unit embedding and the source orientation. The main term retained here is
the literal transformed zero mode; native zero-mode invariance is not used. -/
namespace Sechstmoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem a03_unit_coefficient_measurable {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (α : Ω → ℕ → ℂ) (hα : ∀ n, Measurable (fun ν => α ν n)) (n : ℕ) :
    Measurable (fun ν => rectangularUnitCoefficient d (α ν) n) := by
  unfold rectangularUnitCoefficient
  split_ifs
  · exact hα _
  · exact measurable_const

theorem a03SixActualBoundaryBeta_measurable (T B : ℝ) (g : ℝ → ℝ)
    (k : Fin 4 → ℕ) (hB : 0 < B) (n : ℕ) :
    Measurable (fun ν => a03SixActualBoundaryBeta T B g k ν n) := by
  unfold a03SixActualBoundaryBeta boundaryEmbeddedBeta
  apply a03_unit_coefficient_measurable
  intro m
  apply a03_unit_coefficient_measurable
  intro l
  exact a03SixTensorBeta_measurable hB (phaseActualAmplifierCoefficient T g B)
    (phaseActualAmplifierCoefficient_support T g hB) l

theorem phase_normalized_alpha_measurable {Ω : Type*} [MeasurableSpace Ω]
    (q : QuadraticScales) (α β : Ω → ℕ → ℂ)
    (hα : ∀ n, Measurable (fun ν => α ν n))
    (hβ : ∀ n, Measurable (fun ν => β ν n)) (n : ℕ) :
    Measurable (fun ν => phaseNormalizedAlpha q (α ν) (β ν) n) := by
  unfold phaseNormalizedAlpha
  split_ifs
  · exact hα n
  · exact hβ n

theorem phase_normalized_beta_measurable {Ω : Type*} [MeasurableSpace Ω]
    (q : QuadraticScales) (α β : Ω → ℕ → ℂ)
    (hα : ∀ n, Measurable (fun ν => α ν n))
    (hβ : ∀ n, Measurable (fun ν => β ν n)) (n : ℕ) :
    Measurable (fun ν => phaseNormalizedBeta q (α ν) (β ν) n) := by
  unfold phaseNormalizedBeta
  split_ifs
  · exact hβ n
  · exact hα n

theorem phase_normalized_weights_measurable {Ω : Type*} [MeasurableSpace Ω]
    (q : QuadraticScales) (W : Ω → Fin 5 → ℝ → ℂ)
    (hW : ∀ i x, Measurable (fun ν => W ν i x)) (i : Fin 5) (x : ℝ) :
    Measurable (fun ν => phaseNormalizedWeights q (W ν) i x) := by
  unfold phaseNormalizedWeights
  split_ifs <;> unfold phaseSortedWeights
  all_goals
    generalize decide (q.M₂ < q.M₁) = m
    generalize decide (q.N₂ < q.N₁) = n
    cases m <;> cases n <;> fin_cases i <;> simp only [phasePairSwapWeights, phaseSideSwapWeights]
    all_goals first | exact hW 0 x | exact hW 1 x | exact hW 2 x | exact hW 3 x | exact hW 4 x

theorem a03Six_actual_normalized_source_sum (positive : Bool) (T A B H : ℝ)
    (f g : ℝ → ℝ) (k : Fin 4 → ℕ) (ν : A03SixTensorSpace)
    (W : Fin 5 → ℝ → ℂ) (hW : ∀ i, RectangularComplexWeight (W i))
    (hA : 0 < A) (hB : 0 < B) (hH : 0 < H) :
    let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
    rectangularComplexQuadraticSum positive (phaseActualScales A B H k)
      (phaseActualAmplifierCoefficient T f A)
      (a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B)) W =
      rectangularComplexQuadraticSum (phaseNormalizedSign q positive) (phaseNormalizedScales q)
        (phaseNormalizedAlpha q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
        (phaseNormalizedBeta q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
        (phaseNormalizedWeights q W) := by
  dsimp only
  rw [boundaryEmbedded_signed_sum (boundaryActualFlags k) positive (phaseActualScales A B H k)
    (boundaryActual_scales_pos A B H k hA hB hH) _ _ W hW (boundaryActual_flags_low A B H k)]
  exact (phase_normalized_quadratic_sum _ positive _ _ W).symm

theorem a03Six_actual_normalized_source_discrepancy (positive : Bool) (T A B H : ℝ)
    (f g : ℝ → ℝ) (k : Fin 4 → ℕ) (ν : A03SixTensorSpace)
    (W : Fin 5 → ℝ → ℂ) (hW : ∀ i, RectangularComplexWeight (W i))
    (hA : 0 < A) (hB : 0 < B) (hH : 0 < H) :
    let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
    let a := phaseNormalizedAlpha q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν)
    let b := phaseNormalizedBeta q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν)
    let weights := phaseNormalizedWeights q W
    rectangularComplexQuadraticSum positive (phaseActualScales A B H k)
      (phaseActualAmplifierCoefficient T f A)
      (a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B)) W -
      rectangularComplexZeroMode (phaseNormalizedScales q) a b weights =
      rectangularComplexDiscrepancy (phaseNormalizedSign q positive) (phaseNormalizedScales q)
        a b weights := by
  dsimp only
  rw [a03Six_actual_normalized_source_sum positive T A B H f g k ν W hW hA hB hH]
  rfl

theorem a03Six_actual_normalized_source_integral (positive : Bool) (T A B H : ℝ)
    (f g : ℝ → ℝ) (k : Fin 4 → ℕ) (normalizer : A03SixTensorSpace → ℝ)
    (hW : ∀ ν i, RectangularComplexWeight (a03SixTensorWeight normalizer ν i))
    (c : A03SixTensorSpace → ℂ) (hA : 0 < A) (hB : 0 < B) (hH : 0 < H) :
    let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
    (∫ ν, c ν * rectangularComplexQuadraticSum positive (phaseActualScales A B H k)
      (phaseActualAmplifierCoefficient T f A)
      (a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B))
      (a03SixTensorWeight normalizer ν)) =
    ∫ ν, c ν * rectangularComplexQuadraticSum (phaseNormalizedSign q positive)
      (phaseNormalizedScales q)
      (phaseNormalizedAlpha q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
      (phaseNormalizedBeta q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
      (phaseNormalizedWeights q (a03SixTensorWeight normalizer ν)) := by
  dsimp only
  apply integral_congr_ae
  exact ae_of_all volume fun ν => congrArg (fun z : ℂ => c ν * z)
    (a03Six_actual_normalized_source_sum positive T A B H f g k ν _ (hW ν) hA hB hH)

theorem a03Six_actual_normalized_discrepancy_integral (positive : Bool) (T A B H : ℝ)
    (f g : ℝ → ℝ) (k : Fin 4 → ℕ) (normalizer : A03SixTensorSpace → ℝ)
    (hW : ∀ ν i, RectangularComplexWeight (a03SixTensorWeight normalizer ν i))
    (c : A03SixTensorSpace → ℂ) (hA : 0 < A) (hB : 0 < B) (hH : 0 < H) :
    let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
    let a := fun ν => phaseNormalizedAlpha q (boundaryActualAlpha T A f k)
      (a03SixActualBoundaryBeta T B g k ν)
    let b := fun ν => phaseNormalizedBeta q (boundaryActualAlpha T A f k)
      (a03SixActualBoundaryBeta T B g k ν)
    let weights := fun ν => phaseNormalizedWeights q (a03SixTensorWeight normalizer ν)
    (∫ ν, c ν * (rectangularComplexQuadraticSum positive (phaseActualScales A B H k)
      (phaseActualAmplifierCoefficient T f A)
      (a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B))
      (a03SixTensorWeight normalizer ν) -
      rectangularComplexZeroMode (phaseNormalizedScales q) (a ν) (b ν) (weights ν))) =
    ∫ ν, c ν * rectangularComplexDiscrepancy (phaseNormalizedSign q positive)
      (phaseNormalizedScales q) (a ν) (b ν) (weights ν) := by
  dsimp only
  apply integral_congr_ae
  exact ae_of_all volume fun ν => congrArg (fun z : ℂ => c ν * z)
    (a03Six_actual_normalized_source_discrepancy positive T A B H f g k ν _ (hW ν) hA hB hH)

end
end Sechstmoment
