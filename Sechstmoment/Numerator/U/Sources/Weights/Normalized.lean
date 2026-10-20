import Sechstmoment.Numerator.U.Separation.ShapeActualPowerNear

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section

theorem phase_actual_normalized_source_sum (positive : Bool) (T A B H : ℝ)
    (f g : ℝ → ℝ) (k : Fin 4 → ℕ) (α : MomentShifts) (z : ℂ) (l : ℕ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) :
    let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
    rectangularComplexQuadraticSum positive (phaseActualScales A B H k)
      (phaseActualAmplifierCoefficient T f A)
      (phaseAdjustedBeta (phaseActualScales A B H k) (phaseActualAmplifierCoefficient T g B) l)
      (phaseFiveWeights α z l)=
    rectangularComplexQuadraticSum (phaseNormalizedSign q positive) (phaseNormalizedScales q)
      (phaseNormalizedAlpha q (boundaryActualAlpha T A f k) (boundaryActualBeta T A B H g k l))
      (phaseNormalizedBeta q (boundaryActualAlpha T A f k) (boundaryActualBeta T A B H g k l))
      (phaseNormalizedWeights q (phaseFiveWeights α z l)) := by
  dsimp only
  rw [boundaryActual_source_sum positive T A B H f g k α z l hA hB hH]
  exact (phase_normalized_quadratic_sum _ positive _ _ _).symm

theorem phase_actual_normalized_source_discrepancy (positive : Bool) (T A B H : ℝ)
    (f g : ℝ → ℝ) (k : Fin 4 → ℕ) (α : MomentShifts) (z : ℂ) (l : ℕ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) :
    let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
    let A' := phaseNormalizedAlpha q (boundaryActualAlpha T A f k) (boundaryActualBeta T A B H g k l)
    let B' := phaseNormalizedBeta q (boundaryActualAlpha T A f k) (boundaryActualBeta T A B H g k l)
    let W := phaseNormalizedWeights q (phaseFiveWeights α z l)
    rectangularComplexQuadraticSum positive (phaseActualScales A B H k)
      (phaseActualAmplifierCoefficient T f A)
      (phaseAdjustedBeta (phaseActualScales A B H k) (phaseActualAmplifierCoefficient T g B) l)
      (phaseFiveWeights α z l)-rectangularComplexZeroMode (phaseNormalizedScales q) A' B' W=
    rectangularComplexDiscrepancy (phaseNormalizedSign q positive) (phaseNormalizedScales q) A' B' W := by
  dsimp only
  rw [phase_actual_normalized_source_sum positive T A B H f g k α z l hA hB hH]
  rfl

end
end Sechstmoment
