import Sechstmoment.Numerator.U.ZeroModes.SixTensorZeroMode
import Sechstmoment.Numerator.U.ZeroModes.SoftSourceOrientation

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology FourierTransform
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03SoftEndpointNormalizedSum (positive : Bool) (T A B H : ℝ) (f g : ℝ→ℝ)
    (k : Fin 4→ℕ) (normalizer : A03SixTensorSpace→ℝ) (ν : A03SixTensorSpace) : ℂ :=
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  rectangularComplexQuadraticSum (a03SoftSourceOrientedSign q positive) (a03SoftSourceOrientedScales q)
    (a03SoftSourceOrientedAlpha q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
    (a03SoftSourceOrientedBeta q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
    (a03SoftSourceOrientedWeights q (a03SixTensorWeight normalizer ν))

def a03SoftEndpointNormalizedZeroMode (T A B H : ℝ) (f g : ℝ→ℝ)
    (k : Fin 4→ℕ) (normalizer : A03SixTensorSpace→ℝ) (ν : A03SixTensorSpace) : ℂ :=
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  rectangularComplexZeroMode (a03SoftSourceOrientedScales q)
    (a03SoftSourceOrientedAlpha q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
    (a03SoftSourceOrientedBeta q (boundaryActualAlpha T A f k) (a03SixActualBoundaryBeta T B g k ν))
    (a03SoftSourceOrientedWeights q (a03SixTensorWeight normalizer ν))

def a03SoftEndpointNormalizedDiscrepancy (positive : Bool) (T A B H : ℝ) (f g : ℝ→ℝ)
    (k : Fin 4→ℕ) (normalizer : A03SixTensorSpace→ℝ) (ν : A03SixTensorSpace) : ℂ :=
  a03SoftEndpointNormalizedSum positive T A B H f g k normalizer ν-
    a03SoftEndpointNormalizedZeroMode T A B H f g k normalizer ν

def a03SoftEndpointZeroIntegral (kernel : SchwartzMap A03SixTensorSpace ℂ)
    (normalizer : A03SixTensorSpace→ℝ) (T A B H : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ) : ℂ :=
  ∫ ν, a03SixTensorCoefficient kernel normalizer ν*a03SoftEndpointNormalizedZeroMode T A B H f g k normalizer ν

def a03EndpointPhysicalUnsortedZeroMode (F : A03SixTensorSpace→ℂ) (T A B H : ℝ)
    (f g : ℝ→ℝ) (k : Fin 4→ℕ) : ℂ :=
  a03SixTensorPhysicalZeroMode F false false (phaseActualScales A B H k)
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)

theorem a03_soft_source_zero_eq_native_discrete_units
    (T A B H : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) (hk₁ : k 1≠0) (hk₃ : k 3≠0)
    (normalizer : A03SixTensorSpace→ℝ)
    (hW : ∀ ν i,RectangularComplexWeight (a03SixTensorWeight normalizer ν i))
    (ν : A03SixTensorSpace) :
    a03SoftEndpointNormalizedZeroMode T A B H f g k normalizer ν=
      rectangularComplexZeroMode (phaseActualScales A B H k)
        (phaseActualAmplifierCoefficient T f A)
        (a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B))
        (a03SixTensorWeight normalizer ν) := by
  unfold a03SoftEndpointNormalizedZeroMode
  rw [a03_soft_source_oriented_zero]
  have hm : boundaryActualFlags k 1=false := by simp [boundaryActualFlags,hk₁]
  have hn : boundaryActualFlags k 3=false := by simp [boundaryActualFlags,hk₃]
  exact (boundaryEmbedded_discrete_complex_zero_mode (boundaryActualFlags k) hm hn
    (phaseActualScales A B H k) (boundaryActual_scales_pos A B H k hA hB hH)
    (phaseActualAmplifierCoefficient T f A)
    (a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B))
    (a03SixTensorWeight normalizer ν) (hW ν)
    (fun hf => by simpa [phaseActualScales,boundaryActualFlags,QuadraticScales.size,rectangularUnitCoordinate] using
      (boundaryActual_flags_low A B H k) 0 hf)
    (fun hf => by simpa [phaseActualScales,boundaryActualFlags,QuadraticScales.size,rectangularUnitCoordinate] using
      (boundaryActual_flags_low A B H k) 2 hf)).symm

theorem a03_soft_endpoint_zero_integral_eq_uncut_unsorted_physical
    (kernel : SchwartzMap A03SixTensorSpace ℂ) (F : A03SixTensorSpace→ℂ)
    (hgraph : ∀ y,kernel y=a03TensorLogCutoff y*F y)
    (normalizer : A03SixTensorSpace→ℝ) (hm : Measurable normalizer) (hn : ∀ ν,0<normalizer ν)
    (hc : Integrable (a03SixTensorCoefficient kernel normalizer))
    {D : ℝ} (hD : 0≤D) (hweight : ∀ ν i x,‖a03SixTensorWeight normalizer ν i x‖≤D)
    (T A B H : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) (hk₁ : k 1≠0) (hk₃ : k 3≠0) :
    Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
      a03SoftEndpointNormalizedZeroMode T A B H f g k normalizer ν) ∧
    a03SoftEndpointZeroIntegral kernel normalizer T A B H f g k=
      a03EndpointPhysicalUnsortedZeroMode F T A B H f g k := by
  have he (ν : A03SixTensorSpace) := a03_soft_source_zero_eq_native_discrete_units T A B H f g k
    hA hB hH hk₁ hk₃ normalizer (a03SixTensorWeight_complexWeight normalizer) ν
  have hp := a03SixTensor_native_zero_reconstruction kernel normalizer hm hn hc hD hweight
    false false (phaseActualScales A B H k) hB (boundaryActual_scale_pos (k 1))
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
  refine ⟨hp.1.congr (ae_of_all _ (fun ν => congrArg
    (fun z : ℂ => a03SixTensorCoefficient kernel normalizer ν*z) (he ν).symm)),?_⟩
  calc
    _=a03EndpointPhysicalUnsortedZeroMode kernel T A B H f g k := by
      unfold a03SoftEndpointZeroIntegral a03EndpointPhysicalUnsortedZeroMode
      simp_rw [he]
      exact hp.2
    _=a03EndpointPhysicalUnsortedZeroMode F T A B H f g k :=
      a03SixTensorPhysicalZeroMode_remove_log_cutoff kernel F hgraph false false
        (phaseActualScales A B H k) hB _ _ (phaseActualAmplifierCoefficient_support T g hB)

end
end Sechstmoment
