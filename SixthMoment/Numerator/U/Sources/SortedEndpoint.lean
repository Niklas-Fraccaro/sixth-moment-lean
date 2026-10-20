import SixthMoment.Numerator.U.Sources.GlobalAmplifier
import SixthMoment.Numerator.U.ZeroModes.ActualZeroModeBackTransport

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03EndpointNativeSortedZeroMode (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) (normalizer : A03SixTensorSpace → ℝ) (ν : A03SixTensorSpace) : ℂ :=
  let q := phaseActualScales A B H k
  let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
  let m := decide (q'.M₂<q'.M₁)
  let n := decide (q'.N₂<q'.N₁)
  rectangularComplexZeroMode (phasePairSwapScales m n q)
    (phaseActualAmplifierCoefficient T f A)
    (a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B))
    (phasePairSwapWeights m n (a03SixTensorWeight normalizer ν))

def a03EndpointNativeSortedZeroIntegral (kernel : SchwartzMap A03SixTensorSpace ℂ)
    (normalizer : A03SixTensorSpace → ℝ) (T A B H : ℝ) (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) : ℂ :=
  ∫ ν, a03SixTensorCoefficient kernel normalizer ν*
    a03EndpointNativeSortedZeroMode T A B H f g k normalizer ν

theorem a03_actual_endpoint_zero_mode_eq_native_sorted
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs : s<1/2)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4 → ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ normalizer : A03SixTensorSpace → ℝ,
      (∀ ν i, RectangularComplexWeight (a03SixTensorWeight normalizer ν i)) →
      ∀ ν : A03SixTensorSpace,
      a03EndpointNormalizedZeroMode T A B H f g k normalizer ν=
        a03EndpointNativeSortedZeroMode T A B H f g k normalizer ν := by
  filter_upwards [phase_actual_active_near_zero_mode_back_transport ha hab hlen hs f g hf hg]
    with T hback
  intro A B H hA hB hH k hactive normalizer hW ν
  exact hback A B H hA hB hH k hactive
    (phaseActualAmplifierCoefficient T f A)
    (a03SixTensorBeta ν B (phaseActualAmplifierCoefficient T g B))
    (a03SixTensorWeight normalizer ν) (hW ν)

theorem a03_actual_endpoint_zero_integral_eq_native_sorted
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs : s<1/2)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4 → ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ normalizer : A03SixTensorSpace → ℝ,
      (∀ ν i, RectangularComplexWeight (a03SixTensorWeight normalizer ν i)) →
      ∀ kernel : SchwartzMap A03SixTensorSpace ℂ,
      a03EndpointZeroIntegral kernel normalizer T A B H f g k=
        a03EndpointNativeSortedZeroIntegral kernel normalizer T A B H f g k ∧
      (Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
        a03EndpointNormalizedZeroMode T A B H f g k normalizer ν) ↔
      Integrable (fun ν => a03SixTensorCoefficient kernel normalizer ν*
        a03EndpointNativeSortedZeroMode T A B H f g k normalizer ν)) := by
  filter_upwards [a03_actual_endpoint_zero_mode_eq_native_sorted ha hab hlen hs f g hf hg]
    with T hback
  intro A B H hA hB hH k hactive normalizer hW kernel
  have he := hback A B H hA hB hH k hactive normalizer hW
  have hfun : (fun ν => a03SixTensorCoefficient kernel normalizer ν*
      a03EndpointNormalizedZeroMode T A B H f g k normalizer ν)=
      (fun ν => a03SixTensorCoefficient kernel normalizer ν*
        a03EndpointNativeSortedZeroMode T A B H f g k normalizer ν) := by
    funext ν
    rw [he ν]
  refine ⟨?_,by rw [hfun]⟩
  unfold a03EndpointZeroIntegral a03EndpointNativeSortedZeroIntegral
  exact congrArg (fun F : A03SixTensorSpace → ℂ => ∫ ν, F ν) hfun

end
end SixthMoment
