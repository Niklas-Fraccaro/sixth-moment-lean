import Sechstmoment.Certificate.Profiles.Definitions
import Sechstmoment.Certificate.Profiles.KernelContinuity
import Sechstmoment.Certificate.Profiles.ProductLimit


namespace Sechstmoment

open MeasureTheory Set Filter
open scoped Topology
noncomputable section

set_option maxHeartbeats 2000000

theorem p02ProfilePoint_integral_fubini (f : P02ProfilePoint → ℝ)
    (hf : Integrable f ((volume.prod volume).prod (volume.prod volume))) :
    (∫ z : P02ProfilePoint, f z ∂((volume.prod volume).prod (volume.prod volume))) =
      ∫ a : ℝ, ∫ b : ℝ, ∫ c : ℝ, ∫ d : ℝ, f ((a, b), (c, d)) := by
  rw [integral_prod _ hf, integral_prod _ hf.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hf.prod_right_ae] with a ha
  apply integral_congr_ae
  filter_upwards [ha] with b hb
  exact integral_prod _ hb

private def profileIntegrabilityArguments (z : P02ProfilePoint) : Fin 4 → ℝ :=
  ![z.1.1, z.1.2, z.2.1, z.2.2]

private theorem profileIntegrabilityArguments_continuous :
    Continuous profileIntegrabilityArguments := by
  unfold profileIntegrabilityArguments
  fun_prop

private theorem profileIntegrabilityArguments_nonneg {z : P02ProfilePoint}
    (hz : z ∈ p02ProfileBox 1) : ∀ i, 0 ≤ profileIntegrabilityArguments z i := by
  intro i
  fin_cases i
  · exact hz.1.1.1
  · exact hz.1.2.1
  · exact hz.2.1.1
  · exact hz.2.2.1

theorem certificateFeatureProfileIntegral_integrable (n : ℕ) (hn : 0 < n)
    {x y : Finite.Feature} (hx : x ∈ Finite.features) (hy : y ∈ Finite.features)
    (F : (Fin 4 → ℝ) → ℝ) (hF : ContinuousOn F {z | ∀ i, 0 ≤ z i}) :
    Integrable (fun z : P02ProfilePoint =>
      certificateEndpointProfile x.typ (realEndpoint x.A) n z.1.1 *
      certificateEndpointProfile x.typ (realEndpoint x.B) n z.1.2 *
      certificateEndpointProfile y.typ (realEndpoint y.A) n z.2.1 *
      certificateEndpointProfile y.typ (realEndpoint y.B) n z.2.2 *
        F ![z.1.1, z.1.2, z.2.1, z.2.2])
      ((volume.prod volume).prod (volume.prod volume)) := by
  obtain ⟨hxA, hxB⟩ := certificateFeature_endpoint_geometry hx
  obtain ⟨hyA, hyB⟩ := certificateFeature_endpoint_geometry hy
  let ρ : Fin 4 → ℝ → ℝ :=
    ![certificateEndpointProfile x.typ (realEndpoint x.A) n,
      certificateEndpointProfile x.typ (realEndpoint x.B) n,
      certificateEndpointProfile y.typ (realEndpoint y.A) n,
      certificateEndpointProfile y.typ (realEndpoint y.B) n]
  have hi : ∀ i, Integrable (ρ i) := by
    intro i
    fin_cases i
    · exact certificateEndpointProfile_integrable _ hxA hn
    · exact certificateEndpointProfile_integrable _ hxB hn
    · exact certificateEndpointProfile_integrable _ hyA hn
    · exact certificateEndpointProfile_integrable _ hyB hn
  have hs : ∀ i, Function.support (ρ i) ⊆ Icc (0 : ℝ) 1 := by
    intro i
    fin_cases i
    · exact certificateEndpointProfile_support _ hxA hn
    · exact certificateEndpointProfile_support _ hxB hn
    · exact certificateEndpointProfile_support _ hyA hn
    · exact certificateEndpointProfile_support _ hyB hn
  have hg : ContinuousOn (fun z => F (profileIntegrabilityArguments z)) (p02ProfileBox 1) :=
    hF.comp profileIntegrabilityArguments_continuous.continuousOn
      (fun z hz => profileIntegrabilityArguments_nonneg hz)
  have h := profileProductAverage4_integrable (by norm_num : (0 : ℝ) ≤ 1)
    ρ hi hs _ hg
  apply h.congr
  filter_upwards [] with z
  symm
  change
    certificateEndpointProfile x.typ (realEndpoint x.A) n z.1.1 *
    certificateEndpointProfile x.typ (realEndpoint x.B) n z.1.2 *
    certificateEndpointProfile y.typ (realEndpoint y.A) n z.2.1 *
    certificateEndpointProfile y.typ (realEndpoint y.B) n z.2.2 *
      F ![z.1.1, z.1.2, z.2.1, z.2.2] =
    (certificateEndpointProfile x.typ (realEndpoint x.A) n z.1.1 *
    certificateEndpointProfile x.typ (realEndpoint x.B) n z.1.2) *
    (certificateEndpointProfile y.typ (realEndpoint y.A) n z.2.1 *
    certificateEndpointProfile y.typ (realEndpoint y.B) n z.2.2) *
      F ![z.1.1, z.1.2, z.2.1, z.2.2]
  ring

theorem certificateFeatureProfileIntegral_fubini (n : ℕ) (hn : 0 < n)
    {x y : Finite.Feature} (hx : x ∈ Finite.features) (hy : y ∈ Finite.features)
    (F : (Fin 4 → ℝ) → ℝ) (hF : ContinuousOn F {z | ∀ i, 0 ≤ z i}) :
    certificateFeatureProfileIntegral n x y F =
      ∫ a : ℝ, ∫ b : ℝ, ∫ c : ℝ, ∫ d : ℝ,
        certificateEndpointProfile x.typ (realEndpoint x.A) n a *
        certificateEndpointProfile x.typ (realEndpoint x.B) n b *
        certificateEndpointProfile y.typ (realEndpoint y.A) n c *
        certificateEndpointProfile y.typ (realEndpoint y.B) n d * F ![a, b, c, d] := by
  unfold certificateFeatureProfileIntegral
  exact p02ProfilePoint_integral_fubini _
    (certificateFeatureProfileIntegral_integrable n hn hx hy F hF)

theorem certificateProfileGramZero_integrable (n : ℕ) (hn : 0 < n)
    {x y : Finite.Feature} (hx : x ∈ Finite.features) (hy : y ∈ Finite.features) :
    Integrable (fun z : P02ProfilePoint =>
      certificateEndpointProfile x.typ (realEndpoint x.A) n z.1.1 *
      certificateEndpointProfile x.typ (realEndpoint x.B) n z.1.2 *
      certificateEndpointProfile y.typ (realEndpoint y.A) n z.2.1 *
      certificateEndpointProfile y.typ (realEndpoint y.B) n z.2.2 *
        certificateGramZeroKernel x y ![z.1.1, z.1.2, z.2.1, z.2.2])
      ((volume.prod volume).prod (volume.prod volume)) :=
  certificateFeatureProfileIntegral_integrable n hn hx hy _
    (certificateGramZeroKernel_continuousOn_nonneg x y)

theorem certificateProfileGramMinus_integrable (n : ℕ) (hn : 0 < n)
    {x y : Finite.Feature} (hx : x ∈ Finite.features) (hy : y ∈ Finite.features) :
    Integrable (fun z : P02ProfilePoint =>
      certificateEndpointProfile x.typ (realEndpoint x.A) n z.1.1 *
      certificateEndpointProfile x.typ (realEndpoint x.B) n z.1.2 *
      certificateEndpointProfile y.typ (realEndpoint y.A) n z.2.1 *
      certificateEndpointProfile y.typ (realEndpoint y.B) n z.2.2 *
        certificateGramMinusKernel x y ![z.1.1, z.1.2, z.2.1, z.2.2])
      ((volume.prod volume).prod (volume.prod volume)) :=
  certificateFeatureProfileIntegral_integrable n hn hx hy _
    (certificateGramMinusKernel_continuousOn_nonneg x y)

end
end Sechstmoment
