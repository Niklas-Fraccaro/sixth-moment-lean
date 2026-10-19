import Sechstmoment.Certificate.Profiles.Definitions
import Sechstmoment.Certificate.Profiles.KernelContinuity
import Sechstmoment.Certificate.Profiles.ProductLimit

/-! Joint concentration of the actual four endpoint profiles on every
certified balanced and unbalanced Gram entry. -/

namespace Sechstmoment
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000

private def featureProfiles4 (n : ℕ) (x y : Finite.Feature) : Fin 4 → ℝ → ℝ :=
  ![certificateEndpointProfile x.typ (realEndpoint x.A) n,
    certificateEndpointProfile x.typ (realEndpoint x.B) n,
    certificateEndpointProfile y.typ (realEndpoint y.A) n,
    certificateEndpointProfile y.typ (realEndpoint y.B) n]

private def profileEndpoints4 (z : P02ProfilePoint) : Fin 4 → ℝ :=
  ![z.1.1,z.1.2,z.2.1,z.2.2]

private theorem profileEndpoints4_continuous : Continuous profileEndpoints4 := by
  unfold profileEndpoints4
  fun_prop

private theorem profileEndpoints4_nonneg {z : P02ProfilePoint}
    (hz : z ∈ p02ProfileBox 1) : ∀ i, 0 ≤ profileEndpoints4 z i := by
  intro i
  fin_cases i
  · exact hz.1.1.1
  · exact hz.1.2.1
  · exact hz.2.1.1
  · exact hz.2.2.1

private theorem certificateFeatureProfileIntegral_eq_average (n : ℕ) (x y : Finite.Feature)
    (F : (Fin 4 → ℝ) → ℝ) :
    certificateFeatureProfileIntegral n x y F =
      profileProductAverage4 (fun m => featureProfiles4 m x y) n
        (fun z => F (profileEndpoints4 z)) := by
  unfold certificateFeatureProfileIntegral profileProductAverage4 p02ProfileDensity
    featureProfiles4 profileEndpoints4
  apply integral_congr_ae
  filter_upwards [] with z
  change
    certificateEndpointProfile x.typ (realEndpoint x.A) n z.1.1 *
    certificateEndpointProfile x.typ (realEndpoint x.B) n z.1.2 *
    certificateEndpointProfile y.typ (realEndpoint y.A) n z.2.1 *
    certificateEndpointProfile y.typ (realEndpoint y.B) n z.2.2 *
      F ![z.1.1,z.1.2,z.2.1,z.2.2] =
    (certificateEndpointProfile x.typ (realEndpoint x.A) n z.1.1 *
    certificateEndpointProfile x.typ (realEndpoint x.B) n z.1.2) *
    (certificateEndpointProfile y.typ (realEndpoint y.A) n z.2.1 *
    certificateEndpointProfile y.typ (realEndpoint y.B) n z.2.2) *
      F ![z.1.1,z.1.2,z.2.1,z.2.2]
  ring

/-- A genuine four-profile concentration theorem for any kernel continuous
on the closed nonnegative orthant. The four one-dimensional limits, masses,
supports and integrability are proved for the literal certificate families. -/
theorem certificateFeatureProfileIntegral_tendsto {x y : Finite.Feature}
    (hx : x ∈ Finite.features) (hy : y ∈ Finite.features)
    (F : (Fin 4 → ℝ) → ℝ) (hF : ContinuousOn F {z | ∀ i, 0 ≤ z i}) :
    Tendsto (fun n => certificateFeatureProfileIntegral n x y F) atTop
      (𝓝 (F (certificateFeatureEndpoints x y))) := by
  obtain ⟨hxA,hxB⟩ := certificateFeature_endpoint_geometry hx
  obtain ⟨hyA,hyB⟩ := certificateFeature_endpoint_geometry hy
  have ha : ∀ i, certificateFeatureEndpoints x y i ∈ Icc (0:ℝ) 1 := by
    intro i
    fin_cases i
    · exact ⟨(uCertificateHstar_pos.trans hxA.1).le,hxA.2.1⟩
    · exact ⟨(uCertificateHstar_pos.trans hxB.1).le,hxB.2.1⟩
    · exact ⟨(uCertificateHstar_pos.trans hyA.1).le,hyA.2.1⟩
    · exact ⟨(uCertificateHstar_pos.trans hyB.1).le,hyB.2.1⟩
  have hi : ∀ n i, Integrable (featureProfiles4 (n+1) x y i) := by
    intro n i
    fin_cases i
    · exact certificateEndpointProfile_integrable _ hxA (Nat.succ_pos n)
    · exact certificateEndpointProfile_integrable _ hxB (Nat.succ_pos n)
    · exact certificateEndpointProfile_integrable _ hyA (Nat.succ_pos n)
    · exact certificateEndpointProfile_integrable _ hyB (Nat.succ_pos n)
  have hn : ∀ n i t, 0 ≤ featureProfiles4 (n+1) x y i t := by
    intro n i t
    fin_cases i <;> exact certificateEndpointProfile_nonneg _ (Nat.succ_pos n) t
  have hm : ∀ n i, (∫ t : ℝ, featureProfiles4 (n+1) x y i t) = 1 := by
    intro n i
    fin_cases i
    · exact certificateEndpointProfile_mass _ hxA (Nat.succ_pos n)
    · exact certificateEndpointProfile_mass _ hxB (Nat.succ_pos n)
    · exact certificateEndpointProfile_mass _ hyA (Nat.succ_pos n)
    · exact certificateEndpointProfile_mass _ hyB (Nat.succ_pos n)
  have hs : ∀ n i, Function.support (featureProfiles4 (n+1) x y i) ⊆ Icc (0:ℝ) 1 := by
    intro n i
    fin_cases i
    · exact certificateEndpointProfile_support _ hxA (Nat.succ_pos n)
    · exact certificateEndpointProfile_support _ hxB (Nat.succ_pos n)
    · exact certificateEndpointProfile_support _ hyA (Nat.succ_pos n)
    · exact certificateEndpointProfile_support _ hyB (Nat.succ_pos n)
  have hw : ∀ i (g : ℝ → ℝ), ContinuousOn g (Icc (0:ℝ) 1) →
      Tendsto (fun n => ∫ t : ℝ, g t * featureProfiles4 (n+1) x y i t) atTop
        (𝓝 (g (certificateFeatureEndpoints x y i))) := by
    intro i g hg
    fin_cases i
    · exact (certificateEndpointProfile_test_tendsto _ hxA g hg).comp (tendsto_add_atTop_nat 1)
    · exact (certificateEndpointProfile_test_tendsto _ hxB g hg).comp (tendsto_add_atTop_nat 1)
    · exact (certificateEndpointProfile_test_tendsto _ hyA g hg).comp (tendsto_add_atTop_nat 1)
    · exact (certificateEndpointProfile_test_tendsto _ hyB g hg).comp (tendsto_add_atTop_nat 1)
  have hc : ContinuousOn (fun z => F (profileEndpoints4 z)) (p02ProfileBox 1) :=
    hF.comp profileEndpoints4_continuous.continuousOn (fun z hz => profileEndpoints4_nonneg hz)
  have h := profileProductAverage4_tendsto 1 (fun n => featureProfiles4 (n+1) x y)
    (certificateFeatureEndpoints x y) ha hi hn hm hs hw _ hc
  have he : profileEndpoints4 (p02ProfilePoint (certificateFeatureEndpoints x y)) =
      certificateFeatureEndpoints x y := by
    ext i
    fin_cases i <;> rfl
  rw [he] at h
  apply (tendsto_add_atTop_iff_nat 1).1
  simpa only [certificateFeatureProfileIntegral_eq_average,profileProductAverage4] using h

/-- Every actual balanced Gram entry has its four-profile endpoint limit. -/
theorem certificateProfileGramZero_tendsto {x y : Finite.Feature}
    (hx : x ∈ Finite.features) (hy : y ∈ Finite.features) :
    Tendsto (fun n => certificateProfileGramZero n x y) atTop
      (𝓝 (certificateGramZeroKernel x y (certificateFeatureEndpoints x y))) :=
  certificateFeatureProfileIntegral_tendsto hx hy _
    (certificateGramZeroKernel_continuousOn_nonneg x y)

/-- Every actual unbalanced Gram entry has the same common-stage limit. -/
theorem certificateProfileGramMinus_tendsto {x y : Finite.Feature}
    (hx : x ∈ Finite.features) (hy : y ∈ Finite.features) :
    Tendsto (fun n => certificateProfileGramMinus n x y) atTop
      (𝓝 (certificateGramMinusKernel x y (certificateFeatureEndpoints x y))) :=
  certificateFeatureProfileIntegral_tendsto hx hy _
    (certificateGramMinusKernel_continuousOn_nonneg x y)

/-- The full 15931-pair denominator concentrates to its literal integral
endpoint sum; there are no extra convergence hypotheses. -/
theorem certificateProfileDenominator_tendsto_point :
    Tendsto certificateProfileDenominator atTop (𝓝 certificatePointDenominator) := by
  have hzero : Tendsto (fun n : ℕ => (Finite.pairs.map fun ij =>
      (if ij.1 = ij.2 then (1:ℝ) else 2) *
        certificateProfileGramZero n (Finite.feature ij.1) (Finite.feature ij.2)).sum)
      atTop (𝓝 ((Finite.pairs.map fun ij =>
        (if ij.1 = ij.2 then (1:ℝ) else 2) *
          certificateGramZeroKernel (Finite.feature ij.1) (Finite.feature ij.2)
            (certificateFeatureEndpoints (Finite.feature ij.1) (Finite.feature ij.2))).sum)) := by
    apply tendsto_list_sum
    intro ij hij
    obtain ⟨hle,hlt⟩ := Finite.pair_indices_valid ij hij
    exact (certificateProfileGramZero_tendsto
      (certificateFeature_mem (hle.trans_lt hlt)) (certificateFeature_mem hlt)).const_mul _
  have hminus : Tendsto (fun n : ℕ => (Finite.pairs.map fun ij =>
      (if ij.1 = ij.2 then (1:ℝ) else 2) *
        certificateProfileGramMinus n (Finite.feature ij.1) (Finite.feature ij.2)).sum)
      atTop (𝓝 ((Finite.pairs.map fun ij =>
        (if ij.1 = ij.2 then (1:ℝ) else 2) *
          certificateGramMinusKernel (Finite.feature ij.1) (Finite.feature ij.2)
            (certificateFeatureEndpoints (Finite.feature ij.1) (Finite.feature ij.2))).sum)) := by
    apply tendsto_list_sum
    intro ij hij
    obtain ⟨hle,hlt⟩ := Finite.pair_indices_valid ij hij
    exact (certificateProfileGramMinus_tendsto
      (certificateFeature_mem (hle.trans_lt hlt)) (certificateFeature_mem hlt)).const_mul _
  exact (hzero.add hminus).div_const 2


end
end Sechstmoment
