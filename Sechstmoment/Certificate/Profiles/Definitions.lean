import Sechstmoment.Certificate.Profiles.Denominator

/-! A common compact support and one-dimensional concentration for the
literal endpoint families on all 178 certified groups. -/

namespace Sechstmoment
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- All endpoint and type-dependent beta bounds are verified against the
unchanged feature list. Its polynomials are the checked original row sums. -/
theorem certificateFeatures_integer_geometry : ∀ x ∈ Finite.features,
    0 < x.A ∧ 0 < x.B ∧ x.A ≤ Finite.base ∧ x.B ≤ Finite.base ∧
      (x.typ = .V → x.A ≤ 24997500 ∧ x.B ≤ 24997500) := by decide +kernel

theorem certificateFeature_mem {i : ℕ} (hi : i < 178) :
    Finite.feature i ∈ Finite.features := by
  have h : i < Finite.features.length := by rw [Finite.features_length]; exact hi
  unfold Finite.feature
  rw [List.getElem?_eq_getElem h]
  simp only [Option.getD_some]
  exact List.mem_of_getElem rfl

/-- Admissibility needed for scalar concentration. -/
def CertificateProfileEndpoint (typ : TestType) (a : ℝ) : Prop :=
  uCertificateHstar < a ∧ a ≤ 1 ∧ (typ = .V → a ≤ eta)

theorem certificateFeature_endpoint_geometry {x : Finite.Feature}
    (hx : x ∈ Finite.features) :
    CertificateProfileEndpoint x.typ (realEndpoint x.A) ∧
      CertificateProfileEndpoint x.typ (realEndpoint x.B) := by
  obtain ⟨hA,hB,hAb,hBb,hV⟩ := certificateFeatures_integer_geometry x hx
  have ha : realEndpoint x.A ≤ 1 := by
    unfold realEndpoint
    exact (div_le_one (by norm_num [Finite.base])).mpr (by exact_mod_cast hAb)
  have hb : realEndpoint x.B ≤ 1 := by
    unfold realEndpoint
    exact (div_le_one (by norm_num [Finite.base])).mpr (by exact_mod_cast hBb)
  have hv : x.typ = .V → realEndpoint x.A ≤ eta ∧ realEndpoint x.B ≤ eta := by
    intro ht
    have hh := hV ht
    have hmax : (24997500:ℝ)/(Finite.base:ℝ) ≤ eta := by norm_num [Finite.base,eta]
    exact ⟨(div_le_div_of_nonneg_right (by exact_mod_cast hh.1)
      (by norm_num [Finite.base])).trans hmax,
      (div_le_div_of_nonneg_right (by exact_mod_cast hh.2)
      (by norm_num [Finite.base])).trans hmax⟩
  exact ⟨⟨uCertificateHstar_lt_endpoint hA,ha,fun ht => (hv ht).1⟩,
    ⟨uCertificateHstar_lt_endpoint hB,hb,fun ht => (hv ht).2⟩⟩

theorem certificateEndpointProfile_nonneg (typ : TestType) {a : ℝ}
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    0 ≤ certificateEndpointProfile typ a n t := by
  cases typ
  · exact uEndpointProfile_normalized_nonneg uCertificateHstar_pos a hn t
  · exact vEndpointProfile_nonneg eta_pos a n t

theorem certificateEndpointProfile_integrable (typ : TestType) {a : ℝ}
    (ha : CertificateProfileEndpoint typ a) {n : ℕ} (hn : 0 < n) :
    Integrable (certificateEndpointProfile typ a n) := by
  cases typ
  · exact (uEndpointProfile_normalized_contDiff uCertificateHstar a n).continuous.integrable_of_hasCompactSupport
        (uEndpointProfile_normalized_hasCompactSupport uCertificateHstar_pos a hn)
  · exact vEndpointProfile_integrable eta a n

theorem certificateEndpointProfile_mass (typ : TestType) {a : ℝ}
    (ha : CertificateProfileEndpoint typ a) {n : ℕ} (hn : 0 < n) :
    (∫ t : ℝ, certificateEndpointProfile typ a n t) = 1 := by
  cases typ
  · exact uEndpointProfile_normalized_mass uCertificateHstar_pos a hn
  · exact vEndpointProfile_mass eta_pos (uCertificateHstar_pos.trans ha.1).le (ha.2.2 rfl) n

theorem certificateEndpointProfile_support (typ : TestType) {a : ℝ}
    (ha : CertificateProfileEndpoint typ a) {n : ℕ} (hn : 0 < n) :
    Function.support (certificateEndpointProfile typ a n) ⊆ Icc (0:ℝ) 1 := by
  cases typ
  · intro t ht
    have h := (uEndpointProfile_normalized_interior uCertificateHstar_pos ha.1 hn).2.2
      (subset_tsupport _ ht)
    exact ⟨h.1.le,h.2.le.trans ha.2.1⟩
  · intro t ht
    have h := vEndpointProfile_support eta a n ht
    exact ⟨h.1,h.2.trans (by norm_num [eta])⟩

/-- Scalar weak limits hold against every continuous test on the same
compact interval; no moving profile parameter depends on the height T. -/
theorem certificateEndpointProfile_test_tendsto (typ : TestType) {a : ℝ}
    (ha : CertificateProfileEndpoint typ a) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc (0:ℝ) 1)) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, g t * certificateEndpointProfile typ a n t)
      atTop (𝓝 (g a)) := by
  cases typ
  · exact uEndpointProfile_normalized_continuousOn_test_tendsto uCertificateHstar_pos ha.1 g
      (hg.mono (by intro x hx; exact ⟨hx.1,hx.2.trans ha.2.1⟩))
  · exact vEndpointProfile_continuous_test_tendsto eta_pos
      (uCertificateHstar_pos.trans ha.1).le (ha.2.2 rfl) g
      (hg.mono (by intro x hx; exact ⟨hx.1,hx.2.trans (by norm_num [eta])⟩))

end
end Sechstmoment
