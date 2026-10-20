import Sechstmoment.Certificate.Profiles.Definitions

namespace Sechstmoment
open Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem d06CertificateFeatures_integer_geometry : ∀ x ∈ Finite.features,
    0 < x.A ∧ 0 < x.B ∧
      (x.typ = .U → x.A ≤ x.B ∧ 3*x.A+5*x.B < 2*Finite.base) ∧
      (x.typ = .V → 2106419 ≤ x.A ∧ x.A ≤ 24997500 ∧
        2106419 ≤ x.B ∧ x.B ≤ 24997500) := by decide +kernel

def d06CertificateProfileCap (typ : TestType) (a : ℝ) : ℝ :=
  match typ with
  | .U => a
  | .V => eta

theorem d06CertificateFeature_caps {x : Finite.Feature}
    (hx : x ∈ Finite.features) :
    0 < d06CertificateProfileCap x.typ (realEndpoint x.A) ∧
      0 < d06CertificateProfileCap x.typ (realEndpoint x.B) ∧
      d06CertificateProfileCap x.typ (realEndpoint x.A) +
        d06CertificateProfileCap x.typ (realEndpoint x.B) < 1/2 := by
  obtain ⟨hA,hB,hU,_hV⟩ := d06CertificateFeatures_integer_geometry x hx
  have hb : (0:ℝ) < (Finite.base:ℝ) := by norm_num [Finite.base]
  cases ht : x.typ
  · obtain ⟨hAB,hrect⟩ := hU ht
    have hab : realEndpoint x.A ≤ realEndpoint x.B :=
      div_le_div_of_nonneg_right (by exact_mod_cast hAB) hb.le
    have hr : 3*realEndpoint x.A+5*realEndpoint x.B < 2 := by
      have hi : (3:ℝ)*x.A+5*x.B < 2*(Finite.base:ℝ) := by exact_mod_cast hrect
      dsimp only [realEndpoint]
      rw [show 3*((x.A:ℝ)/(Finite.base:ℝ))+5*((x.B:ℝ)/(Finite.base:ℝ)) =
        (3*(x.A:ℝ)+5*(x.B:ℝ))/(Finite.base:ℝ) by ring]
      exact (div_lt_iff₀ hb).mpr hi
    exact ⟨div_pos (by exact_mod_cast hA) hb,
      div_pos (by exact_mod_cast hB) hb,rectangular_pair_length hab hr⟩
  · refine ⟨eta_pos,eta_pos,?_⟩
    change eta+eta<1/2
    linarith [eta_lt_quarter]

theorem d06Certificate_beta_endpoints {A n : ℕ}
    (hA : 2106419 ≤ A) (hAu : A ≤ 24997500) (hn : 12 ≤ n) :
    betaScaledProfile eta n (betaProfileIndex eta (realEndpoint A) n) 0 = 0 ∧
      betaScaledProfile eta n (betaProfileIndex eta (realEndpoint A) n) eta = 0 := by
  have ha : 0 < realEndpoint A := div_pos
    (by
      have hi : (2106419:ℝ) ≤ A := by exact_mod_cast hA
      linarith)
    (by norm_num [Finite.base])
  have haη : realEndpoint A < eta := by
    have hi : (A:ℝ) ≤ 24997500 := by exact_mod_cast hAu
    dsimp [realEndpoint]
    exact (div_le_div_of_nonneg_right hi (by norm_num [Finite.base])).trans_lt
      (by norm_num [Finite.base,eta])
  have hthreshold : eta ≤ (n:ℝ)*realEndpoint A := by
    have hn' : (12:ℝ) ≤ n := by exact_mod_cast hn
    have hA' : (2106419:ℝ) ≤ A := by exact_mod_cast hA
    have hh := mul_le_mul hn' hA' (by norm_num : (0:ℝ) ≤ 2106419)
      (by positivity : (0:ℝ) ≤ (n:ℝ))
    norm_num [eta,realEndpoint,Finite.base] at *
    nlinarith
  exact betaProfile_endpoints eta_pos ha.le haη (by omega) hthreshold

theorem d06CertificateFeature_profiles_continuous {x : Finite.Feature}
    (hx : x ∈ Finite.features) {n : ℕ} (hn : 12 ≤ n) :
    Continuous (certificateEndpointProfile x.typ (realEndpoint x.A) n) ∧
      Continuous (certificateEndpointProfile x.typ (realEndpoint x.B) n) := by
  obtain ⟨_hA,_hB,_hU,hV⟩ := d06CertificateFeatures_integer_geometry x hx
  cases ht : x.typ
  · exact ⟨(uEndpointProfile_normalized_contDiff _ _ _).continuous,
      (uEndpointProfile_normalized_contDiff _ _ _).continuous⟩
  · obtain ⟨hAl,hAu,hBl,hBu⟩ := hV ht
    exact ⟨vEndpointProfile_continuous_of_endpoints eta_pos n
      (d06Certificate_beta_endpoints hAl hAu hn),
      vEndpointProfile_continuous_of_endpoints eta_pos n
        (d06Certificate_beta_endpoints hBl hBu hn)⟩

theorem d06CertificateEndpointProfile_tsupport (typ : TestType) {a : ℝ}
    (ha : CertificateProfileEndpoint typ a) {n : ℕ} (hn : 0 < n) :
    tsupport (certificateEndpointProfile typ a n) ⊆
      Icc 0 (d06CertificateProfileCap typ a) := by
  cases typ
  · intro t ht
    have h := (uEndpointProfile_normalized_interior uCertificateHstar_pos ha.1 hn).2.2 ht
    exact ⟨h.1.le,h.2.le⟩
  · apply closure_minimal
    · exact vEndpointProfile_support eta a n
    · exact isClosed_Icc

theorem d06CertificateFeature_four_caps {x y : Finite.Feature}
    (hx : x ∈ Finite.features) (hy : y ∈ Finite.features) :
    d06CertificateProfileCap x.typ (realEndpoint x.A)+
      d06CertificateProfileCap x.typ (realEndpoint x.B)+
      d06CertificateProfileCap y.typ (realEndpoint y.A)+
      d06CertificateProfileCap y.typ (realEndpoint y.B) < 1 := by
  exact four_profile_length (d06CertificateFeature_caps hx).2.2
    (d06CertificateFeature_caps hy).2.2

end
end Sechstmoment

namespace Sechstmoment
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem d06CertificatePairs_type_order : ∀ ij ∈ Finite.pairs,
    (Finite.feature ij.1).typ = .V → (Finite.feature ij.2).typ = .V := by
  decide +kernel

theorem d06CertificateFeatures_reflected_coefficients : ∀ x ∈ Finite.features,
    ∀ r : Fin 5, Finite.coef (Finite.reflect x.poly) r.val =
      Finite.coef x.poly r.val * (-1)^r.val := by
  decide +kernel

end Sechstmoment
