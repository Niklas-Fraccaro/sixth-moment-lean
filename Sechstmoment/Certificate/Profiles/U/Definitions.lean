import Sechstmoment.Certificate.Kernels.Balanced.Lengths
import Sechstmoment.Certificate.Profiles.GeneratorCoefficients
import Sechstmoment.Certificate.Profiles.U.Normalized


namespace Sechstmoment
open _root_.Sechstmoment.Finite
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

def uCertificateHstar : ℝ := 1/(2*(Finite.base:ℝ))

theorem uCertificateHstar_pos : 0 < uCertificateHstar := by
  norm_num [uCertificateHstar,Finite.base]

theorem uCertificateHstar_lt_endpoint {A : ℕ} (hA : 0 < A) :
    uCertificateHstar < (A:ℝ)/(Finite.base:ℝ) := by
  have hA1 : (1:ℝ) ≤ A := by exact_mod_cast hA
  dsimp [uCertificateHstar]
  norm_num [Finite.base]
  linarith

theorem certificate_uProfile_admissible {d : TestDatum} (hd : d ∈ certificate)
    {n : ℕ} (hn : 0 < n) :
    SmoothInteriorProfile ((d.A:ℝ)/(Finite.base:ℝ))
      (uEndpointProfile uNormalizedBump uCertificateHstar ((d.A:ℝ)/(Finite.base:ℝ)) n) ∧
    SmoothInteriorProfile ((d.B:ℝ)/(Finite.base:ℝ))
      (uEndpointProfile uNormalizedBump uCertificateHstar ((d.B:ℝ)/(Finite.base:ℝ)) n) := by
  obtain ⟨hA,hB,_⟩ := certificate_numerator_generator_geometry d hd
  exact ⟨uEndpointProfile_normalized_interior uCertificateHstar_pos
    (uCertificateHstar_lt_endpoint hA) hn,
    uEndpointProfile_normalized_interior uCertificateHstar_pos
      (uCertificateHstar_lt_endpoint hB) hn⟩

theorem certificate_uProfile_mass (d : TestDatum) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ, uEndpointProfile uNormalizedBump uCertificateHstar
      ((d.A:ℝ)/(Finite.base:ℝ)) n x)=1 ∧
    (∫ x : ℝ, uEndpointProfile uNormalizedBump uCertificateHstar
      ((d.B:ℝ)/(Finite.base:ℝ)) n x)=1 :=
  ⟨uEndpointProfile_normalized_mass uCertificateHstar_pos _ hn,
    uEndpointProfile_normalized_mass uCertificateHstar_pos _ hn⟩

theorem certificate_uProfile_nonneg (d : TestDatum) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    0 ≤ uEndpointProfile uNormalizedBump uCertificateHstar
      ((d.A:ℝ)/(Finite.base:ℝ)) n x ∧
    0 ≤ uEndpointProfile uNormalizedBump uCertificateHstar
      ((d.B:ℝ)/(Finite.base:ℝ)) n x :=
  ⟨uEndpointProfile_normalized_nonneg uCertificateHstar_pos _ hn x,
    uEndpointProfile_normalized_nonneg uCertificateHstar_pos _ hn x⟩

theorem certificate_uProfile_first_test_tendsto {d : TestDatum} (hd : d ∈ certificate)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 ((d.A:ℝ)/(Finite.base:ℝ)))) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, g x*
      uEndpointProfile uNormalizedBump uCertificateHstar ((d.A:ℝ)/(Finite.base:ℝ)) n x)
      atTop (𝓝 (g ((d.A:ℝ)/(Finite.base:ℝ)))) :=
  uEndpointProfile_normalized_continuousOn_test_tendsto uCertificateHstar_pos
    (uCertificateHstar_lt_endpoint (certificate_numerator_generator_geometry d hd).1) g hg

theorem certificate_uProfile_second_test_tendsto {d : TestDatum} (hd : d ∈ certificate)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 ((d.B:ℝ)/(Finite.base:ℝ)))) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, g x*
      uEndpointProfile uNormalizedBump uCertificateHstar ((d.B:ℝ)/(Finite.base:ℝ)) n x)
      atTop (𝓝 (g ((d.B:ℝ)/(Finite.base:ℝ)))) :=
  uEndpointProfile_normalized_continuousOn_test_tendsto uCertificateHstar_pos
    (uCertificateHstar_lt_endpoint (certificate_numerator_generator_geometry d hd).2.1) g hg

end
end Sechstmoment
