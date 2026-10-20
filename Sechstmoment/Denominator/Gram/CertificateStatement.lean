import Sechstmoment.Certificate.Profiles.Denominator
import Sechstmoment.Denominator.Gram.PhaseDefinitions
import Sechstmoment.Final.CauchySchwarz

namespace Sechstmoment
open Filter MeasureTheory
open scoped Topology
noncomputable section

def D06ActualCertificateGramAsymptotic : Prop :=
  ∀ (Φ : ℝ → ℝ), SmoothDyadicWeight Φ → (∀ x, 0 ≤ Φ x) →
  ∀ n : ℕ, 12 ≤ n →
    Tendsto (fun T : ℝ => actual250ProjectedGramMoment n T Φ /
      (T*(Real.log T)^9)) atTop
      (𝓝 (arithmeticFactor*(∫ x : ℝ, Φ x)*certificateProfileDenominator n))

def D06PhaseGramIdentification : Prop :=
  D06ExtremeMinusVanishing ∧ D06ExtremePlusVanishing ∧
    D06ActualCertificateGramAsymptotic

end
end Sechstmoment
