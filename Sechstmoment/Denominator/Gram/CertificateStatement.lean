import Sechstmoment.Certificate.Profiles.Denominator
import Sechstmoment.Denominator.Gram.PhaseDefinitions
import Sechstmoment.Final.CauchySchwarz

/-! The literal D06 consumer for the original certificate.
Both actual extreme phases and the actual full projected Gram moment are
retained. The height limit is at a fixed common profile stage, with no
asymptotic or reconstruction assertion as an additional antecedent.
Nonnegative smooth dyadic weights are exactly the norm weights needed by F01. -/
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

/-- D06 for both original extreme phases and the exact original 250-row norm.
All three components are theorems to prove, never axioms or source contracts. -/
def D06PhaseGramIdentification : Prop :=
  D06ExtremeMinusVanishing ∧ D06ExtremePlusVanishing ∧
    D06ActualCertificateGramAsymptotic

end
end Sechstmoment
