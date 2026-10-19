import Sechstmoment.Arithmetic.Watt.Statement
import Sechstmoment.Numerator.U.CertificateMoments
import Sechstmoment.Zeta.AFE.Four.Specification

/-!
# Necessary first-row consumer, with Watt Proposition 4.1

This proposition is a target specification, not an axiom or a theorem.
It retains the actual original 250-row raw and phase-projected zeta tests,
normalization by T log(T)^9, the fixed profile-stage height limit, and the
subsequent profile concentration limit. There is no hypothesis asserting a
U moment asymptotic, a reconstruction receipt, a contour receipt or the target.

A witness of this target is necessary for the requested A03--A05 chain, but
alone does not certify Lemma 2's quantitative A03 estimate or every A04 step.
The Python gate therefore keeps the entire first row OPEN independently.
-/

namespace Sechstmoment
open Complex MeasureTheory Filter
open scoped Topology
noncomputable section

/-- Exact necessary consumer under only Watt Proposition 4.1.
A declaration with an additional unproved U-limit premise cannot inhabit this
proposition. The common V concentration stage is the existing stage 12. -/
def FirstRowNumeratorConsumer : Prop :=
  DivisorProof.Watt41 →
  ∀ (Φ : ℝ → ℝ), SmoothDyadicWeight Φ →
    (∀ n : ℕ, 12 ≤ n → Tendsto
      (fun T : ℝ => actual250RawMixedMoment n T Φ / ((T:ℂ)*(Real.log T:ℂ)^9))
      atTop (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        Complex.ofReal (certificateProfileNumerator n)))) ∧
    (∀ n : ℕ, 12 ≤ n → Tendsto
      (fun T : ℝ => actual250ProjectedMixedMoment n T Φ / ((T:ℂ)*(Real.log T:ℂ)^9))
      atTop (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        Complex.ofReal (certificateProfileNumerator n)))) ∧
    Tendsto (fun n : ℕ => (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (certificateProfileNumerator n)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        Complex.ofReal (finiteNumerator:ℝ)))

end
end Sechstmoment
