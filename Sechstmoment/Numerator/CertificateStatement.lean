import Sechstmoment.Arithmetic.Watt.Statement
import Sechstmoment.Numerator.U.CertificateMoments
import Sechstmoment.Zeta.AFE.Four.Specification


namespace Sechstmoment
open Complex MeasureTheory Filter
open scoped Topology
noncomputable section

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
