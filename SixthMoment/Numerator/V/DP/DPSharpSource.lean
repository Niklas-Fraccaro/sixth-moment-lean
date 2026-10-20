import SixthMoment.Analysis.Dyadic.PartialSummation
import SixthMoment.Numerator.V.DP.DPNormalization


namespace SixthMoment.Source
open Complex MeasureTheory Set Polynomial Filter
open scoped Topology
noncomputable section

def dpSharpMoment (T X η : ℝ) (P : ℝ[X]) (σ : MomentShifts) : ℂ :=
  sharpPrimitive (fun t => chiTwistedFourthIntegrand T t (rawMomentShifts T σ)
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
    (fun _ => 1)) X

def dpRawSharpMainTerm (T X η : ℝ) (P : ℝ[X]) (σ : MomentShifts) : ℂ :=
  (arithmeticFactor : ℂ)*(X : ℂ)*(Real.log (T^η) : ℂ)^6*
    dpFourResidues X (T^η) P (rawMomentShifts T σ)

def DPv2SharpInput : Prop :=
  ∀ η : ℝ, 0 < η → η < 1/4 → ∀ P : ℝ[X],
  ∀ K : Set MomentShifts, IsCompact K → (∀ σ ∈ K, DPSeparated σ) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ X ∈ Icc (T/4) (2*T),
      ‖dpSharpMoment T X η P σ-dpRawSharpMainTerm T X η P σ‖ ≤
        C*T*(Real.log T)^8

def dpLeadingDensity (T η : ℝ) (P : ℝ[X]) (σ : MomentShifts) : ℂ :=
  (arithmeticFactor : ℂ)*(Real.log T : ℂ)^9*(η : ℂ)^6*
    dpNormalizedFourResidues 1 η P σ

theorem dpRawSharpMainTerm_normalized {T : ℝ} (hT : 1 < T)
    (X η : ℝ) (P : ℝ[X]) (σ : MomentShifts) :
    dpRawSharpMainTerm T X η P σ =
      (X : ℂ)*(arithmeticFactor : ℂ)*(Real.log T : ℂ)^9*(η : ℂ)^6*
        dpNormalizedFourResidues (Real.log (X/(2*Real.pi))/Real.log T) η P σ := by
  unfold dpRawSharpMainTerm
  rw [Real.log_rpow (zero_lt_one.trans hT), dpFourResidues_endpoint_normalized hT]
  push_cast
  ring

end
end SixthMoment.Source
