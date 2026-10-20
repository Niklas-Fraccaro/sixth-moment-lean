import Sechstmoment.Numerator.Polar.General.DP
import Sechstmoment.Numerator.V.DP.DPPolydiscBoundary

namespace Sechstmoment.Source
open Complex MeasureTheory Set Polynomial Filter
open scoped Topology
noncomputable section

def dpRegularKernel (η : ℝ) (P : ℝ[X]) (σ : MomentShifts) : ℂ :=
  polarGeneralGeneratorContour η P (polarSourceKnots σ) 16 16

def dpRegularLeadingDensity (T η : ℝ) (P : ℝ[X]) (σ : MomentShifts) : ℂ :=
  (arithmeticFactor : ℂ)*(Real.log T : ℂ)^9*dpRegularKernel η P σ

theorem dpRegularKernel_eq_residues_on_boundary {η : ℝ} (hη : 0 < η)
    (P : ℝ[X]) (σ : MomentShifts)
    (hσ : σ ∈ rectangularDistinguishedBoundary dpCauchyRadii) :
    dpRegularKernel η P σ = (η : ℂ)^6*dpNormalizedFourResidues 1 η P σ := by
  have hn (j : Fin 4) : ‖polarSourceKnots σ j‖=‖σ j‖ := by
    fin_cases j <;> simp [polarSourceKnots]
  have hR : ∀ j, ‖polarSourceKnots σ j‖ < (16 : ℝ) := by
    intro j
    rw [hn,hσ j]
    fin_cases j <;> norm_num [dpCauchyRadii]
  exact polarGeneralGeneratorContour_eq_dpNormalizedFourResidues hη P σ 16 16
    (dpCauchyBoundary_separated σ hσ) hR hR

theorem dpRegularLeadingDensity_eq_on_boundary {η : ℝ} (hη : 0 < η)
    (T : ℝ) (P : ℝ[X]) (σ : MomentShifts)
    (hσ : σ ∈ rectangularDistinguishedBoundary dpCauchyRadii) :
    dpRegularLeadingDensity T η P σ = dpLeadingDensity T η P σ := by
  unfold dpRegularLeadingDensity dpLeadingDensity
  rw [dpRegularKernel_eq_residues_on_boundary hη P σ hσ]
  ring

theorem dpActualMoment_regular_boundary_bound (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ ∈ rectangularDistinguishedBoundary dpCauchyRadii,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → (∀ x, |deriv Φ x| ≤ B) →
      ‖chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ-
        (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpRegularLeadingDensity T η P σ‖ ≤
          C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,hbound⟩ := dpActualMoment_boundary_uniform_smoothing hsource η hη hηu P B hB
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with T hbound σ hσ Φ hΦ hderiv
  rw [dpRegularLeadingDensity_eq_on_boundary hη T P σ hσ]
  exact hbound σ hσ Φ hΦ hderiv

end
end Sechstmoment.Source
