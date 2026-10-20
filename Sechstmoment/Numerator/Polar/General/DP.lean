import Sechstmoment.Numerator.Polar.General.Coincidence
import Sechstmoment.Numerator.Polar.General.Triple
import Sechstmoment.Numerator.V.DP.DPWeightedSimplex

namespace Sechstmoment
open Complex Metric Filter Set
open scoped BigOperators Topology

set_option maxHeartbeats 1000000

theorem polarGeneralTripleProfile_eq_dpNormalizedTriple
    {η : ℝ} (hη : 0 < η) (P : Polynomial ℝ) (β γ δ : ℂ) (R : ℝ)
    (hq : Function.Injective (![-β,γ,δ] : Fin 3 → ℂ))
    (hR : ∀ j, ‖(![-β,γ,δ] : Fin 3 → ℂ) j‖ < R) :
    polarGeneralTripleProfile η P ![-β,γ,δ] R =
      (η : ℂ)^3 * Source.dpNormalizedTriple η P β γ δ := by
  unfold polarGeneralTripleProfile
  simp_rw [polarTripleInverseContour_eq_triangle _ _ R hq hR]
  exact weighted_triangle_eq_dpNormalizedTriple hη P β γ δ

theorem polarGeneralGeneratorContour_eq_dpNormalizedFourResidues
    {η : ℝ} (hη : 0 < η) (P : Polynomial ℝ) (σ : Fin 4 → ℂ) (innerR outerR : ℝ)
    (hσ : Function.Injective (polarSourceKnots σ))
    (hinner : ∀ j, ‖polarSourceKnots σ j‖ < innerR)
    (houter : ∀ j, ‖polarSourceKnots σ j‖ < outerR) :
    polarGeneralGeneratorContour η P (polarSourceKnots σ) innerR outerR =
      (η : ℂ)^6 * Source.dpNormalizedFourResidues 1 η P σ := by
  have hv0 : Function.Injective (![-σ 1,σ 2,σ 3] : Fin 3 → ℂ) := by
    have h := hσ.comp (show Function.Injective ((0 : Fin 4).succAbove) from Fin.succAbove_right_injective)
    convert h using 1
    funext k
    fin_cases k <;> rfl
  have hv1 : Function.Injective (![-σ 0,σ 2,σ 3] : Fin 3 → ℂ) := by
    have h := hσ.comp (show Function.Injective ((1 : Fin 4).succAbove) from Fin.succAbove_right_injective)
    convert h using 1
    funext k
    fin_cases k <;> rfl
  have hv2 : Function.Injective (![-σ 1,-σ 0,σ 3] : Fin 3 → ℂ) := by
    intro j k hjk
    have hmap (i : Fin 3) : (![-σ 1,-σ 0,σ 3] : Fin 3 → ℂ) i =
        polarSourceKnots σ ((![1,0,3] : Fin 3 → Fin 4) i) := by fin_cases i <;> rfl
    rw [hmap,hmap] at hjk
    have h := hσ hjk
    fin_cases j <;> fin_cases k <;> simp_all
  have hv3 : Function.Injective (![-σ 1,σ 2,-σ 0] : Fin 3 → ℂ) := by
    intro j k hjk
    have hmap (i : Fin 3) : (![-σ 1,σ 2,-σ 0] : Fin 3 → ℂ) i =
        polarSourceKnots σ ((![1,2,0] : Fin 3 → Fin 4) i) := by fin_cases i <;> rfl
    rw [hmap,hmap] at hjk
    have h := hσ hjk
    fin_cases j <;> fin_cases k <;> simp_all
  have hR0 : ∀ j, ‖(![-σ 1,σ 2,σ 3] : Fin 3 → ℂ) j‖ < innerR := by
    intro j
    fin_cases j
    · exact hinner 1
    · exact hinner 2
    · exact hinner 3
  have hR1 : ∀ j, ‖(![-σ 0,σ 2,σ 3] : Fin 3 → ℂ) j‖ < innerR := by
    intro j
    fin_cases j
    · exact hinner 0
    · exact hinner 2
    · exact hinner 3
  have hR2 : ∀ j, ‖(![-σ 1,-σ 0,σ 3] : Fin 3 → ℂ) j‖ < innerR := by
    intro j
    fin_cases j
    · exact hinner 1
    · exact hinner 0
    · exact hinner 3
  have hR3 : ∀ j, ‖(![-σ 1,σ 2,-σ 0] : Fin 3 → ℂ) j‖ < innerR := by
    intro j
    fin_cases j
    · exact hinner 1
    · exact hinner 2
    · exact hinner 0
  rw [polarGeneralGeneratorContour_source_residues η P σ innerR outerR hσ hinner houter,
    polarGeneralTripleProfile_eq_dpNormalizedTriple hη P _ _ _ innerR hv0 hR0,
    polarGeneralTripleProfile_eq_dpNormalizedTriple hη P _ _ _ innerR hv1 hR1,
    polarGeneralTripleProfile_eq_dpNormalizedTriple hη P _ _ _ innerR hv2 hR2,
    polarGeneralTripleProfile_eq_dpNormalizedTriple hη P _ _ _ innerR hv3 hR3]
  simp only [Source.dpNormalizedFourResidues, Complex.ofReal_one,one_mul]
  ring

theorem polarSourceKnots_continuous : Continuous polarSourceKnots := by
  unfold polarSourceKnots
  fun_prop

theorem dpNormalizedFourResidues_joint_limit
    {η : ℝ} (hη : 0 < η) (P : Polynomial ℝ) (σ : Fin 4 → ℂ) (innerR outerR : ℝ)
    (hinner : ∀ j, ‖polarSourceKnots σ j‖ < innerR)
    (houter : ∀ j, ‖polarSourceKnots σ j‖ < outerR) :
    Tendsto (fun σ' : Fin 4 → ℂ =>
      (η : ℂ)^6 * Source.dpNormalizedFourResidues 1 η P σ')
      (𝓝[{σ' | Source.DPSeparated σ'}] σ)
      (𝓝 (polarGeneralGeneratorContour η P (polarSourceKnots σ) innerR outerR)) := by
  have ht : Tendsto (fun σ' : Fin 4 → ℂ =>
      polarGeneralGeneratorContour η P (polarSourceKnots σ') innerR outerR)
      (𝓝[{σ' | Source.DPSeparated σ'}] σ)
      (𝓝 (polarGeneralGeneratorContour η P (polarSourceKnots σ) innerR outerR)) :=
    ((polarGeneralGeneratorContour_continuousAt η P (polarSourceKnots σ)
      innerR outerR hinner houter).comp polarSourceKnots_continuous.continuousAt).tendsto.mono_left
      inf_le_left
  apply ht.congr'
  have hd : ∀ᶠ σ' in 𝓝 σ,
      polarSourceKnots σ' ∈ polarCircleDomain innerR outerR :=
    polarSourceKnots_continuous.continuousAt.preimage_mem_nhds
      ((polarCircleDomain_isOpen innerR outerR).mem_nhds
        (fun j => ⟨hinner j,houter j⟩))
  filter_upwards [hd.filter_mono inf_le_left,self_mem_nhdsWithin] with σ' hσ' hSeparated
  exact polarGeneralGeneratorContour_eq_dpNormalizedFourResidues hη P σ' innerR outerR
    hSeparated (fun j => (hσ' j).1) (fun j => (hσ' j).2)

end Sechstmoment
