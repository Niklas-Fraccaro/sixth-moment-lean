import Sechstmoment.Numerator.Polar.General.DP
import Sechstmoment.Numerator.Polar.General.Holomorphy
import Sechstmoment.Numerator.V.DP.DPPolynomialPolarization

/-! Actual two-profile polar circle and its exact literal DP-residue collision limit. -/

namespace Sechstmoment
open Complex Metric Filter Set MeasureTheory
open scoped BigOperators Topology

set_option maxHeartbeats 0

theorem polarGeneralProfile_add (η : ℝ) (P Q : Polynomial ℝ)
    (q : Fin 4 → ℂ) (R : ℝ) (ω : ℂ) (hR : ∀ j, ‖q j‖ < R) :
    polarGeneralProfile η (P+Q) q R ω =
      polarGeneralProfile η P q R ω+polarGeneralProfile η Q q R ω := by
  have hi : Continuous (fun a : ℝ => polarGeneralInverseContour a ω q R) :=
    polarGeneralInverseContour_continuous_family id (fun _ : ℝ => ω)
      (fun _ : ℝ => q) R continuous_id continuous_const continuous_const (fun _ => hR)
  have hc (S : Polynomial ℝ) : Continuous (fun a : ℝ =>
      ((Polynomial.eval (1-a/η:ℝ) S:ℝ):ℂ)*polarGeneralInverseContour a ω q R) :=
    (by fun_prop : Continuous (fun a : ℝ =>
      ((Polynomial.eval (1-a/η:ℝ) S:ℝ):ℂ))).mul hi
  unfold polarGeneralProfile
  simp only [Polynomial.eval_add, Complex.ofReal_add, add_mul]
  exact intervalIntegral.integral_add ((hc P).intervalIntegrable 0 η)
    ((hc Q).intervalIntegrable 0 η)

theorem polarGeneralProfile_neg (η : ℝ) (P : Polynomial ℝ)
    (q : Fin 4 → ℂ) (R : ℝ) (ω : ℂ) :
    polarGeneralProfile η (-P) q R ω = -polarGeneralProfile η P q R ω := by
  unfold polarGeneralProfile
  simp only [Polynomial.eval_neg, Complex.ofReal_neg, neg_mul, intervalIntegral.integral_neg]

theorem polarGeneralProfile_sub (η : ℝ) (P Q : Polynomial ℝ)
    (q : Fin 4 → ℂ) (R : ℝ) (ω : ℂ) (hR : ∀ j, ‖q j‖ < R) :
    polarGeneralProfile η (P-Q) q R ω =
      polarGeneralProfile η P q R ω-polarGeneralProfile η Q q R ω := by
  rw [sub_eq_add_neg, polarGeneralProfile_add η P (-Q) q R ω hR,
    polarGeneralProfile_neg, sub_eq_add_neg]

noncomputable def polarGeneralBilinearGeneratorContour (η : ℝ) (P Q : Polynomial ℝ)
    (q : Fin 4 → ℂ) (innerR outerR : ℝ) : ℂ :=
  (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
    ∮ ω in C(0,outerR), Complex.exp (ω-q 2-q 3)/
      (∏ j : Fin 4, (ω-q j))*polarGeneralProfile η P q innerR ω*
        polarGeneralProfile η Q q innerR ω

private theorem actual_polar_integrand_circleIntegrable (η : ℝ) (P : Polynomial ℝ)
    (q : Fin 4 → ℂ) (innerR outerR : ℝ)
    (hinner : ∀ j, ‖q j‖ < innerR) (houter : ∀ j, ‖q j‖ < outerR) :
    CircleIntegrable (fun ω : ℂ => Complex.exp (ω-q 2-q 3)/
      (∏ j : Fin 4, (ω-q j))*(polarGeneralProfile η P q innerR ω)^2) 0 outerR := by
  have hpos : 0 < outerR := (norm_nonneg (q 0)).trans_lt (houter 0)
  have hp : Continuous (fun ω : ℂ => polarGeneralProfile η P q innerR ω) :=
    polarGeneralProfile_continuous_family η P id (fun _ : ℂ => q) innerR
      continuous_id continuous_const (fun _ => hinner)
  apply ContinuousOn.circleIntegrable hpos.le
  apply ContinuousOn.mul
  · apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro ω hω
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      apply sub_ne_zero.mpr
      have hn : ‖ω‖ = outerR := by simpa [mem_sphere, dist_eq_norm] using hω
      intro he
      rw [he] at hn
      exact (ne_of_lt (houter j)) hn
  · exact (hp.pow 2).continuousOn

theorem polarGeneralBilinearGeneratorContour_polarization (η : ℝ) (P Q : Polynomial ℝ)
    (q : Fin 4 → ℂ) (innerR outerR : ℝ)
    (hinner : ∀ j, ‖q j‖ < innerR) (houter : ∀ j, ‖q j‖ < outerR) :
    polarGeneralBilinearGeneratorContour η P Q q innerR outerR =
      (1/4:ℂ)*(polarGeneralGeneratorContour η (P+Q) q innerR outerR-
        polarGeneralGeneratorContour η (P-Q) q innerR outerR) := by
  have he (ω : ℂ) : Complex.exp (ω-q 2-q 3)/(∏ j : Fin 4, (ω-q j))*
      polarGeneralProfile η P q innerR ω*polarGeneralProfile η Q q innerR ω =
    (1/4:ℂ)*(Complex.exp (ω-q 2-q 3)/(∏ j : Fin 4, (ω-q j))*
      (polarGeneralProfile η (P+Q) q innerR ω)^2-
      Complex.exp (ω-q 2-q 3)/(∏ j : Fin 4, (ω-q j))*
        (polarGeneralProfile η (P-Q) q innerR ω)^2) := by
    rw [polarGeneralProfile_add η P Q q innerR ω hinner,
      polarGeneralProfile_sub η P Q q innerR ω hinner]
    ring
  unfold polarGeneralBilinearGeneratorContour polarGeneralGeneratorContour
  simp_rw [he]
  rw [circleIntegral.integral_const_mul,
    circleIntegral.integral_sub
      (actual_polar_integrand_circleIntegrable η (P+Q) q innerR outerR hinner houter)
      (actual_polar_integrand_circleIntegrable η (P-Q) q innerR outerR hinner houter)]
  ring

theorem polarGeneralBilinearGeneratorContour_eq_dpNormalizedBilinearFourResidues
    {η : ℝ} (hη : 0 < η) (P Q : Polynomial ℝ) (σ : Fin 4 → ℂ)
    (innerR outerR : ℝ) (hσ : Function.Injective (polarSourceKnots σ))
    (hinner : ∀ j, ‖polarSourceKnots σ j‖ < innerR)
    (houter : ∀ j, ‖polarSourceKnots σ j‖ < outerR) :
    polarGeneralBilinearGeneratorContour η P Q (polarSourceKnots σ) innerR outerR =
      (η:ℂ)^6*Source.dpNormalizedBilinearFourResidues 1 η P Q σ := by
  rw [polarGeneralBilinearGeneratorContour_polarization η P Q _ _ _ hinner houter,
    polarGeneralGeneratorContour_eq_dpNormalizedFourResidues hη (P+Q) σ
      innerR outerR hσ hinner houter,
    polarGeneralGeneratorContour_eq_dpNormalizedFourResidues hη (P-Q) σ
      innerR outerR hσ hinner houter,
    Source.dpNormalizedBilinearFourResidues_polarization]
  ring

theorem dpNormalizedBilinearFourResidues_joint_limit
    {η : ℝ} (hη : 0 < η) (P Q : Polynomial ℝ) (σ : Fin 4 → ℂ)
    (innerR outerR : ℝ)
    (hinner : ∀ j, ‖polarSourceKnots σ j‖ < innerR)
    (houter : ∀ j, ‖polarSourceKnots σ j‖ < outerR) :
    Tendsto (fun σ' : Fin 4 → ℂ =>
      (η:ℂ)^6*Source.dpNormalizedBilinearFourResidues 1 η P Q σ')
      (𝓝[{σ' | Source.DPSeparated σ'}] σ)
      (𝓝 (polarGeneralBilinearGeneratorContour η P Q (polarSourceKnots σ) innerR outerR)) := by
  have hp := dpNormalizedFourResidues_joint_limit hη (P+Q) σ innerR outerR hinner houter
  have hm := dpNormalizedFourResidues_joint_limit hη (P-Q) σ innerR outerR hinner houter
  have ht := (hp.sub hm).const_mul (1/4:ℂ)
  rw [← polarGeneralBilinearGeneratorContour_polarization η P Q _ _ _ hinner houter] at ht
  apply ht.congr
  intro σ'
  rw [Source.dpNormalizedBilinearFourResidues_polarization]
  ring

theorem polarGeneralBilinearGeneratorContour_continuousAt (η : ℝ)
    (P Q : Polynomial ℝ) (q : Fin 4 → ℂ) (innerR outerR : ℝ)
    (hinner : ∀ j, ‖q j‖ < innerR) (houter : ∀ j, ‖q j‖ < outerR) :
    ContinuousAt (fun q' => polarGeneralBilinearGeneratorContour η P Q q' innerR outerR) q := by
  have hp := polarGeneralGeneratorContour_continuousAt η (P+Q) q innerR outerR hinner houter
  have hm := polarGeneralGeneratorContour_continuousAt η (P-Q) q innerR outerR hinner houter
  have hc := (hp.sub hm).const_mul (1/4:ℂ)
  apply hc.congr_of_eventuallyEq
  filter_upwards [(polarCircleDomain_isOpen innerR outerR).mem_nhds
    (fun j => ⟨hinner j,houter j⟩)] with q' hq'
  exact polarGeneralBilinearGeneratorContour_polarization η P Q q' innerR outerR
    (fun j => (hq' j).1) (fun j => (hq' j).2)

theorem polarGeneralBilinearGeneratorContour_differentiableOn (η : ℝ)
    (P Q : Polynomial ℝ) (innerR outerR : ℝ) (hη : 0 ≤ η) :
    DifferentiableOn ℂ (fun q => polarGeneralBilinearGeneratorContour η P Q q innerR outerR)
      (polarCircleDomain innerR outerR) := by
  have hp := polarGeneralGeneratorContour_differentiableOn η (P+Q) innerR outerR hη
  have hm := polarGeneralGeneratorContour_differentiableOn η (P-Q) innerR outerR hη
  have hc := (hp.sub hm).const_mul (1/4:ℂ)
  apply hc.congr
  intro q hq
  exact polarGeneralBilinearGeneratorContour_polarization η P Q q innerR outerR
    (fun j => (hq j).1) (fun j => (hq j).2)

end Sechstmoment
