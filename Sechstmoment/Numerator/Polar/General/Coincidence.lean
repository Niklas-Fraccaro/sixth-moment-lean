import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Sechstmoment.Numerator.Polar.General.Source

/-!
Continuity of the actual fixed-circle formula, including coincident shifts.
The circles surround the knots uniformly; no residue expression is used to
assert continuity across its apparent denominators.
-/

namespace Sechstmoment
open Complex Metric MeasureTheory Set Filter
open scoped BigOperators Topology

set_option maxHeartbeats 1000000

private theorem polar_circle_denominator_ne {n : ℕ} (q : Fin n → ℂ)
    (R : ℝ) (hR : ∀ j, ‖q j‖ < R) (θ : ℝ) :
    (∏ j : Fin n, (circleMap 0 R θ-q j)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply sub_ne_zero.mpr
  apply circleMap_ne_mem_ball
  simpa [mem_ball,dist_eq_norm] using hR j

theorem polarGeneralInverseContour_continuous_family
    {X : Type*} [TopologicalSpace X]
    (x : X → ℝ) (ω : X → ℂ) (q : X → (Fin 4 → ℂ)) (R : ℝ)
    (hx : Continuous x) (hω : Continuous ω) (hq : Continuous q)
    (hR : ∀ p j, ‖q p j‖ < R) :
    Continuous (fun p => polarGeneralInverseContour (x p) (ω p) (q p) R) := by
  unfold polarGeneralInverseContour circleIntegral
  simp only [deriv_circleMap,smul_eq_mul]
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hd : Continuous (fun p : X × ℝ =>
      ∏ j : Fin 4, (circleMap 0 R p.2-q p.1 j)) := by fun_prop
  have hn : Continuous (fun p : X × ℝ =>
      Complex.exp ((x p.1:ℂ)*circleMap 0 R p.2)*(circleMap 0 R p.2-ω p.1)) := by
    fun_prop
  exact (by fun_prop : Continuous (fun p : X × ℝ => circleMap 0 R p.2*Complex.I)).mul
    (hn.div hd (fun p => polar_circle_denominator_ne (q p.1) R (hR p.1) p.2))

theorem polarGeneralProfile_continuous_family
    {X : Type*} [TopologicalSpace X]
    (η : ℝ) (P : Polynomial ℝ) (ω : X → ℂ) (q : X → (Fin 4 → ℂ)) (R : ℝ)
    (hω : Continuous ω) (hq : Continuous q)
    (hR : ∀ p j, ‖q p j‖ < R) :
    Continuous (fun p => polarGeneralProfile η P (q p) R (ω p)) := by
  unfold polarGeneralProfile
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hinner : Continuous (fun p : X × ℝ =>
      polarGeneralInverseContour p.2 (ω p.1) (q p.1) R) :=
    polarGeneralInverseContour_continuous_family Prod.snd (ω ∘ Prod.fst)
      (q ∘ Prod.fst) R continuous_snd (hω.comp continuous_fst)
      (hq.comp continuous_fst) (fun p j => hR p.1 j)
  exact (by fun_prop : Continuous (fun p : X × ℝ =>
    ((Polynomial.eval (1-p.2/η:ℝ) P:ℝ):ℂ))).mul hinner

theorem polarGeneralGeneratorContour_continuous_family
    {X : Type*} [TopologicalSpace X]
    (η : ℝ) (P : Polynomial ℝ) (q : X → (Fin 4 → ℂ)) (innerR outerR : ℝ)
    (hq : Continuous q) (hinner : ∀ p j, ‖q p j‖ < innerR)
    (houter : ∀ p j, ‖q p j‖ < outerR) :
    Continuous (fun p => polarGeneralGeneratorContour η P (q p) innerR outerR) := by
  unfold polarGeneralGeneratorContour circleIntegral
  simp only [deriv_circleMap,smul_eq_mul]
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hprofile : Continuous (fun p : X × ℝ =>
      polarGeneralProfile η P (q p.1) innerR (circleMap 0 outerR p.2)) :=
    polarGeneralProfile_continuous_family η P (circleMap 0 outerR ∘ Prod.snd)
      (q ∘ Prod.fst) innerR ((continuous_circleMap 0 outerR).comp continuous_snd)
      (hq.comp continuous_fst) (fun p j => hinner p.1 j)
  have hd : Continuous (fun p : X × ℝ =>
      ∏ j : Fin 4, (circleMap 0 outerR p.2-q p.1 j)) := by fun_prop
  have hn : Continuous (fun p : X × ℝ =>
      Complex.exp (circleMap 0 outerR p.2-q p.1 2-q p.1 3)) := by fun_prop
  exact (by fun_prop : Continuous (fun p : X × ℝ => circleMap 0 outerR p.2*Complex.I)).mul
    ((hn.div hd (fun p => polar_circle_denominator_ne (q p.1) outerR
      (houter p.1) p.2)).mul (hprofile.pow 2))

def polarCircleDomain (innerR outerR : ℝ) : Set (Fin 4 → ℂ) :=
  {q | ∀ j, ‖q j‖ < innerR ∧ ‖q j‖ < outerR}

theorem polarCircleDomain_isOpen (innerR outerR : ℝ) :
    IsOpen (polarCircleDomain innerR outerR) := by
  unfold polarCircleDomain
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  change IsOpen ({q : Fin 4 → ℂ | ‖q j‖ < innerR} ∩ {q : Fin 4 → ℂ | ‖q j‖ < outerR})
  exact (isOpen_lt (continuous_apply j).norm continuous_const).inter
    (isOpen_lt (continuous_apply j).norm continuous_const)

theorem polarGeneralGeneratorContour_continuousOn (η : ℝ) (P : Polynomial ℝ)
    (innerR outerR : ℝ) :
    ContinuousOn (fun q => polarGeneralGeneratorContour η P q innerR outerR)
      (polarCircleDomain innerR outerR) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact polarGeneralGeneratorContour_continuous_family η P
    (fun q : polarCircleDomain innerR outerR => q.1) innerR outerR
    continuous_subtype_val (fun q j => (q.2 j).1) (fun q j => (q.2 j).2)

/-- The actual circle formula has a joint limit at every collection of knots,
including repeated knots. Injectivity is not a hypothesis. -/
theorem polarGeneralGeneratorContour_continuousAt (η : ℝ) (P : Polynomial ℝ)
    (q : Fin 4 → ℂ) (innerR outerR : ℝ)
    (hinner : ∀ j, ‖q j‖ < innerR) (houter : ∀ j, ‖q j‖ < outerR) :
    ContinuousAt (fun q => polarGeneralGeneratorContour η P q innerR outerR) q := by
  apply (polarGeneralGeneratorContour_continuousOn η P innerR outerR).continuousAt
  exact (polarCircleDomain_isOpen innerR outerR).mem_nhds
    (fun j => ⟨hinner j,houter j⟩)

/-- The residue expression approaches the regular circle value as the knots
coalesce along their genuine injective domain. -/
theorem polarGeneralResidues_joint_limit (η : ℝ) (P : Polynomial ℝ)
    (q : Fin 4 → ℂ) (innerR outerR : ℝ)
    (hinner : ∀ j, ‖q j‖ < innerR) (houter : ∀ j, ‖q j‖ < outerR) :
    Tendsto (fun q' : Fin 4 → ℂ => ∑ j : Fin 4,
      Complex.exp (q' j-q' 2-q' 3)*
        (polarGeneralTripleProfile η P (fun k => q' (j.succAbove k)) innerR)^2 /
          polarPoleDenominator q' j)
      (𝓝[{q' | Function.Injective q'}] q)
      (𝓝 (polarGeneralGeneratorContour η P q innerR outerR)) := by
  have ht : Tendsto (fun q' : Fin 4 → ℂ =>
      polarGeneralGeneratorContour η P q' innerR outerR)
      (𝓝[{q' | Function.Injective q'}] q)
      (𝓝 (polarGeneralGeneratorContour η P q innerR outerR)) :=
    (polarGeneralGeneratorContour_continuousAt η P q innerR outerR
      hinner houter).tendsto.mono_left inf_le_left
  apply ht.congr'
  have hd : ∀ᶠ q' in 𝓝 q, q' ∈ polarCircleDomain innerR outerR :=
    (polarCircleDomain_isOpen innerR outerR).mem_nhds (fun j => ⟨hinner j,houter j⟩)
  filter_upwards [hd.filter_mono inf_le_left, self_mem_nhdsWithin] with q' hq' hInjective
  exact polarGeneralGeneratorContour_triple_residues η P q' innerR outerR hInjective
    (fun j => (hq' j).1) (fun j => (hq' j).2)

end Sechstmoment
