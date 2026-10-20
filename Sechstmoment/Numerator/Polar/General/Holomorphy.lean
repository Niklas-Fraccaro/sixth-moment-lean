import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Sechstmoment.Analysis.Complex.PartialDerivative
import Sechstmoment.Analysis.Integration.ComplexParameter
import Sechstmoment.Numerator.Polar.General.Coincidence

namespace Sechstmoment
open Complex Metric MeasureTheory Set
open scoped BigOperators Topology

set_option maxHeartbeats 1000000

def polarInnerDomain (R : ℝ) : Set ((Fin 4 → ℂ) × ℂ) :=
  {p | ∀ j, ‖p.1 j‖ < R}

theorem polarInnerDomain_isOpen (R : ℝ) : IsOpen (polarInnerDomain R) := by
  unfold polarInnerDomain
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt ((continuous_apply j).comp continuous_fst).norm continuous_const

noncomputable def polarInnerCircleExtended (R : ℝ)
    (p : ((Fin 4 → ℂ) × ℂ) × (ℂ × ℂ)) : ℂ :=
  let u := (R : ℂ)*Complex.exp (p.2.2*Complex.I)
  u*Complex.I*(Complex.exp (p.2.1*u)*(u-p.1.2)/(∏ j : Fin 4, (u-p.1.1 j)))

theorem polarInnerCircleExtended_contDiffAt (R : ℝ)
    (q : Fin 4 → ℂ) (ω : ℂ) (a θ : ℝ) (hR : ∀ j, ‖q j‖ < R) :
    ContDiffAt ℂ 1 (polarInnerCircleExtended R) ((q,ω),((a:ℂ),(θ:ℂ))) := by
  have hn : (∏ j : Fin 4, ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)-q j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply sub_ne_zero.mpr
    have hw : q j ∈ ball (0:ℂ) R := by simpa [mem_ball,dist_eq_norm] using hR j
    simpa only [circleMap,zero_add] using circleMap_ne_mem_ball hw θ
  unfold polarInnerCircleExtended
  apply ContDiffAt.mul
  · fun_prop
  · apply ContDiffAt.div
    · fun_prop
    · fun_prop
    · exact hn

noncomputable def polarInnerCircleFamily (R : ℝ) :
    ComplexIntegralFamily (polarInnerDomain R) (ℝ × ℝ) where
  value p x := polarInnerCircleExtended R (p,((x.1:ℂ),(x.2:ℂ)))
  derivative p x := complexFirstFDeriv (polarInnerCircleExtended R)
    (p,((x.1:ℂ),(x.2:ℂ)))
  continuous_value := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hg : Continuous (fun p : polarInnerDomain R × (ℝ × ℝ) =>
        (p.1.1,((p.2.1:ℂ),(p.2.2:ℂ)))) := by fun_prop
    exact (polarInnerCircleExtended_contDiffAt R p.1.1.1 p.1.1.2 p.2.1 p.2.2 p.1.2).continuousAt.comp
      (f := fun p : polarInnerDomain R × (ℝ × ℝ) => (p.1.1,((p.2.1:ℂ),(p.2.2:ℂ))))
      (x := p) hg.continuousAt
  continuous_derivative := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hg : Continuous (fun p : polarInnerDomain R × (ℝ × ℝ) =>
        (p.1.1,((p.2.1:ℂ),(p.2.2:ℂ)))) := by fun_prop
    exact (complexFirstFDeriv_continuousAt _ _
      (polarInnerCircleExtended_contDiffAt R p.1.1.1 p.1.1.2 p.2.1 p.2.2 p.1.2)).comp
      (f := fun p : polarInnerDomain R × (ℝ × ℝ) => (p.1.1,((p.2.1:ℂ),(p.2.2:ℂ))))
      (x := p) hg.continuousAt
  hasFDerivAt := by
    intro p hp x
    exact complexFirstFDeriv_hasFDerivAt _ _
      ((polarInnerCircleExtended_contDiffAt R p.1 p.2 x.1 x.2 hp).differentiableAt (by norm_num))

noncomputable def polarInnerContourFamily (R : ℝ) :
    ComplexIntegralFamily (polarInnerDomain R) ℝ :=
  ((polarInnerCircleFamily R).intervalIntegral (polarInnerDomain_isOpen R)
    0 (2*Real.pi) Real.two_pi_pos.le).mulAux
      (fun _ => (2*(Real.pi:ℂ)*Complex.I)⁻¹) continuous_const

theorem polarInnerContourFamily_value (R : ℝ) (p : (Fin 4 → ℂ) × ℂ) (a : ℝ) :
    (polarInnerContourFamily R).value p a = polarGeneralInverseContour a p.2 p.1 R := by
  unfold polarInnerContourFamily ComplexIntegralFamily.mulAux
    ComplexIntegralFamily.intervalIntegral polarInnerCircleFamily polarGeneralInverseContour
    circleIntegral polarInnerCircleExtended
  simp only [deriv_circleMap,smul_eq_mul,circleMap,zero_add]

noncomputable def polarProfileFamily (η : ℝ) (P : Polynomial ℝ) (R : ℝ)
    (hη : 0 ≤ η) : ComplexIntegralFamily (polarInnerDomain R) Unit :=
  (((polarInnerContourFamily R).mulAux
    (fun a => ((Polynomial.eval (1-a/η:ℝ) P:ℝ):ℂ)) (by fun_prop)).reindexAux
      (fun p : Unit × ℝ => p.2) continuous_snd).intervalIntegral
        (polarInnerDomain_isOpen R) 0 η hη

theorem polarProfileFamily_value (η : ℝ) (P : Polynomial ℝ) (R : ℝ) (hη : 0 ≤ η)
    (p : (Fin 4 → ℂ) × ℂ) :
    (polarProfileFamily η P R hη).value p () = polarGeneralProfile η P p.1 R p.2 := by
  change (∫ a in (0:ℝ)..η, ((Polynomial.eval (1-a/η:ℝ) P:ℝ):ℂ)*
    (polarInnerContourFamily R).value p a) = _
  simp_rw [polarInnerContourFamily_value]
  rfl

attribute [irreducible] polarProfileFamily

theorem polarGeneralProfile_differentiableOn_joint (η : ℝ) (P : Polynomial ℝ)
    (R : ℝ) (hη : 0 ≤ η) :
    DifferentiableOn ℂ (fun p : (Fin 4 → ℂ) × ℂ => polarGeneralProfile η P p.1 R p.2)
      (polarInnerDomain R) := by
  intro p hp
  have h := ((polarProfileFamily η P R hη).hasFDerivAt p hp ()).differentiableAt
  have heq : (fun p => (polarProfileFamily η P R hη).value p ()) =
      (fun p => polarGeneralProfile η P p.1 R p.2) :=
    funext (fun p => polarProfileFamily_value η P R hη p)
  rw [heq] at h
  exact h.differentiableWithinAt

noncomputable def polarOuterProfileFamily (η : ℝ) (P : Polynomial ℝ)
    (innerR outerR : ℝ) (hη : 0 ≤ η) :
    ComplexIntegralFamily (polarCircleDomain innerR outerR) ℝ where
  value q θ := (polarProfileFamily η P innerR hη).value (q,circleMap 0 outerR θ) ()
  derivative q θ := ((polarProfileFamily η P innerR hη).derivative
    (q,circleMap 0 outerR θ) ()).comp (ContinuousLinearMap.inl ℂ (Fin 4 → ℂ) ℂ)
  continuous_value := by
    have hm : Continuous (fun p : polarCircleDomain innerR outerR × ℝ =>
        ((⟨(p.1.1,circleMap 0 outerR p.2),fun j => (p.1.2 j).1⟩ : polarInnerDomain innerR),())) := by
      fun_prop
    exact (polarProfileFamily η P innerR hη).continuous_value.comp hm
  continuous_derivative := by
    have hm : Continuous (fun p : polarCircleDomain innerR outerR × ℝ =>
        ((⟨(p.1.1,circleMap 0 outerR p.2),fun j => (p.1.2 j).1⟩ : polarInnerDomain innerR),())) := by
      fun_prop
    exact ((polarProfileFamily η P innerR hη).continuous_derivative.comp hm).clm_comp_const _
  hasFDerivAt := by
    intro q hq θ
    exact ((polarProfileFamily η P innerR hη).hasFDerivAt
      (q,circleMap 0 outerR θ) (fun j => (hq j).1) ()).comp q
        (f := fun y : Fin 4 → ℂ => (y,circleMap 0 outerR θ))
        (hasFDerivAt_prodMk_left q (circleMap 0 outerR θ))

noncomputable def polarOuterCircleExtended (R : ℝ) (p : (Fin 4 → ℂ) × ℂ) : ℂ :=
  let u := (R : ℂ)*Complex.exp (p.2*Complex.I)
  u*Complex.I*(Complex.exp (u-p.1 2-p.1 3)/(∏ j : Fin 4, (u-p.1 j)))

theorem polarOuterCircleExtended_contDiffAt (R : ℝ)
    (q : Fin 4 → ℂ) (θ : ℝ) (hR : ∀ j, ‖q j‖ < R) :
    ContDiffAt ℂ 1 (polarOuterCircleExtended R) (q,(θ:ℂ)) := by
  have hn : (∏ j : Fin 4, ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)-q j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply sub_ne_zero.mpr
    have hw : q j ∈ ball (0:ℂ) R := by simpa [mem_ball,dist_eq_norm] using hR j
    simpa only [circleMap,zero_add] using circleMap_ne_mem_ball hw θ
  unfold polarOuterCircleExtended
  apply ContDiffAt.mul
  · fun_prop
  · apply ContDiffAt.div
    · fun_prop
    · fun_prop
    · exact hn

noncomputable def polarOuterCircleFamily (innerR outerR : ℝ) :
    ComplexIntegralFamily (polarCircleDomain innerR outerR) ℝ where
  value q θ := polarOuterCircleExtended outerR (q,(θ:ℂ))
  derivative q θ := complexFirstFDeriv (polarOuterCircleExtended outerR) (q,(θ:ℂ))
  continuous_value := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hm : Continuous (fun p : polarCircleDomain innerR outerR × ℝ =>
        (p.1.1,(p.2:ℂ))) := by fun_prop
    exact (polarOuterCircleExtended_contDiffAt outerR p.1.1 p.2
      (fun j => (p.1.2 j).2)).continuousAt.comp
        (f := fun p : polarCircleDomain innerR outerR × ℝ => (p.1.1,(p.2:ℂ)))
        (x := p) hm.continuousAt
  continuous_derivative := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hm : Continuous (fun p : polarCircleDomain innerR outerR × ℝ =>
        (p.1.1,(p.2:ℂ))) := by fun_prop
    exact (complexFirstFDeriv_continuousAt _ _ (polarOuterCircleExtended_contDiffAt outerR
      p.1.1 p.2 (fun j => (p.1.2 j).2))).comp
        (f := fun p : polarCircleDomain innerR outerR × ℝ => (p.1.1,(p.2:ℂ)))
        (x := p) hm.continuousAt
  hasFDerivAt := by
    intro q hq θ
    exact complexFirstFDeriv_hasFDerivAt _ _
      ((polarOuterCircleExtended_contDiffAt outerR q θ (fun j => (hq j).2)).differentiableAt
        (by norm_num))

noncomputable def polarGeneratorFamily (η : ℝ) (P : Polynomial ℝ)
    (innerR outerR : ℝ) (hη : 0 ≤ η) :
    ComplexIntegralFamily (polarCircleDomain innerR outerR) Unit :=
  let profile := polarOuterProfileFamily η P innerR outerR hη
  (((polarOuterCircleFamily innerR outerR).mul (profile.mul profile)).reindexAux
    (fun p : Unit × ℝ => p.2) continuous_snd).intervalIntegral
      (polarCircleDomain_isOpen innerR outerR) 0 (2*Real.pi) Real.two_pi_pos.le |>.mulAux
        (fun _ => (2*(Real.pi:ℂ)*Complex.I)⁻¹) continuous_const

theorem polarGeneratorFamily_value (η : ℝ) (P : Polynomial ℝ)
    (innerR outerR : ℝ) (hη : 0 ≤ η) (q : Fin 4 → ℂ) :
    (polarGeneratorFamily η P innerR outerR hη).value q () =
      polarGeneralGeneratorContour η P q innerR outerR := by
  change (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
    (∫ θ in (0:ℝ)..2*Real.pi, polarOuterCircleExtended outerR (q,(θ:ℂ))*
      ((polarProfileFamily η P innerR hη).value (q,circleMap 0 outerR θ) ()*
        (polarProfileFamily η P innerR hη).value (q,circleMap 0 outerR θ) ())) = _
  simp_rw [polarProfileFamily_value]
  unfold polarGeneralGeneratorContour circleIntegral polarOuterCircleExtended
  simp only [deriv_circleMap,smul_eq_mul,circleMap,zero_add]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  ring

theorem polarGeneralGeneratorContour_differentiableOn (η : ℝ) (P : Polynomial ℝ)
    (innerR outerR : ℝ) (hη : 0 ≤ η) :
    DifferentiableOn ℂ (fun q => polarGeneralGeneratorContour η P q innerR outerR)
      (polarCircleDomain innerR outerR) := by
  intro q hq
  have h := ((polarGeneratorFamily η P innerR outerR hη).hasFDerivAt q hq ()).differentiableAt
  have heq : (fun q => (polarGeneratorFamily η P innerR outerR hη).value q ()) =
      (fun q => polarGeneralGeneratorContour η P q innerR outerR) :=
    funext (fun q => polarGeneratorFamily_value η P innerR outerR hη q)
  rw [heq] at h
  exact h.differentiableWithinAt

end Sechstmoment
