import Mathlib.Tactic
import Sechstmoment.Numerator.Polar.Mellin.Holomorphic

/-!
# Actual arithmetic multiplier on the profile contours

The principal term retains the genuine shifted Euler rest and the five
entangled zeta factors.  Normal convergence of the Euler rest proves
holomorphy in each amplifier variable on an open half-plane containing
every profile contour.  The bounds are independent of both imaginary
amplifier coordinates.
-/

namespace Sechstmoment

open Real Complex Set
open scoped BigOperators

noncomputable section

def principalAmplifierDomain (ε : ℝ) : Set ℂ := {u | ε/2 < u.re}

theorem principalAmplifierDomain_isOpen (ε : ℝ) :
    IsOpen (principalAmplifierDomain ε) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem polarArithmeticEntangledFactor_principal_differentiableOn_left
    {α : MomentShifts} {ε : ℝ} {v : ℂ}
    (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ ε/4) (hv : ε ≤ v.re) :
    DifferentiableOn ℂ (fun u => polarArithmeticEntangledFactor α u v 0)
      (principalAmplifierDomain ε) := by
  have hre (j : Fin 4) : -(ε/4) ≤ (α j).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
  have ha : ∀ i : Fin 3, DifferentiableOn ℂ
      (fun u => polarMellinLeftTriple α u 0 i) (principalAmplifierDomain ε) := by
    intro i
    fin_cases i <;> simp [polarMellinLeftTriple]
    fun_prop
  have hb : ∀ i : Fin 3, DifferentiableOn ℂ
      (fun u => polarMellinRightTriple α v 0 i) (principalAmplifierDomain ε) := by
    intro i
    exact differentiableOn_const _
  have haε : ∀ u ∈ principalAmplifierDomain ε, ∀ i : Fin 3,
      -ε < (polarMellinLeftTriple α u 0 i).re := by
    intro u hu i
    change ε/2 < u.re at hu
    fin_cases i <;> simp [polarMellinLeftTriple] <;> linarith [hre 0,hre 1]
  have hbε : ∀ u ∈ principalAmplifierDomain ε, ∀ i : Fin 3,
      -ε < (polarMellinRightTriple α v 0 i).re := by
    intro u _ i
    fin_cases i <;> simp [polarMellinRightTriple] <;> linarith [hre 2,hre 3]
  have hA := shiftedPolarEulerRest_differentiableOn (principalAmplifierDomain_isOpen ε)
    (fun u => polarMellinLeftTriple α u 0) (fun _ => polarMellinRightTriple α v 0)
    hε1 ha hb haε hbε
  have hZ : DifferentiableOn ℂ (fun u => polarEntangledZetaProduct α u v 0)
      (principalAmplifierDomain ε) := by
    unfold polarEntangledZetaProduct
    apply DifferentiableOn.fun_finsetProd
    intro i _ u hu
    have harg : 1 < (polarEntangledZetaArguments α u v 0 i).re := by
      change ε/2 < u.re at hu
      fin_cases i <;> simp [polarEntangledZetaArguments] <;>
        linarith [hre 0,hre 1,hre 2,hre 3]
    have hne : polarEntangledZetaArguments α u v 0 i ≠ 1 := by
      intro he
      rw [he,one_re] at harg
      exact lt_irrefl 1 harg
    have hdiff : DifferentiableAt ℂ (fun u => polarEntangledZetaArguments α u v 0 i) u := by
      unfold polarEntangledZetaArguments
      fin_cases i <;> simp <;> fun_prop
    exact ((differentiableAt_riemannZeta hne).comp u hdiff).differentiableWithinAt
  exact hA.mul hZ

theorem polarArithmeticEntangledFactor_principal_differentiableOn_right
    {α : MomentShifts} {ε : ℝ} {u : ℂ}
    (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ ε/4) (hu : ε ≤ u.re) :
    DifferentiableOn ℂ (fun v => polarArithmeticEntangledFactor α u v 0)
      (principalAmplifierDomain ε) := by
  have hre (j : Fin 4) : -(ε/4) ≤ (α j).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
  have ha : ∀ i : Fin 3, DifferentiableOn ℂ
      (fun v => polarMellinLeftTriple α u 0 i) (principalAmplifierDomain ε) := by
    intro i
    exact differentiableOn_const _
  have hb : ∀ i : Fin 3, DifferentiableOn ℂ
      (fun v => polarMellinRightTriple α v 0 i) (principalAmplifierDomain ε) := by
    intro i
    fin_cases i <;> simp [polarMellinRightTriple]
    fun_prop
  have haε : ∀ v ∈ principalAmplifierDomain ε, ∀ i : Fin 3,
      -ε < (polarMellinLeftTriple α u 0 i).re := by
    intro v _ i
    fin_cases i <;> simp [polarMellinLeftTriple] <;> linarith [hre 0,hre 1]
  have hbε : ∀ v ∈ principalAmplifierDomain ε, ∀ i : Fin 3,
      -ε < (polarMellinRightTriple α v 0 i).re := by
    intro v hv i
    change ε/2 < v.re at hv
    fin_cases i <;> simp [polarMellinRightTriple] <;> linarith [hre 2,hre 3]
  have hA := shiftedPolarEulerRest_differentiableOn (principalAmplifierDomain_isOpen ε)
    (fun _ => polarMellinLeftTriple α u 0) (fun v => polarMellinRightTriple α v 0)
    hε1 ha hb haε hbε
  have hZ : DifferentiableOn ℂ (fun v => polarEntangledZetaProduct α u v 0)
      (principalAmplifierDomain ε) := by
    unfold polarEntangledZetaProduct
    apply DifferentiableOn.fun_finsetProd
    intro i _ v hv
    have harg : 1 < (polarEntangledZetaArguments α u v 0 i).re := by
      change ε/2 < v.re at hv
      fin_cases i <;> simp [polarEntangledZetaArguments] <;>
        linarith [hre 0,hre 1,hre 2,hre 3]
    have hne : polarEntangledZetaArguments α u v 0 i ≠ 1 := by
      intro he
      rw [he,one_re] at harg
      exact lt_irrefl 1 harg
    have hdiff : DifferentiableAt ℂ (fun v => polarEntangledZetaArguments α u v 0 i) v := by
      unfold polarEntangledZetaArguments
      fin_cases i <;> simp <;> fun_prop
    exact ((differentiableAt_riemannZeta hne).comp v hdiff).differentiableWithinAt
  exact hA.mul hZ

theorem polarMellinRemovedKernel_principal_differentiableOn_left
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {ε : ℝ} {v : ℂ}
    (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4) (hv : ε ≤ v.re) :
    DifferentiableOn ℂ (fun u => polarMellinRemovedKernel T σ m u v 0)
      (principalAmplifierDomain ε) := by
  exact (polarArithmeticEntangledFactor_principal_differentiableOn_left hε hε1
    (fun j => bblrSixShifts_norm_le _ hα m j) hv).mul (differentiableOn_const _)

theorem polarMellinRemovedKernel_principal_differentiableOn_right
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {ε : ℝ} {u : ℂ}
    (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4) (hu : ε ≤ u.re) :
    DifferentiableOn ℂ (fun v => polarMellinRemovedKernel T σ m u v 0)
      (principalAmplifierDomain ε) := by
  exact (polarArithmeticEntangledFactor_principal_differentiableOn_right hε hε1
    (fun j => bblrSixShifts_norm_le _ hα m j) hu).mul (differentiableOn_const _)

def actualPrincipalArithmeticMajorant (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (ε : ℝ) : ℝ :=
  polarArithmeticEntangledMajorant ε * ‖purePolarRemovedIntegrand T σ m 0‖

theorem actualPrincipalArithmeticMajorant_nonneg
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) (ε : ℝ) :
    0 ≤ actualPrincipalArithmeticMajorant T σ m ε :=
  mul_nonneg (polarArithmeticEntangledMajorant_nonneg ε) (norm_nonneg _)

theorem polarMellinRemovedKernel_principal_norm_bound
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {ε : ℝ} {u v : ℂ}
    (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4)
    (hu : ε ≤ u.re) (hv : ε ≤ v.re) :
    ‖polarMellinRemovedKernel T σ m u v 0‖ ≤
      actualPrincipalArithmeticMajorant T σ m ε := by
  unfold polarMellinRemovedKernel actualPrincipalArithmeticMajorant
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (polarArithmeticEntangledFactor_norm_bound hε hε1
      (fun j => bblrSixShifts_norm_le _ hα m j) hu hv (by simp; linarith))
    (norm_nonneg _)

theorem polarMellinRemovedKernel_principal_norm_bound_pure
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {ε : ℝ} {u v : ℂ}
    (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4)
    (hu : ε ≤ u.re) (hv : ε ≤ v.re)
    (hρ : ∀ ij : Fin 2 × Fin 2, purePolarRoot T σ (m,ij) ≠ 0) :
    ‖polarMellinRemovedKernel T σ m u v 0‖ ≤
      polarArithmeticEntangledMajorant ε * ‖purePolarZetaProduct T σ m 0‖ := by
  rw [polarMellinRemovedKernel_zero T σ m u v hρ, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (polarArithmeticEntangledFactor_norm_bound hε hε1
      (fun j => bblrSixShifts_norm_le _ hα m j) hu hv (by simp; linarith))
    (norm_nonneg _)

theorem polarMellinRemovedKernel_principal_uniform_norm_bound
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℂ, ε ≤ u.re → ε ≤ v.re →
      ‖polarMellinRemovedKernel T σ m u v 0‖ ≤ C := by
  exact ⟨actualPrincipalArithmeticMajorant T σ m ε,
    actualPrincipalArithmeticMajorant_nonneg T σ m ε,
    fun _ _ hu hv => polarMellinRemovedKernel_principal_norm_bound
      T σ m hε hε1 hα hu hv⟩

theorem polarMellinRemovedKernel_principal_jointline_continuous
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {ε c d : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ ε/4)
    (hc : ε ≤ c) (hd : ε ≤ d) :
    Continuous (fun y : ℝ × ℝ => polarMellinRemovedKernel T σ m
      ((c:ℂ)+(y.1:ℂ)*I) ((d:ℂ)+(y.2:ℂ)*I) 0) := by
  let α : MomentShifts := Source.bblrSixShifts (rawMomentShifts T σ) m
  have hshift (j : Fin 4) : ‖α j‖ ≤ ε/4 := bblrSixShifts_norm_le _ hα m j
  have hcont : Continuous (fun y : ℝ × ℝ => polarArithmeticEntangledFactor α
      ((c:ℂ)+(y.1:ℂ)*I) ((d:ℂ)+(y.2:ℂ)*I) 0) := by
    rw [continuous_iff_continuousAt]
    intro y
    let u : ℂ := (c:ℂ)+(y.1:ℂ)*I
    let v : ℂ := (d:ℂ)+(y.2:ℂ)*I
    have hu : ε ≤ u.re := by simpa [u] using hc
    have hv : ε ≤ v.re := by simpa [v] using hd
    obtain ⟨ha,hb⟩ := polarMellinTriples_re_lower_bound hε hshift hu hv
      (by simp; linarith : -ε/2 ≤ (0:ℂ).re)
    have hdomain : (polarMellinLeftTriple α u 0,polarMellinRightTriple α v 0) ∈
        polarShiftDomain ε := ⟨ha,hb⟩
    have hmap : Continuous (fun y : ℝ × ℝ =>
        (polarMellinLeftTriple α ((c:ℂ)+(y.1:ℂ)*I) 0,
          polarMellinRightTriple α ((d:ℂ)+(y.2:ℂ)*I) 0)) := by
      unfold polarMellinLeftTriple polarMellinRightTriple
      fun_prop
    have hA : ContinuousAt (fun y : ℝ × ℝ =>
        shiftedPolarEulerRest (polarMellinLeftTriple α ((c:ℂ)+(y.1:ℂ)*I) 0)
          (polarMellinRightTriple α ((d:ℂ)+(y.2:ℂ)*I) 0)) y :=
      ContinuousAt.comp (f := fun y : ℝ × ℝ =>
        (polarMellinLeftTriple α ((c:ℂ)+(y.1:ℂ)*I) 0,
          polarMellinRightTriple α ((d:ℂ)+(y.2:ℂ)*I) 0))
        (g := fun ab : PolarShiftSpace => shiftedPolarEulerRest ab.1 ab.2)
        ((shiftedPolarEulerRest_continuousOn hε1).continuousAt
          ((polarShiftDomain_isOpen ε).mem_nhds hdomain)) hmap.continuousAt
    have hZ : ContinuousAt (fun y : ℝ × ℝ =>
        polarEntangledZetaProduct α ((c:ℂ)+(y.1:ℂ)*I)
          ((d:ℂ)+(y.2:ℂ)*I) 0) y := by
      unfold polarEntangledZetaProduct
      apply tendsto_finsetProd
      intro i _
      have hne : polarEntangledZetaArguments α u v 0 i ≠ 1 := by
        intro he
        have hr := polarEntangledZetaArguments_re_lower_bound hε hshift hu hv
          (by simp; linarith : -ε/2 ≤ (0:ℂ).re) i
        rw [he,one_re] at hr
        linarith
      have hzi : ContinuousAt (fun y : ℝ × ℝ =>
          polarEntangledZetaArguments α ((c:ℂ)+(y.1:ℂ)*I)
            ((d:ℂ)+(y.2:ℂ)*I) 0 i) y := by
        unfold polarEntangledZetaArguments
        fin_cases i <;> fun_prop
      exact ContinuousAt.comp (f := fun y : ℝ × ℝ =>
        polarEntangledZetaArguments α ((c:ℂ)+(y.1:ℂ)*I)
          ((d:ℂ)+(y.2:ℂ)*I) 0 i) (g := riemannZeta)
        (differentiableAt_riemannZeta hne).continuousAt hzi
    exact hA.mul hZ
  exact hcont.mul continuous_const

end

end Sechstmoment
