import Mathlib.Tactic
import Sechstmoment.Numerator.Polar.EulerMellinKernel


namespace Sechstmoment

open Real Complex Set
open scoped BigOperators

noncomputable section

def polarMellinHolomorphicDomain (δ : ℝ) : Set ℂ := {z | -3*δ/4 < z.re}

theorem polarMellinHolomorphicDomain_isOpen (δ : ℝ) :
    IsOpen (polarMellinHolomorphicDomain δ) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem polarArithmeticEntangledFactor_differentiableOn {α : MomentShifts}
    {δ : ℝ} {u v : ℂ} (hδ : 0 < δ) (hδ1 : δ < 1/4)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) :
    DifferentiableOn ℂ (polarArithmeticEntangledFactor α u v)
      (polarMellinHolomorphicDomain δ) := by
  have hre (j : Fin 4) : -(δ/4) ≤ (α j).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
  have ha : ∀ i : Fin 3, DifferentiableOn ℂ
      (fun z => polarMellinLeftTriple α u z i) (polarMellinHolomorphicDomain δ) := by
    intro i
    fin_cases i <;> simp [polarMellinLeftTriple] <;> fun_prop
  have hb : ∀ i : Fin 3, DifferentiableOn ℂ
      (fun z => polarMellinRightTriple α v z i) (polarMellinHolomorphicDomain δ) := by
    intro i
    fin_cases i <;> simp [polarMellinRightTriple] <;> fun_prop
  have haδ : ∀ z ∈ polarMellinHolomorphicDomain δ, ∀ i : Fin 3,
      -δ < (polarMellinLeftTriple α u z i).re := by
    intro z hz i
    change -3*δ/4 < z.re at hz
    fin_cases i <;> simp [polarMellinLeftTriple] <;> linarith [hre 0,hre 1]
  have hbδ : ∀ z ∈ polarMellinHolomorphicDomain δ, ∀ i : Fin 3,
      -δ < (polarMellinRightTriple α v z i).re := by
    intro z hz i
    change -3*δ/4 < z.re at hz
    fin_cases i <;> simp [polarMellinRightTriple] <;> linarith [hre 2,hre 3]
  have hA := shiftedPolarEulerRest_differentiableOn (polarMellinHolomorphicDomain_isOpen δ)
    (fun z => polarMellinLeftTriple α u z) (fun z => polarMellinRightTriple α v z)
    hδ1 ha hb haδ hbδ
  have hZ : DifferentiableOn ℂ (polarEntangledZetaProduct α u v)
      (polarMellinHolomorphicDomain δ) := by
    unfold polarEntangledZetaProduct
    apply DifferentiableOn.fun_finsetProd
    intro i _ z hz
    have harg : 1 < (polarEntangledZetaArguments α u v z i).re := by
      change -3*δ/4 < z.re at hz
      fin_cases i <;> simp [polarEntangledZetaArguments] <;>
        linarith [hre 0,hre 1,hre 2,hre 3]
    have hne : polarEntangledZetaArguments α u v z i ≠ 1 := by
      intro he
      rw [he,one_re] at harg
      exact lt_irrefl 1 harg
    have hdiff : DifferentiableAt ℂ (fun z => polarEntangledZetaArguments α u v z i) z := by
      unfold polarEntangledZetaArguments
      fin_cases i <;> simp <;> fun_prop
    exact ((differentiableAt_riemannZeta hne).comp z hdiff).differentiableWithinAt
  exact hA.mul hZ

def polarMellinRemovedKernel (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (u v z : ℂ) : ℂ :=
  polarArithmeticEntangledFactor (Source.bblrSixShifts (rawMomentShifts T σ) m) u v z*
    purePolarRemovedIntegrand T σ m z

theorem polarMellinRemovedKernel_differentiableOn
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {δ : ℝ} {u v : ℂ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) :
    DifferentiableOn ℂ (polarMellinRemovedKernel T σ m u v)
      (polarMellinHolomorphicDomain δ) :=
  (polarArithmeticEntangledFactor_differentiableOn hδ hδ1
    (fun j => bblrSixShifts_norm_le _ hα m j) hu hv).mul
      (purePolarRemovedIntegrand_differentiable T σ m).differentiableOn

theorem polarMellinRemovedKernel_eq
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) (u v : ℂ)
    (hρ : ∀ ij : Fin 2 × Fin 2, purePolarRoot T σ (m,ij) ≠ 0)
    {z : ℂ} (hz : ∀ ij : Fin 2 × Fin 2, z ≠ purePolarRoot T σ (m,ij)) :
    polarMellinRemovedKernel T σ m u v z = polarMellinArithmeticKernel T σ m u v z := by
  unfold polarMellinRemovedKernel polarMellinArithmeticKernel
  rw [purePolarRemovedIntegrand_eq T σ m hρ hz]

theorem polarMellinRemovedKernel_zero
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) (u v : ℂ)
    (hρ : ∀ ij : Fin 2 × Fin 2, purePolarRoot T σ (m,ij) ≠ 0) :
    polarMellinRemovedKernel T σ m u v 0 =
      polarArithmeticEntangledFactor (Source.bblrSixShifts (rawMomentShifts T σ) m) u v 0*
        purePolarZetaProduct T σ m 0 := by
  rw [polarMellinRemovedKernel_eq T σ m u v hρ (fun ij => (hρ ij).symm)]
  simp only [polarMellinArithmeticKernel,polarPoleKiller_zero,one_mul]

end

end Sechstmoment
