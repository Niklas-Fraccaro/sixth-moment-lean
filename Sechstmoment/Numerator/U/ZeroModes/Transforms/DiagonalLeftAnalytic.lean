import Sechstmoment.Numerator.Polar.ContourShift
import Sechstmoment.Numerator.U.ZeroModes.Transforms.DiagonalBGlobalBounds

/-! Holomorphic pole-removed numerator for the actual fixed-amplifier
diagonal, on an open strip containing Re(z)=-1/8 through Re(z)=1. -/

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03DiagonalEulerDenominatorArgument (α : MomentShifts) (z : ℂ) : ℂ :=
  2+α 0+α 1+α 2+α 3+4*z

def a03DiagonalEulerKernel (G : ℂ→ℂ) (α : MomentShifts) (a b : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  G z/z*(t/(2*Real.pi):ℂ)^(2*z)*((a*b:ℕ):ℂ)^(-(1+z))*
    (bblrAArithmetic (α 0+z) (α 1+z) (α 2+z) (α 3+z)*
      bblrBFactorAt (α 0) (α 1) (α 2) (α 3) z a*
      bblrBFactorAt (α 2) (α 3) (α 0) (α 1) z b)

def a03DiagonalLeftDomain : Set ℂ := {z : ℂ | -(9/64:ℝ)<z.re}

def a03DiagonalRemovedNumerator (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (a b : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  let α := bblrSixShifts (rawMomentShifts T σ) m
  purePolarRemovedIntegrand T σ m z*
    (riemannZeta (a03DiagonalEulerDenominatorArgument α z))⁻¹*
      a03DiagonalBFactorRational (α 0) (α 1) (α 2) (α 3) z a*
      a03DiagonalBFactorRational (α 2) (α 3) (α 0) (α 1) z b*
      (t/(2*Real.pi):ℂ)^(2*z)*((a*b:ℕ):ℂ)^(-(1+z))

theorem a03DiagonalEulerDenominator_re_lower {α : MomentShifts}
    (hα : ∀ j : Fin 4,‖α j‖≤1/64) {z : ℂ} (hz : -(1/8:ℝ)≤z.re) :
    (7/5:ℝ)≤(a03DiagonalEulerDenominatorArgument α z).re := by
  have hr (j : Fin 4) : -(1/64:ℝ)≤(α j).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
  unfold a03DiagonalEulerDenominatorArgument
  norm_num [add_re,mul_re]
  linarith [hr 0,hr 1,hr 2,hr 3]

theorem a03DiagonalEulerDenominator_re_gt_one {α : MomentShifts}
    (hα : ∀ j : Fin 4,‖α j‖≤1/64) {z : ℂ} (hz : z∈a03DiagonalLeftDomain) :
    1<(a03DiagonalEulerDenominatorArgument α z).re := by
  have hr (j : Fin 4) : -(1/64:ℝ)≤(α j).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
  change -(9/64:ℝ)<z.re at hz
  unfold a03DiagonalEulerDenominatorArgument
  norm_num [add_re,mul_re]
  linarith [hr 0,hr 1,hr 2,hr 3]

theorem a03DiagonalRemovedNumerator_differentiableOn {T : ℝ} (σ : MomentShifts)
    (hα : ∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) (m : Fin 6)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {t : ℝ} (ht : 0<t) :
    DifferentiableOn ℂ (a03DiagonalRemovedNumerator T σ m a b t) a03DiagonalLeftDomain := by
  let α := bblrSixShifts (rawMomentShifts T σ) m
  have hsmall (j : Fin 4) : ‖α j‖≤1/64 := bblrSixShifts_norm_le _ hα m j
  have hdarg : Differentiable ℂ (a03DiagonalEulerDenominatorArgument α) := by
    unfold a03DiagonalEulerDenominatorArgument
    fun_prop
  have hInv : DifferentiableOn ℂ
      (fun z => (riemannZeta (a03DiagonalEulerDenominatorArgument α z))⁻¹) a03DiagonalLeftDomain := by
    intro z hz
    have hRe := a03DiagonalEulerDenominator_re_gt_one hsmall hz
    exact (((differentiableAt_riemannZeta (by intro he; rw [he,one_re] at hRe; linarith)).comp
      z (hdarg z)).inv (riemannZeta_ne_zero_of_one_lt_re hRe)).differentiableWithinAt
  have hB1 : DifferentiableOn ℂ
      (fun z => a03DiagonalBFactorRational (α 0) (α 1) (α 2) (α 3) z a) a03DiagonalLeftDomain := by
    intro z hz
    apply (a03DiagonalBFactorRational_differentiableAt _ _ _ _ _ _).differentiableWithinAt
    convert a03DiagonalEulerDenominator_re_gt_one hsmall hz using 1
    unfold a03DiagonalEulerDenominatorArgument
    congr 1
    ring
  have hB2 : DifferentiableOn ℂ
      (fun z => a03DiagonalBFactorRational (α 2) (α 3) (α 0) (α 1) z b) a03DiagonalLeftDomain := by
    intro z hz
    apply (a03DiagonalBFactorRational_differentiableAt _ _ _ _ _ _).differentiableWithinAt
    convert a03DiagonalEulerDenominator_re_gt_one hsmall hz using 1
    unfold a03DiagonalEulerDenominatorArgument
    congr 1
    ring
  have hTime : Differentiable ℂ (fun z : ℂ => (t/(2*Real.pi):ℂ)^(2*z)) :=
    (by fun_prop : Differentiable ℂ (fun z : ℂ => 2*z)).const_cpow
      (Or.inl (div_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))
  have hAmp : Differentiable ℂ (fun z : ℂ => ((a*b:ℕ):ℂ)^(-(1+z))) :=
    (by fun_prop : Differentiable ℂ (fun z : ℂ => -(1+z))).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (mul_ne_zero ha hb)))
  exact (((((purePolarRemovedIntegrand_differentiable T σ m).differentiableOn.mul hInv).mul hB1).mul hB2).mul hTime.differentiableOn).mul hAmp.differentiableOn

theorem a03DiagonalArithmetic_eq_pureQuotient (T : ℝ) (σ : MomentShifts) (m : Fin 6) (z : ℂ) :
    let α := bblrSixShifts (rawMomentShifts T σ) m
    bblrAArithmetic (α 0+z) (α 1+z) (α 2+z) (α 3+z)=
      purePolarZetaProduct T σ m z/riemannZeta (a03DiagonalEulerDenominatorArgument α z) := by
  dsimp only
  let α := bblrSixShifts (rawMomentShifts T σ) m
  have hp : purePolarZetaProduct T σ m z=
      riemannZeta (1+(α 0+z)+(α 2+z))*riemannZeta (1+(α 0+z)+(α 3+z))*
        riemannZeta (1+(α 1+z)+(α 2+z))*riemannZeta (1+(α 1+z)+(α 3+z)) := by
    unfold purePolarZetaProduct
    simp_rw [purePolarZetaArgument_eq_source]
    rw [Fintype.prod_prod_type]
    simp only [Fin.prod_univ_two,purePolarLeft,purePolarRight]
    change (riemannZeta (1+2*z+α 0+α 2)*riemannZeta (1+2*z+α 0+α 3))*
      (riemannZeta (1+2*z+α 1+α 2)*riemannZeta (1+2*z+α 1+α 3))=_
    have he (i j : Fin 4) : 1+2*z+α i+α j=1+(α i+z)+(α j+z) := by ring
    rw [he 0 2,he 0 3,he 1 2,he 1 3]
    ring
  rw [hp]
  unfold bblrAArithmetic a03DiagonalEulerDenominatorArgument
  congr 2
  ring

theorem a03DiagonalRemovedNumerator_eq_kernel {T : ℝ} (σ : MomentShifts)
    (hα : ∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) (m : Fin 6)
    (a b : ℕ) (t : ℝ)
    (hρ : ∀ ij : Fin 2 × Fin 2,purePolarRoot T σ (m,ij)≠0)
    {z : ℂ} (hz : -(1/8:ℝ)≤z.re)
    (hoff : ∀ ij : Fin 2 × Fin 2,z≠purePolarRoot T σ (m,ij)) :
    a03DiagonalRemovedNumerator T σ m a b t z/z=
      a03DiagonalEulerKernel (polarPoleKiller T σ)
        (bblrSixShifts (rawMomentShifts T σ) m) a b t z := by
  have hs (j : Fin 4) := bblrSixShifts_norm_le _ hα m j
  unfold a03DiagonalRemovedNumerator a03DiagonalEulerKernel
  rw [purePolarRemovedIntegrand_eq T σ m hρ hoff,a03DiagonalArithmetic_eq_pureQuotient]
  rw [bblrBFactorAt_eq_rational _ _ _ _ _ (hs 0) (hs 1) (hs 2) (hs 3) hz,
    bblrBFactorAt_eq_rational _ _ _ _ _ (hs 2) (hs 3) (hs 0) (hs 1) hz]
  ring

theorem bblrBFactorAt_zero (α β γ δ : ℂ) (a : ℕ) :
    bblrBFactorAt α β γ δ 0 a=bblrBFactor α β γ δ a := by
  unfold bblrBFactorAt bblrBFactor Finsupp.prod
  simp_rw [bblrBPrimeFactorAt_zero]

theorem a03DiagonalRemovedNumerator_zero {T : ℝ} (σ : MomentShifts)
    (hα : ∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) (m : Fin 6)
    {a b : ℕ} (_ha : a≠0) (_hb : b≠0) (t : ℝ)
    (hρ : ∀ ij : Fin 2 × Fin 2,purePolarRoot T σ (m,ij)≠0) :
    a03DiagonalRemovedNumerator T σ m a b t 0=
      ((a*b:ℕ):ℂ)^(-1:ℂ)*
        bblrZArithmetic (bblrSixShifts (rawMomentShifts T σ) m 0)
          (bblrSixShifts (rawMomentShifts T σ) m 1)
          (bblrSixShifts (rawMomentShifts T σ) m 2)
          (bblrSixShifts (rawMomentShifts T σ) m 3) a b := by
  have hs (j : Fin 4) := bblrSixShifts_norm_le _ hα m j
  unfold a03DiagonalRemovedNumerator bblrZArithmetic
  dsimp only
  rw [purePolarRemovedIntegrand_eq T σ m hρ (fun ij => (hρ ij).symm),polarPoleKiller_zero,one_mul]
  rw [←bblrBFactorAt_eq_rational _ _ _ _ 0 (hs 0) (hs 1) (hs 2) (hs 3) (by norm_num),
    ←bblrBFactorAt_eq_rational _ _ _ _ 0 (hs 2) (hs 3) (hs 0) (hs 1) (by norm_num),
    bblrBFactorAt_zero,bblrBFactorAt_zero]
  simp only [mul_zero,Complex.cpow_zero,mul_one,add_zero]
  have hA := a03DiagonalArithmetic_eq_pureQuotient T σ m 0
  dsimp only at hA
  simp only [add_zero] at hA
  rw [hA]
  ring

end
end Sechstmoment
