import Mathlib.Tactic
import Sechstmoment.Numerator.Polar.PoleKiller
import Sechstmoment.Zeta.Regularized

/-!
# Holomorphic removal of the actual four pure zeta poles in each of six terms

The extension below is an explicit function assembled from `G_T` and the
entire regularization of the actual Riemann zeta function. Equality with the
unregularized integrand is proved away from its poles. No contour movement or
bound at infinity is inferred from this local pole removal.
-/

namespace Sechstmoment

open Complex
open scoped BigOperators

noncomputable section

def polarOtherTermsKiller (T : ℝ) (σ : MomentShifts) (m : Fin 6) (z : ℂ) : ℂ :=
  ∏ n ∈ Finset.univ.erase m, purePolarTermKiller T σ n z

theorem polarPoleKiller_term_split (T : ℝ) (σ : MomentShifts) (m : Fin 6) (z : ℂ) :
    polarPoleKiller T σ z =
      Complex.exp (z^2) * purePolarTermKiller T σ m z * polarOtherTermsKiller T σ m z := by
  unfold polarPoleKiller polarOtherTermsKiller purePolarTermKiller
  rw [Fintype.prod_prod_type]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun n : Fin 6 => ∏ ij : Fin 2 × Fin 2,
      polarPoleKillingFactor (purePolarRoot T σ (n,ij)) z) (Finset.mem_univ m)]
  ring

theorem purePolarTermKiller_differentiable (T : ℝ) (σ : MomentShifts) (m : Fin 6) :
    Differentiable ℂ (purePolarTermKiller T σ m) := by
  unfold purePolarTermKiller
  apply Differentiable.fun_finsetProd
  intro ij _
  change Differentiable ℂ (fun z : ℂ => if purePolarRoot T σ (m,ij) = 0 then 1
    else 1-z^2/(purePolarRoot T σ (m,ij))^2)
  by_cases hρ : purePolarRoot T σ (m,ij) = 0
  · simp only [ite_eq_left hρ]
    fun_prop
  · simp only [ite_eq_right hρ]
    fun_prop

theorem polarOtherTermsKiller_differentiable (T : ℝ) (σ : MomentShifts) (m : Fin 6) :
    Differentiable ℂ (polarOtherTermsKiller T σ m) := by
  unfold polarOtherTermsKiller
  exact Differentiable.fun_finsetProd (fun _ _ => purePolarTermKiller_differentiable T σ _)

/-- The actual product of four pure zeta factors in a literal BBLR term. -/
def purePolarZetaProduct (T : ℝ) (σ : MomentShifts) (m : Fin 6) (z : ℂ) : ℂ :=
  ∏ ij : Fin 2 × Fin 2, riemannZeta (1+2*(z-purePolarRoot T σ (m,ij)))

/-- Its explicit entire extension after multiplication by `G_T`. -/
def purePolarRemovedIntegrand (T : ℝ) (σ : MomentShifts) (m : Fin 6) (z : ℂ) : ℂ :=
  Complex.exp (z^2) * polarOtherTermsKiller T σ m z *
    purePolarTermRemovedKiller T σ m z *
    ∏ ij : Fin 2 × Fin 2, polarRegularizedZeta (1+2*(z-purePolarRoot T σ (m,ij)))

theorem purePolarZetaArgument_eq_source (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (ij : Fin 2 × Fin 2) (z : ℂ) :
    1+2*(z-purePolarRoot T σ (m,ij)) = 1+2*z+
      Source.bblrSixShifts (rawMomentShifts T σ) m (purePolarLeft ij.1) +
      Source.bblrSixShifts (rawMomentShifts T σ) m (purePolarRight ij.2) := by
  unfold purePolarRoot
  ring

/-- Exact agreement off the actual polar roots, with all multiplicities kept. -/
theorem purePolarRemovedIntegrand_eq (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (hρ : ∀ ij : Fin 2 × Fin 2, purePolarRoot T σ (m,ij) ≠ 0)
    {z : ℂ} (hz : ∀ ij : Fin 2 × Fin 2, z ≠ purePolarRoot T σ (m,ij)) :
    purePolarRemovedIntegrand T σ m z = polarPoleKiller T σ z * purePolarZetaProduct T σ m z := by
  have hfactor (ij : Fin 2 × Fin 2) :
      polarRegularizedZeta (1+2*(z-purePolarRoot T σ (m,ij))) =
        (2*(z-purePolarRoot T σ (m,ij))) *
          riemannZeta (1+2*(z-purePolarRoot T σ (m,ij))) := by
    have harg : 1+2*(z-purePolarRoot T σ (m,ij)) ≠ 1 := by
      have hne : 2*(z-purePolarRoot T σ (m,ij)) ≠ 0 :=
        mul_ne_zero (by norm_num) (sub_ne_zero.mpr (hz ij))
      simpa using hne
    rw [polarRegularizedZeta_of_ne_one harg]
    ring
  unfold purePolarRemovedIntegrand
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, polarPoleKiller_term_split,
    purePolarTermKiller_factorization T σ m hρ z]
  unfold purePolarTermDivisor purePolarZetaProduct
  ring

/-- The extension is genuinely entire in `z`, even at coincident polar roots. -/
theorem purePolarRemovedIntegrand_differentiable (T : ℝ) (σ : MomentShifts) (m : Fin 6) :
    Differentiable ℂ (purePolarRemovedIntegrand T σ m) := by
  unfold purePolarRemovedIntegrand
  apply Differentiable.mul
  · exact ((by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (z^2))).mul
      (polarOtherTermsKiller_differentiable T σ m)).mul
        (purePolarTermRemovedKiller_differentiable T σ m)
  · apply Differentiable.fun_finsetProd
    intro ij _
    exact polarRegularizedZeta_differentiable.comp (by fun_prop)

end

end Sechstmoment
