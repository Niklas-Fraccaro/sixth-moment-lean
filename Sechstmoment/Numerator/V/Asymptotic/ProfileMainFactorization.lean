import Sechstmoment.Numerator.V.Asymptotic.ProfileOriginalCoefficients
import Sechstmoment.Numerator.V.Asymptotic.ProfileOriginalMain

/-! The finite arithmetic main term factors exactly into its time mass,
the literal original harmonic profile and the three actual zeta factors. -/

namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPHarmonic NoDPGlobalConvolution Complex Real Polynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem profileAdditiveOriginalMain_factorization {η L : ℝ} (hL : 0 < L)
    (w : ℝ → ℂ) (β : Fin 4 → ℂ) (P Q : ℝ[X]) (X : ℝ) :
    profileAdditiveOriginalMain
      (fun x => (zeroExtendedPolynomialProfile η P x:ℂ))
      (fun x => (zeroExtendedPolynomialProfile η Q x:ℂ)) L
      (⌊Real.exp (L*η)⌋₊^2) w β X =
      ∑ i : Fin 4, mellin w (1-β i)*(X:ℂ)^(1-β i)*
        originalProfileSum η L i β P Q*
        (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, riemannZeta (1+β j-β i)) := by
  classical
  let f : ℝ → ℂ := fun x => (zeroExtendedPolynomialProfile η P x:ℂ)
  let g : ℝ → ℂ := fun x => (zeroExtendedPolynomialProfile η Q x:ℂ)
  let Y := ⌊Real.exp (L*η)⌋₊^2
  have hprofile (i : Fin 4) :
      (∑ N : Finset.Icc 1 Y, profileCoefficient f g L N.val*originalCoeffAt i β N.val 1) =
        originalProfileSum η L i β P Q :=
    (Finset.sum_coe_sort _ (fun N => profileCoefficient f g L N*originalCoeffAt i β N 1)).trans
      (profileCoefficient_eq_originalProfileSum hL i β P Q)
  unfold profileAdditiveOriginalMain additiveOriginalMain
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (mellin w (1-β i)*(X:ℂ)^(1-β i))*
        (∑ N : Finset.Icc 1 Y, profileCoefficient f g L N.val*originalCoeffAt i β N.val 1)*
        (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, riemannZeta (1+β j-β i)) := by
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro N _
      ring
    _ = _ := by rw [hprofile]

end
end Sechstmoment.Source.NoDPGlobalLFactorization
