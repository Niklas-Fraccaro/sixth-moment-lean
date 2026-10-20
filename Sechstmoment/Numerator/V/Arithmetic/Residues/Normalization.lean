import Sechstmoment.Numerator.V.Arithmetic.Principal.EulerNormalization
import Sechstmoment.Numerator.V.Arithmetic.Principal.Gauss
import Sechstmoment.Numerator.V.Arithmetic.Principal.MellinResidue


namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory ZMod
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem principalMellin_residue_normalized (q : ℕ) [NeZero q] (d : ℕ)
    (w : ℝ → ℂ) (β : Fin 4 → ℂ) (hβ : Function.Injective β) (x : ℝ) (i : Fin 4) :
    (q.totient:ℂ)⁻¹*(ArithmeticFunction.moebius q:ℂ)*
      ((((Finset.univ : Finset (Fin 4)).erase i).prod
        (fun j : Fin 4 => (1-β i)-(1-β j)))⁻¹*
          principalMellinNumerator q d w β x (1-β i)) =
      ((ArithmeticFunction.moebius q:ℂ)/(q:ℂ))*
        mellin w (1-β i)*(x:ℂ)^(1-β i)*
        eulerCorrection (1 : DirichletCharacter ℂ q) d β (1-β i)*
        (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
          (1 : DirichletCharacter ℂ q).LFunction ((1-β i)+β j)) := by
  have hM : (q.totient:ℂ)⁻¹*(∏ p ∈ q.primeFactors, (1-(p:ℂ)⁻¹)) = (q:ℂ)⁻¹ := by
    simpa only [DirichletCharacter.LFunctionTrivChar₁,Function.update_self] using
      principal_regularizedL_one_totient_normalization q
  rw [principalMellinNumerator_residue q d w β hβ x i]
  calc
    _ = (ArithmeticFunction.moebius q:ℂ)*
        ((q.totient:ℂ)⁻¹*(∏ p ∈ q.primeFactors, (1-(p:ℂ)⁻¹)))*
        (mellin w (1-β i)*(x:ℂ)^(1-β i)*
          eulerCorrection (1 : DirichletCharacter ℂ q) d β (1-β i)*
          (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
            (1 : DirichletCharacter ℂ q).LFunction ((1-β i)+β j))) := by ring
    _ = _ := by rw [hM]; ring

theorem principalMellin_residue_normalized_zeta (q : ℕ) [NeZero q] (d : ℕ)
    (w : ℝ → ℂ) (β : Fin 4 → ℂ) (hβ : Function.Injective β) (x : ℝ) (i : Fin 4) :
    (q.totient:ℂ)⁻¹*gaussSum (1 : DirichletCharacter ℂ q) stdAddChar*
      ((((Finset.univ : Finset (Fin 4)).erase i).prod
        (fun j : Fin 4 => (1-β i)-(1-β j)))⁻¹*
          principalMellinNumerator q d w β x (1-β i)) =
      ((ArithmeticFunction.moebius q:ℂ)/(q:ℂ))*
        mellin w (1-β i)*(x:ℂ)^(1-β i)*
        eulerCorrection (1 : DirichletCharacter ℂ q) d β (1-β i)*
        (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
          ∏ p ∈ q.primeFactors, (1-(p:ℂ)^(-(1+β j-β i))))*
        (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, riemannZeta (1+β j-β i)) := by
  rw [principal_gaussSum_eq_moebius,principalMellin_residue_normalized q d w β hβ x i,
    principal_residue_L_product_eq_zeta q β hβ i]
  ring

end
end Sechstmoment.Source.NoDPGlobalLFactorization
