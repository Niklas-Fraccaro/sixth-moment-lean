import Sechstmoment.Numerator.V.Arithmetic.Residues.Arithmetic
import Sechstmoment.Numerator.V.Arithmetic.Residues.Normalization


namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Complex Real ZMod NoDPGlobalRest
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem principalMellin_residue_scaled (q : ℕ) [NeZero q] (d : ℕ)
    (w : ℝ → ℂ) (β : Fin 4 → ℂ) (hβ : Function.Injective β)
    {X : ℝ} (hX : 0 < X) (i : Fin 4) :
    (q.totient:ℂ)⁻¹*(ArithmeticFunction.moebius q:ℂ)*
      ((((Finset.univ : Finset (Fin 4)).erase i).prod
        (fun j : Fin 4 => (1-β i)-(1-β j)))⁻¹*
          principalMellinNumerator q d w β ((q:ℝ)*X) (1-β i)) =
      mellin w (1-β i)*(X:ℂ)^(1-β i)*
        principalResidueArithmeticTerm (reindexShifts i β) q d*
        (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, riemannZeta (1+β j-β i)) := by
  have H := principalMellin_residue_normalized_zeta q d w β hβ ((q:ℝ)*X) i
  rw [principal_gaussSum_eq_moebius] at H
  rw [H,principalResidueArithmeticTerm_reindex]
  have hq : (q:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hmul : ((q:ℂ)*(X:ℂ))^(1-β i) = (q:ℂ)^(1-β i)*(X:ℂ)^(1-β i) := by
    simpa only [Complex.ofReal_natCast] using
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg q) hX.le (1-β i)
  have hpow : (q:ℂ)^(1-β i) = (q:ℂ)*(q:ℂ)^(-β i) := by
    rw [sub_eq_add_neg,Complex.cpow_add _ _ hq,Complex.cpow_one]
  rw [Complex.ofReal_mul,Complex.ofReal_natCast,hmul,hpow]
  calc
    _ = ((q:ℂ)*(q:ℂ)⁻¹)*
        (mellin w (1-β i)*(X:ℂ)^(1-β i)*
          ((ArithmeticFunction.moebius q:ℂ)*(q:ℂ)^(-β i)*
            (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
              ∏ p ∈ q.primeFactors, (1-(p:ℂ)^(-(1+β j-β i))))*
            eulerCorrection (1 : DirichletCharacter ℂ q) d β (1-β i))*
          (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
            riemannZeta (1+β j-β i))) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hq,one_mul]

end
end Sechstmoment.Source.NoDPGlobalLFactorization
