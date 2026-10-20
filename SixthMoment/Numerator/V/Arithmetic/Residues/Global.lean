import SixthMoment.Numerator.V.Arithmetic.Additive.ResidueIdentity
import SixthMoment.Numerator.V.Arithmetic.Residues.Scale


namespace SixthMoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory NoDPGlobalRest NoDPGlobalConvolution
open scoped BigOperators ContDiff
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem divisorPrincipalResidues_sum_exact (N : ℕ) (hN : N ≠ 0)
    (w : ℝ → ℂ) (β : Fin 4 → ℂ) (hsep : Function.Injective β)
    {X ρ : ℝ} (hX : 0 < X) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4)
    (hβ : ∀ j, ‖β j‖ ≤ ρ) :
    (∑ d : N.divisors, divisorPrincipalResidues N hN d w β ((N:ℝ)*X)) =
      (N:ℂ)*∑ i : Fin 4, mellin w (1-β i)*(X:ℂ)^(1-β i)*
        originalCoeffAt i β N 1*
        (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, riemannZeta (1+β j-β i)) := by
  classical
  let W (i : Fin 4) := mellin w (1-β i)*(X:ℂ)^(1-β i)
  let Z (i : Fin 4) :=
    ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, riemannZeta (1+β j-β i)
  have hpoint (d : N.divisors) :
      divisorPrincipalResidues N hN d w β ((N:ℝ)*X) =
        ∑ i : Fin 4, W i*
          principalResidueArithmeticTerm (reindexShifts i β) (N/d.val) d.val*Z i := by
    let : NeZero (N/d.val) := divisorQuotientNeZero N hN d
    have hd : (d.val:ℝ) ≠ 0 := by exact_mod_cast divisor_ne_zero d.property
    have hx : ((N:ℝ)*X)/(d.val:ℝ) = (N/d.val:ℕ)*X := by
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors d.property) hd]
      ring
    dsimp only [divisorPrincipalResidues,principalMellinResidueSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx]
    exact principalMellin_residue_scaled (N/d.val) d.val w β hsep hX i
  have harith (i : Fin 4) :
      (∑ d : N.divisors,
        principalResidueArithmeticTerm (reindexShifts i β) (N/d.val) d.val) =
          (N:ℂ)*originalCoeffAt i β N 1 := by
    calc
      _ = ∑ d ∈ N.divisors,
          principalResidueArithmeticTerm (reindexShifts i β) (N/d) d :=
        Finset.sum_coe_sort N.divisors
          (fun d => principalResidueArithmeticTerm (reindexShifts i β) (N/d) d)
      _ = ∑ q ∈ N.divisors,
          principalResidueArithmeticTerm (reindexShifts i β) q (N/q) :=
        (Nat.sum_divisorsAntidiagonal'
          (principalResidueArithmeticTerm (reindexShifts i β))).symm.trans
            (Nat.sum_divisorsAntidiagonal
              (principalResidueArithmeticTerm (reindexShifts i β)))
      _ = _ := principalResidueArithmetic_divisor_sum_at i β ρ hρ0 hρ hβ N
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i : Fin 4, W i*
        (∑ d : N.divisors,
          principalResidueArithmeticTerm (reindexShifts i β) (N/d.val) d.val)*Z i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum,Finset.sum_mul]
    _ = ∑ i : Fin 4, W i*((N:ℂ)*originalCoeffAt i β N 1)*Z i := by
      simp_rw [harith]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [W,Z]
      ring

theorem additive_fourAF_original_residue_identity {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (N : ℕ) (hN : N ≠ 0) (β : Fin 4 → ℂ) (hsep : Function.Injective β)
    {X a b ρ : ℝ} (hX : 0 < X) (ha : 1/2 < a) (hb : b ≤ 5/4)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hβρ : ∀ j, ‖β j‖ ≤ ρ)
    (hβ : ∀ j, ‖β j‖ ≤ min (1/8) (a-1/2))
    (hpa : ∀ j, a < (1-β j).re) (hc : ∀ j, 1 < b+(β j).re) :
    (∑' m : ℕ, (fourAF β m*w ((m:ℝ)/((N:ℝ)*X)))*naturalAdditivePhase N m) =
      (1/(2*Real.pi):ℂ)*
        (∑ d : N.divisors, divisorMellinIntegral N hN d w a β ((N:ℝ)*X))+
      (N:ℂ)*∑ i : Fin 4, mellin w (1-β i)*(X:ℂ)^(1-β i)*
        originalCoeffAt i β N 1*
        (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, riemannZeta (1+β j-β i)) := by
  have hNX : 0 < (N:ℝ)*X := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hN) hX
  rw [additive_fourAF_residue_identity hw hws N hN β hsep hNX ha hb hβ hpa hc,
    divisorPrincipalResidues_sum_exact N hN w β hsep hX hρ0 hρ hβρ]

end
end SixthMoment.Source.NoDPGlobalLFactorization
