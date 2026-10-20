import SixthMoment.Numerator.V.Arithmetic.Residues.Global


namespace SixthMoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory NoDPGlobalConvolution
open scoped BigOperators ContDiff
noncomputable section
set_option autoImplicit false

def additiveOriginalMain (w : ℝ → ℂ) (β : Fin 4 → ℂ) (N : ℕ) (X : ℝ) : ℂ :=
  ∑ i : Fin 4, mellin w (1-β i)*(X:ℂ)^(1-β i)*originalCoeffAt i β N 1*
    (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, riemannZeta (1+β j-β i))

theorem additive_original_main_eq_remainder {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (N : ℕ) (hN : N ≠ 0) (β : Fin 4 → ℂ) (hsep : Function.Injective β)
    {κ X : ℝ} (hκ : 1/2 < κ) (hκu : κ ≤ 3/4)
    (hsmall : ∀ j, ‖β j‖ ≤ min (1/8) (κ-1/2)) (hX : 0 < X) :
    (N:ℂ)⁻¹*
        (∑' m : ℕ, (fourAF β m*w ((m:ℝ)/((N:ℝ)*X)))*naturalAdditivePhase N m)-
      additiveOriginalMain w β N X =
        (1/(2*Real.pi):ℂ)*displacedRemainder N hN w κ β ((N:ℝ)*X) := by
  have hsmall' (j : Fin 4) : ‖β j‖ ≤ 1/8 := (hsmall j).trans (min_le_left _ _)
  have hre (j : Fin 4) : |(β j).re| ≤ 1/8 := (Complex.abs_re_le_norm _).trans (hsmall' j)
  have he := additive_fourAF_original_residue_identity hw hws N hN β hsep hX
    (a := κ) (b := 5/4) (ρ := 1/8) hκ (by norm_num)
    (by norm_num) (by norm_num) hsmall' hsmall
    (fun j => by simp only [sub_re,one_re]; linarith [(abs_le.mp (hre j)).2])
    (fun j => by linarith [(abs_le.mp (hre j)).1])
  have hNC : (N:ℂ) ≠ 0 := by exact_mod_cast hN
  rw [he]
  change (N:ℂ)⁻¹*((1/(2*Real.pi):ℂ)*(∑ d : N.divisors,
    divisorMellinIntegral N hN d w κ β ((N:ℝ)*X))+
    (N:ℂ)*additiveOriginalMain w β N X)-additiveOriginalMain w β N X = _
  have hcancel : (N:ℂ)⁻¹*((N:ℂ)*additiveOriginalMain w β N X) =
      additiveOriginalMain w β N X := by
    rw [← mul_assoc,inv_mul_cancel₀ hNC,one_mul]
  rw [mul_add,hcancel,add_sub_cancel_right]
  dsimp only [displacedRemainder]
  ring

theorem additive_original_main_uniform {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ _hN : N ≠ 0,
      ∀ β : Fin 4 → ℂ, Function.Injective β →
      (∀ j, ‖β j‖ ≤ min (1/16) (ε/2)) → ∀ X : ℝ, 0 < X →
        ‖(N:ℂ)⁻¹*
            (∑' m : ℕ, (fourAF β m*w ((m:ℝ)/((N:ℝ)*X)))*naturalAdditivePhase N m)-
          additiveOriginalMain w β N X‖ ≤ C*X^(5/8:ℝ)*(N:ℝ)^(1/8+ε) := by
  obtain ⟨A,hA,HA⟩ := displacedRemainder_scaled_bound hw hws (5/8) ε (by norm_num) hε
  let K : ℂ := (1/(2*Real.pi):ℂ)
  refine ⟨(‖K‖+1)*A,by positivity,?_⟩
  intro N hN β hsep hβ X hX
  have hsmall (j : Fin 4) : ‖β j‖ ≤ 1/16 := (hβ j).trans (min_le_left _ _)
  have hre (j : Fin 4) : |(β j).re| ≤ 1/16 := (Complex.abs_re_le_norm _).trans (hsmall j)
  have hcorr (j : Fin 4) : ‖β j‖ ≤ min (5/8) (ε/2) :=
    le_min ((hsmall j).trans (by norm_num)) ((hβ j).trans (min_le_right _ _))
  have hstrip (j : Fin 4) : (5/8:ℝ)+(β j).re ∈ Icc (1/2:ℝ) (3/4) := by
    constructor <;> linarith [(abs_le.mp (hre j)).1,(abs_le.mp (hre j)).2]
  have herr := HA N hN β hcorr hstrip X hX
  rw [additive_original_main_eq_remainder hw hws N hN β hsep
    (κ := 5/8) (by norm_num) (by norm_num)
    (fun j => (hsmall j).trans (by norm_num)) hX,norm_mul]
  calc
    _ ≤ ‖K‖*(A*X^(5/8:ℝ)*(N:ℝ)^(1/8+ε)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg K)
      simpa only [show (5/8-1/2+ε:ℝ) = 1/8+ε by ring] using herr
    _ ≤ (‖K‖+1)*(A*X^(5/8:ℝ)*(N:ℝ)^(1/8+ε)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end
end SixthMoment.Source.NoDPGlobalLFactorization
