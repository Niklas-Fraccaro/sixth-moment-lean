import Sechstmoment.Numerator.V.Arithmetic.Additive.OriginalMain
import Sechstmoment.Numerator.V.Arithmetic.TimeWeightRemainder


namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section
set_option autoImplicit false

def profileAdditiveActual (f g : ℝ → ℂ) (L : ℝ) (Y : ℕ)
    (w : ℝ → ℂ) (β : Fin 4 → ℂ) (X : ℝ) : ℂ :=
  ∑ N : Finset.Icc 1 Y, profileCoefficient f g L N.val*(N.val:ℂ)⁻¹*
    (∑' m : ℕ, (fourAF β m*w ((m:ℝ)/((N.val:ℝ)*X)))*naturalAdditivePhase N.val m)

def profileAdditiveOriginalMain (f g : ℝ → ℂ) (L : ℝ) (Y : ℕ)
    (w : ℝ → ℂ) (β : Fin 4 → ℂ) (X : ℝ) : ℂ :=
  ∑ N : Finset.Icc 1 Y, profileCoefficient f g L N.val*additiveOriginalMain w β N.val X

theorem profile_original_main_eq_remainder {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (f g : ℝ → ℂ) (L : ℝ) (Y : ℕ) (β : Fin 4 → ℂ) (hsep : Function.Injective β)
    {κ X : ℝ} (hκ : 1/2 < κ) (hκu : κ ≤ 3/4)
    (hβ : ∀ j, ‖β j‖ ≤ min (1/8) (κ-1/2)) (hX : 0 < X) :
    profileAdditiveActual f g L Y w β X-profileAdditiveOriginalMain f g L Y w β X =
      (1/(2*Real.pi):ℂ)*profileRemainderSum f g L Y w κ β X := by
  classical
  calc
    _ = ∑ N : Finset.Icc 1 Y, profileCoefficient f g L N.val*
        ((N.val:ℂ)⁻¹*
          (∑' m : ℕ, (fourAF β m*w ((m:ℝ)/((N.val:ℝ)*X)))*naturalAdditivePhase N.val m)-
          additiveOriginalMain w β N.val X) := by
      simp only [profileAdditiveActual,profileAdditiveOriginalMain,mul_sub,
        Finset.sum_sub_distrib,mul_assoc]
    _ = ∑ N : Finset.Icc 1 Y, profileCoefficient f g L N.val*
        ((1/(2*Real.pi):ℂ)*displacedRemainder N.val (positiveIndexNeZero Y N)
          w κ β ((N.val:ℝ)*X)) := by
      apply Finset.sum_congr rfl
      intro N _
      rw [additive_original_main_eq_remainder hw hws N.val
        (positiveIndexNeZero Y N) β hsep hκ hκu hβ hX]
    _ = _ := by
      rw [profileRemainderSum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _
      ring

theorem timeWeight_profile_original_main_power_saving {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) (ε η : ℝ)
    (hε : 0 < ε) (hεu : ε < 1/2) (hη : η ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ X : ℝ, 0 < X → X ≤ T → ∀ z : ℂ, ‖z‖ ≤ R →
      ∀ Y : ℕ, Y ≠ 0 → (Y:ℝ) ≤ T^(2*η) →
      ∀ f g : ℝ → ℂ, ∀ B : ℝ, 0 ≤ B → (∀ x, ‖f x‖ ≤ B) → (∀ x, ‖g x‖ ≤ B) →
      ∀ β : Fin 4 → ℂ, Function.Injective β → (∀ j, ‖β j‖ ≤ R/Real.log T) →
      ‖profileAdditiveActual f g (Real.log T) Y
          (noDPTimeWeight w T (z/(Real.log T:ℂ))) β X-
        profileAdditiveOriginalMain f g (Real.log T) Y
          (noDPTimeWeight w T (z/(Real.log T:ℂ))) β X‖ ≤
        C*B^2*T^(1/2+2*η+ε) := by
  obtain ⟨A,hA,U,hU,HA⟩ := timeWeight_profile_displaced_power_saving_scaled
    hw hws hR ε η hε hεu hη
  obtain ⟨V,hV,HV⟩ := log_shift_tolerance (ε/32) R (by linarith)
  let K : ℂ := (1/(2*Real.pi):ℂ)
  refine ⟨(‖K‖+1)*A,by positivity,max U V,hU.trans_le (le_max_left _ _),?_⟩
  intro T hT X hX hXT z hz Y hY hYlen f g B hB hf hg β hsep hβ
  have hTp : 0 < T := hX.trans_le hXT
  have hTU : U ≤ T := (le_max_left _ _).trans hT
  have hTV : V ≤ T := (le_max_right _ _).trans hT
  have hsmall (j : Fin 4) : ‖β j‖ ≤ min (1/8) ((1/2+ε/16)-1/2) := by
    have H := (hβ j).trans (HV T hTV)
    apply le_min <;> linarith
  rw [profile_original_main_eq_remainder (noDPTimeWeight_contDiff hw hws T _)
    ((noDPTimeWeight_tsupport w T _).trans hws) f g (Real.log T) Y β hsep
    (κ := 1/2+ε/16) (by linarith) (by linarith) hsmall hX,norm_mul]
  have H := HA T hTU X hX hXT z hz Y hY hYlen f g B hB hf hg β hβ
  calc
    _ ≤ ‖K‖*(A*B^2*T^(1/2+2*η+ε)) :=
      mul_le_mul_of_nonneg_left H (norm_nonneg K)
    _ ≤ (‖K‖+1)*(A*B^2*T^(1/2+2*η+ε)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end
end Sechstmoment.Source.NoDPGlobalLFactorization
