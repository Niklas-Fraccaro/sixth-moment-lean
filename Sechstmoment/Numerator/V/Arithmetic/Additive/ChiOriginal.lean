import Sechstmoment.Numerator.V.Arithmetic.Additive.DirichletReduction
import Sechstmoment.Numerator.V.Asymptotic.ProfileOriginalMain

/-! The additive series in the actual chi reduction has exactly the
natural additive phase and the Mellin scale T/(2*pi). -/

namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section
set_option autoImplicit false

theorem additiveChi_series_eq_natural (w : ℝ → ℂ) {T : ℝ} (hT : T ≠ 0)
    (N : ℕ) [NeZero N] (u : ℂ) (β : Fin 4 → ℂ) :
    (∑' m : ℕ+, noDPAdditiveChiTerm w T (N:ℝ) u β m) =
      ∑' m : ℕ, (fourAF β m*
        noDPTimeWeight w T u ((m:ℝ)/((N:ℝ)*(T/(2*Real.pi)))))*naturalAdditivePhase N m := by
  let F (m : ℕ) := (fourAF β m*
    noDPTimeWeight w T u ((m:ℝ)/((N:ℝ)*(T/(2*Real.pi)))))*naturalAdditivePhase N m
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hpi : (2*Real.pi:ℝ) ≠ 0 := by positivity
  have harg (m : ℕ) : 2*Real.pi*((m:ℝ)/(N:ℝ))/T =
      (m:ℝ)/((N:ℝ)*(T/(2*Real.pi))) := by
    field_simp [hT,hNR,hpi]
  have hphase (m : ℕ) :
      Complex.exp (I*((-2*Real.pi*((m:ℝ)/(N:ℝ)):ℝ):ℂ)) = naturalAdditivePhase N m := by
    unfold naturalAdditivePhase
    congr 1
    push_cast
    ring
  calc
    _ = ∑' m : ℕ+, F m := by
      apply tsum_congr
      intro m
      dsimp only [noDPAdditiveChiTerm,F]
      rw [harg,hphase]
      ring
    _ = _ := tsum_pnat_eq_tsum_of_eq_zero (f := F) (by simp [F])

def profileChiAdditiveActual (w : ℝ → ℂ) (T : ℝ) (u : ℂ) (f g : ℝ → ℂ)
    (L : ℝ) (Y : ℕ) (β : Fin 4 → ℂ) : ℂ :=
  ∑ N : Finset.Icc 1 Y, profileCoefficient f g L N.val*(N.val:ℂ)⁻¹*
    (∑' m : ℕ+, noDPAdditiveChiTerm w T (N.val:ℝ) u β m)

theorem profileChiAdditiveActual_eq (w : ℝ → ℂ) {T : ℝ} (hT : T ≠ 0)
    (u : ℂ) (f g : ℝ → ℂ) (L : ℝ) (Y : ℕ) (β : Fin 4 → ℂ) :
    profileChiAdditiveActual w T u f g L Y β =
      profileAdditiveActual f g L Y (noDPTimeWeight w T u) β (T/(2*Real.pi)) := by
  classical
  unfold profileChiAdditiveActual profileAdditiveActual
  apply Finset.sum_congr rfl
  intro N _
  let : NeZero N.val := ⟨positiveIndexNeZero Y N⟩
  rw [additiveChi_series_eq_natural w hT N.val u β]

theorem profileChi_original_main_power_saving {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) (ε η : ℝ)
    (hε : 0 < ε) (hεu : ε < 1/2) (hη : η ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ Y : ℕ, Y ≠ 0 → (Y:ℝ) ≤ T^(2*η) →
      ∀ f g : ℝ → ℂ, ∀ B : ℝ, 0 ≤ B → (∀ x, ‖f x‖ ≤ B) → (∀ x, ‖g x‖ ≤ B) →
      ∀ β : Fin 4 → ℂ, Function.Injective β → (∀ j, ‖β j‖ ≤ R/Real.log T) →
      ‖profileChiAdditiveActual w T (z/(Real.log T:ℂ)) f g (Real.log T) Y β-
        profileAdditiveOriginalMain f g (Real.log T) Y
          (noDPTimeWeight w T (z/(Real.log T:ℂ))) β (T/(2*Real.pi))‖ ≤
        C*B^2*T^(1/2+2*η+ε) := by
  obtain ⟨C,hC,T₀,hT₀,H⟩ := timeWeight_profile_original_main_power_saving
    hw hws hR ε η hε hεu hη
  refine ⟨C,hC,T₀,hT₀,?_⟩
  intro T hT z hz Y hY hYlen f g B hB hf hg β hsep hβ
  have hTp : 0 < T := zero_lt_one.trans (hT₀.trans_le hT)
  have hp : 0 < 2*Real.pi := by positivity
  have hXT : T/(2*Real.pi) ≤ T :=
    (div_le_iff₀ hp).mpr (le_mul_of_one_le_right hTp.le (by linarith [Real.two_le_pi]))
  rw [profileChiAdditiveActual_eq w hTp.ne']
  exact H T hT (T/(2*Real.pi)) (div_pos hTp hp) hXT z hz Y hY hYlen
    f g B hB hf hg β hsep hβ

end
end Sechstmoment.Source.NoDPGlobalLFactorization
