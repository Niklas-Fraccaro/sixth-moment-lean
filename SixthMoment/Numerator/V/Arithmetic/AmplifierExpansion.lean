import SixthMoment.Numerator.V.Arithmetic.AmplifiedAdditiveReduction
import SixthMoment.Numerator.V.Contour.ShiftedChiFactor


namespace SixthMoment.Source
open Complex Real Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section

theorem profileDirichletSum_one_sub_pair {T : ℝ} (hT : 1 < T) (η : ℝ)
    (f g : ℝ → ℝ) (hf : ∀ x, η < x → f x = 0) (hg : ∀ x, η < x → g x = 0)
    (s : ℂ) :
    profileDirichletSum T f (1-s)*profileDirichletSum T g (1-s) =
      ∑ a ∈ Finset.range ⌊T^η⌋₊, ∑ b ∈ Finset.range ⌊T^η⌋₊,
        noDPAmplifierPairWeight T f g a b*(((a+1:ℝ)*(b+1:ℝ):ℝ):ℂ)^s := by
  rw [profileDirichletSum_eq_finite hT η f hf,profileDirichletSum_eq_finite hT η g hg]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have ha : (a+1:ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero a
  have hb : (b+1:ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero b
  have hpa : (a+1:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl ha)
  have hpb : (b+1:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hb)
  rw [Complex.cpow_sub _ _ ha,Complex.cpow_sub _ _ hb,Complex.cpow_one,Complex.cpow_one]
  unfold noDPAmplifierPairWeight
  simp only [Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (by positivity : (0:ℝ) ≤ a+1)
    (by positivity : (0:ℝ) ≤ b+1)]
  push_cast
  field_simp [ha,hb,hpa,hpb]

theorem shiftedChi_profile_integral_eq_amplified {w : ℝ → ℂ}
    (hw : Continuous w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {T : ℝ} (hT : 80 ≤ T) (η : ℝ) (f g : ℝ → ℝ)
    (hf : ∀ x, η < x → f x = 0) (hg : ∀ x, η < x → g x = 0)
    (c : ℝ) (u : ℂ) (hu : ‖u‖ ≤ 1/8) (β : Fin 4 → ℂ)
    (hβ : ∀ j, ‖β j‖ ≤ 1/8) :
    (1/(2*Real.pi):ℂ)*(∫ t : ℝ,
      shiftedChiProfileFactor T u β f g ((c:ℂ)+(t:ℂ)*I)*w (t/T)) =
      ∑ a ∈ Finset.range ⌊T^η⌋₊, ∑ b ∈ Finset.range ⌊T^η⌋₊,
        noDPAmplifierPairWeight T f g a b*
          noDPFourChiMoment w T c ((a+1:ℝ)*(b+1:ℝ)) u β := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 < T := by linarith
  let F : ℝ → ℝ → ℂ := fun N t =>
    shiftedChiZetaFactor u β ((c:ℂ)+(t:ℂ)*I)*(N:ℂ)^((c:ℂ)+(t:ℂ)*I)*w (t/T)
  have hInt (N : ℝ) (hN : 0 < N) : Integrable (F N) := by
    have hp : Continuous (fun t : ℝ => (c:ℂ)+(t:ℂ)*I) := by fun_prop
    have hpow : Continuous (fun t : ℝ => (N:ℂ)^((c:ℂ)+(t:ℂ)*I)) :=
      hp.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))
    have hwT : Continuous (fun t : ℝ => w (t/T)) := hw.comp (by fun_prop)
    have hcont : ContinuousOn (F N) (Icc T (2*T)) := by
      intro t ht
      have hh : 40 ≤ |((c:ℂ)+(t:ℂ)*I).im| := by
        simp only [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add]
        rw [abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.1]
      have hz : ContinuousAt (shiftedChiZetaFactor u β) ((c:ℂ)+(t:ℂ)*I) :=
        (shiftedChiZetaFactor_differentiableAt (s := (c:ℂ)+(t:ℂ)*I) (u := u)
          β hh hu hβ).continuousAt
      have hcomp : ContinuousAt
          (fun r : ℝ => shiftedChiZetaFactor u β ((c:ℂ)+(r:ℂ)*I)) t :=
        ContinuousAt.comp (f := fun r : ℝ => (c:ℂ)+(r:ℂ)*I) (x := t)
          hz hp.continuousAt
      exact ((hcomp.mul hpow.continuousAt).mul hwT.continuousAt).continuousWithinAt
    have hzero (t : ℝ) (ht : t ∉ Icc T (2*T)) : F N t = 0 := by
      have hz : w (t/T) = 0 := by
        apply Function.notMem_support.mp
        intro hm
        have H := hws (subset_tsupport _ hm)
        apply ht
        exact ⟨by simpa using (le_div_iff₀ hT0).mp H.1,(div_le_iff₀ hT0).mp H.2⟩
      simp only [F,hz,mul_zero]
    have he : F N = (Icc T (2*T)).indicator (F N) := by
      funext t
      by_cases ht : t ∈ Icc T (2*T)
      · rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht,hzero t ht]
    rw [he]
    exact (integrable_indicator_iff measurableSet_Icc).mpr hcont.integrableOn_Icc
  have hpoint (t : ℝ) :
      shiftedChiProfileFactor T u β f g ((c:ℂ)+(t:ℂ)*I)*w (t/T) =
        ∑ a ∈ Finset.range ⌊T^η⌋₊, ∑ b ∈ Finset.range ⌊T^η⌋₊,
          noDPAmplifierPairWeight T f g a b*F ((a+1:ℝ)*(b+1:ℝ)) t := by
    rw [shiftedChiProfileFactor,mul_assoc (shiftedChiZetaFactor _ _ _),
      profileDirichletSum_one_sub_pair hT1 η f g hf hg]
    simp_rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [F]
    ring
  have hterm (a b : ℕ) : Integrable (fun t : ℝ =>
      noDPAmplifierPairWeight T f g a b*F ((a+1:ℝ)*(b+1:ℝ)) t) :=
    (hInt _ (by positivity)).const_mul _
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hterm a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hterm _ b),integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [noDPFourChiMoment]
  have he : F ((a+1:ℝ)*(b+1:ℝ)) = fun t : ℝ =>
      (zetaChi (1-((c:ℂ)+(t:ℂ)*I)+u)*w (t/T))*
        ((((a+1:ℝ)*(b+1:ℝ):ℝ):ℂ)^((c:ℂ)+(t:ℂ)*I)*
          ∏ j : Fin 4, riemannZeta ((c:ℂ)+(t:ℂ)*I+β j)) := by
    funext t
    dsimp only [F,shiftedChiZetaFactor]
    ring
  rw [he]
  ring

theorem shiftedChi_profile_additive_reduction {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) (η : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 80 (100*Real.pi) ≤ T →
      4*(2*R+2) ≤ Real.log T → ∀ u : ℂ, ‖u‖ ≤ R/Real.log T →
      ∀ β : Fin 4 → ℂ, (∀ j, ‖β j‖ ≤ R/Real.log T) →
      ∀ B D : ℝ, 0 ≤ B → 0 ≤ D → ∀ f g : ℝ → ℝ,
      (∀ x, η < x → f x = 0) → (∀ x, η < x → g x = 0) →
      (∀ x ∈ Icc (0:ℝ) η, |f x| ≤ B) →
      (∀ x ∈ Icc (0:ℝ) η, |g x| ≤ D) →
      ‖(1/(2*Real.pi):ℂ)*(∫ t : ℝ,
          shiftedChiProfileFactor T u β f g ((noDPRightLine T R:ℂ)+(t:ℂ)*I)*w (t/T))-
        (∑ a ∈ Finset.range ⌊T^η⌋₊, ∑ b ∈ Finset.range ⌊T^η⌋₊,
          noDPAmplifierPairWeight T f g a b*
            ∑' m : ℕ+, noDPAdditiveChiTerm w T ((a+1:ℝ)*(b+1:ℝ)) u β m)‖ ≤
        C*B*D*T^(1/2+2*η:ℝ)*(Real.log T)^4 := by
  obtain ⟨C,hC,H⟩ := amplified_four_zeta_chi_additive_reduction hw hws hR η
  refine ⟨C,hC,?_⟩
  intro T hT hL u hu β hβ B D hB hD f g hf hg hfB hgD
  have hT80 : 80 ≤ T := (le_max_left _ _).trans hT
  have hT64 : max 64 (100*Real.pi) ≤ T :=
    max_le (by linarith) ((le_max_right _ _).trans hT)
  rw [shiftedChi_profile_integral_eq_amplified hw.continuous hws hT80 η f g hf hg
    (noDPRightLine T R) u (noDPRightLine_chi_shift_geometry hR hL hu).2.1 β
    (fun j => (noDPRightLine_chi_shift_geometry hR hL (hβ j)).2.1)]
  exact H T hT64 hL u hu β hβ B D hB hD f g hfB hgD

end
end SixthMoment.Source
