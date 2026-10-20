import SixthMoment.Numerator.V.Contour.AlmostHolomorphicContour


namespace SixthMoment.Source
open Complex Real Set MeasureTheory
open scoped ContDiff
noncomputable section

theorem almostHolomorphicWeight_integrated_replacement {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ u : ℝ, |u-1/2| ≤ 1 →
      ∀ F : ℝ → ℂ, ContinuousOn F (Icc (T/2) (3*T)) →
      ∀ M : ℝ, 0 ≤ M → (∀ t ∈ Icc T (2*T), ‖F t‖ ≤ M) →
      ‖(∫ t : ℝ, F t*almostHolomorphicWeight w K T u t)-
        (∫ t : ℝ, F t*w (t/T))‖ ≤ C*M := by
  obtain ⟨D,hD,hweight⟩ := almostHolomorphicWeight_sub_original_bound hw hws K
  refine ⟨3*D,by positivity,?_⟩
  intro T hT u hu F hF M hM hbound
  have hT0 : 0 < T := by linarith
  have horder : T/2 ≤ 3*T := by linarith
  have hW : Continuous (fun t => almostHolomorphicWeight w K T u t) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (almostHolomorphicWeight_hasDerivAt_imag hw K T u t).continuousAt)
  have hwT : Continuous (fun t => w (t/T)) := hw.continuous.comp (by fun_prop)
  have hiW : IntervalIntegrable (fun t => F t * almostHolomorphicWeight w K T u t)
      volume (T/2) (3*T) :=
    (hF.mul hW.continuousOn).intervalIntegrable_of_Icc horder
  have hiw : IntervalIntegrable (fun t => F t * w (t/T)) volume (T/2) (3*T) :=
    (hF.mul hwT.continuousOn).intervalIntegrable_of_Icc horder
  have hleft := almostHolomorphicWeight_integral_eq_interval hws K hT0 (1/2) F
  simp only [almostHolomorphicWeight_left_boundary] at hleft
  rw [almostHolomorphicWeight_integral_eq_interval hws K hT0 u F,hleft,
    ← intervalIntegral.integral_sub hiW hiw]
  have hpoint (t : ℝ) :
      ‖F t*almostHolomorphicWeight w K T u t-F t*w (t/T)‖ ≤ M*(D/T) := by
    rw [← mul_sub,norm_mul]
    by_cases ht : t ∈ Icc T (2*T)
    · exact mul_le_mul (hbound t ht) (hweight T hT u t hu) (norm_nonneg _) hM
    · have hWzero := almostHolomorphicWeight_eq_zero_outside_dyadic hws K hT0 u t ht
      have hwzero : w (t/T) = 0 := by
        apply Function.notMem_support.mp
        intro hm
        have H := hws (subset_tsupport w hm)
        apply ht
        constructor
        · have Hlow := (le_div_iff₀ hT0).mp H.1
          linarith
        · exact (div_le_iff₀ hT0).mp H.2
      rw [hWzero,hwzero,sub_self,norm_zero,mul_zero]
      positivity
  have H := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := T/2) (b := 3*T) (fun t _ => hpoint t)
  rw [abs_of_nonneg (sub_nonneg.mpr horder)] at H
  apply H.trans
  have he : (M*(D/T))*(3*T-T/2) = (5/2:ℝ)*M*D := by
    field_simp [hT0.ne']
    ring
  rw [he]
  nlinarith

end
end SixthMoment.Source
