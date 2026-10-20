import SixthMoment.Numerator.U.Replacement.VStar.FiniteGrid
import SixthMoment.Numerator.U.Separation.DualLeadingRegularity

namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

def rectangularFiniteSmallVStarCombinedRemainder (c T : ℝ) (σ : MomentShifts)
    (X R t : ℝ) : ℂ :=
  rectangularFiniteSmallVStarRemainder c T σ (rawMomentShifts T σ) t X R+
    bblrDualLeadingMultiplier T σ (t/T)*
      rectangularFiniteSmallVStarRemainder c T σ
        (bblrSixShifts (rawMomentShifts T σ) 1) t X R

private theorem dual_raw_norm {T : ℝ} {σ : MomentShifts}
    (hα : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) :
    ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) 1 j‖≤1/4 := by
  intro j
  fin_cases j <;> simp [bblrSixShifts] <;>
    first | simpa using hα 0 | simpa using hα 1 | simpa using hα 2 | simpa using hα 3

theorem rectangularVStarCombinedAFE_time_stronglyMeasurable (T : ℝ) (σ : MomentShifts) :
    StronglyMeasurable (fun t : ℝ =>
      bblrVStarAFESum (polarPoleKiller T σ) (rawMomentShifts T σ) t+
        bblrDualLeadingMultiplier T σ (t/T)*
          bblrVStarAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) 1) t) := by
  have hG := (polarPoleKiller_differentiable T σ).continuous
  exact (bblrVStarAFESum_time_stronglyMeasurable _ hG _).add
    ((bblrDualLeadingMultiplier_time_measurable T σ).stronglyMeasurable.mul
      (bblrVStarAFESum_time_stronglyMeasurable _ hG _))

theorem rectangularFiniteSmallVStarCombinedRemainder_time_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T : ℝ) (σ : MomentShifts)
    (hα : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (X R : ℝ) :
    StronglyMeasurable (rectangularFiniteSmallVStarCombinedRemainder c T σ X R) :=
  (rectangularFiniteSmallVStarRemainder_time_stronglyMeasurable hc T σ _ hα X R).add
    ((bblrDualLeadingMultiplier_time_measurable T σ).stronglyMeasurable.mul
      (rectangularFiniteSmallVStarRemainder_time_stronglyMeasurable hc T σ _ (dual_raw_norm hα) X R))

theorem rectangularFiniteSmallVStarCombinedRemainder_uniform_rapid
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ t∈Icc T (2*T),
      ‖rectangularFiniteSmallVStarCombinedRemainder c T σ (T^(2+η)) (θ*Real.log T) t‖≤C*T^(-M) := by
  obtain ⟨C,hC,hb⟩ := rectangularFiniteSmallVStarRemainder_uniform_rapid_bound hc hc1 hη hθ K δ hδ hroot M
  obtain ⟨D,hD,hd⟩ := bblrDualLeadingMultiplier_uniform_normalized_bound K hK
  refine ⟨C*(1+D),by positivity,?_⟩
  filter_upwards [hb,hd,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num)] with T hb hd hs
  intro σ hσ t ht
  have hα := hs σ hσ
  unfold rectangularFiniteSmallVStarCombinedRemainder
  calc
    _≤‖rectangularFiniteSmallVStarRemainder c T σ (rawMomentShifts T σ) t (T^(2+η)) (θ*Real.log T)‖+
      ‖bblrDualLeadingMultiplier T σ (t/T)*
        rectangularFiniteSmallVStarRemainder c T σ (bblrSixShifts (rawMomentShifts T σ) 1) t (T^(2+η)) (θ*Real.log T)‖ := norm_add_le _ _
    _≤C*T^(-M)+D*(C*T^(-M)) := by
      rw [norm_mul]
      gcongr
      · exact hb σ hσ _ hα t ht
      · exact hd σ hσ t ht
      · exact hb σ hσ _ (dual_raw_norm hα) t ht
    _=_ := by ring

theorem rectangularVStarAFEIntegrand_eventually_integrable
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop, ∀ σ∈K, Integrable (rectangularVStarAFEIntegrand T σ f g Φ) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨P,hP,hΦb⟩ := rectangular_supported_weight_bounded Φ hΦ
  obtain ⟨C,hC,hb⟩ := bblrGaussianVStarAFESum_uniform_polynomial_bound K δ hδ hroot
  obtain ⟨D,hD,hd⟩ := bblrDualLeadingMultiplier_uniform_normalized_bound K hK
  have hCD : 0≤C*(1+D) := by positivity
  filter_upwards [hb,hd,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T hb hd hs hT
  intro σ hσ
  have hα := hs σ hσ
  have hbound (t : ℝ) (ht : t∈Icc T (2*T)) :
      ‖bblrVStarAFESum (polarPoleKiller T σ) (rawMomentShifts T σ) t+
        bblrDualLeadingMultiplier T σ (t/T)*
          bblrVStarAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) 1) t‖≤C*(1+D)*T^(3:ℝ) := by
    calc
      _≤‖bblrVStarAFESum (polarPoleKiller T σ) (rawMomentShifts T σ) t‖+
        ‖bblrDualLeadingMultiplier T σ (t/T)*
          bblrVStarAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) 1) t‖ := norm_add_le _ _
      _≤C*T^(3:ℝ)+D*(C*T^(3:ℝ)) := by
        rw [norm_mul]
        gcongr
        · exact hb σ hσ _ hα t ht
        · exact hd σ hσ t ht
        · exact hb σ hσ _ (dual_raw_norm hα) t ht
      _=_ := by ring
  exact rectangular_amplified_error_integrable hT hF hG hP hCD a b f g Φ _
    (rectangular_supported_profile_zero_above f hf) (rectangular_supported_profile_zero_above g hg)
    hfb hgb hΦ hΦb (rectangularVStarCombinedAFE_time_stronglyMeasurable T σ) hbound

theorem rectangularVStarCombinedRemainderMoment_uniform_rapid
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*
        rectangularFiniteSmallVStarCombinedRemainder c T σ (T^(2+η)) (θ*Real.log T) t) ∧
      ‖rectangularAmplifiedError T f g Φ
        (rectangularFiniteSmallVStarCombinedRemainder c T σ (T^(2+η)) (θ*Real.log T))‖≤C*T^(-M) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨P,hP,hΦb⟩ := rectangular_supported_weight_bounded Φ hΦ
  obtain ⟨C,hC,hb⟩ := rectangularFiniteSmallVStarCombinedRemainder_uniform_rapid
    hc hc1 hη hθ K hK δ hδ hroot (1+a+b+M)
  refine ⟨P*F*G*C,by positivity,?_⟩
  filter_upwards [hb,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T hb hs hT
  intro σ hσ
  have hfs := rectangular_supported_profile_zero_above f hf
  have hgs := rectangular_supported_profile_zero_above g hg
  refine ⟨rectangular_amplified_error_integrable hT hF hG hP hC a b f g Φ _ hfs hgs
    hfb hgb hΦ hΦb (rectangularFiniteSmallVStarCombinedRemainder_time_stronglyMeasurable hc T σ (hs σ hσ) _ _)
      (hb σ hσ),?_⟩
  have he := rectangular_amplified_error_norm_le hT hF hG hP hC a b f g Φ _ hfs hgs
    hfb hgb hΦ hΦb (hb σ hσ)
  convert he using 1
  congr 1
  ring

theorem rectangularVStarAFEMoment_uniform_finite_small_error
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      Integrable (rectangularVStarAFEIntegrand T σ f g Φ) ∧
      Integrable (rectangularFiniteSmallVStarIntegrand c T σ f g Φ (T^(2+η)) (θ*Real.log T)) ∧
      ‖rectangularVStarAFEMoment T σ f g Φ-
        rectangularFiniteSmallVStarMoment c T σ f g Φ (T^(2+η)) (θ*Real.log T)‖≤C*T^(-M) := by
  obtain ⟨C,hC,hb⟩ := rectangularVStarCombinedRemainderMoment_uniform_rapid
    hc hc1 hη hθ K hK δ hδ hroot a b f g Φ hf hg hΦ M
  have hfint := rectangularVStarAFEIntegrand_eventually_integrable K hK δ hδ hroot a b f g Φ hf hg hΦ
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,hfint,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num)] with T hb hfint hs
  intro σ hσ
  have hα := hs σ hσ
  have he : rectangularFiniteSmallVStarIntegrand c T σ f g Φ (T^(2+η)) (θ*Real.log T)=
      fun t : ℝ => rectangularVStarAFEIntegrand T σ f g Φ t-
        rectangularMomentWeight T f g Φ t*
          rectangularFiniteSmallVStarCombinedRemainder c T σ (T^(2+η)) (θ*Real.log T) t := by
    funext t
    unfold rectangularFiniteSmallVStarIntegrand rectangularVStarAFEIntegrand
      rectangularFiniteSmallVStarCombinedRemainder
    rw [rectangular_actual_VStar_finite_small_grid c T σ _ hα t _ _,
      rectangular_actual_VStar_finite_small_grid c T σ _ (dual_raw_norm hα) t _ _]
    ring
  have hi := hfint σ hσ
  have hE := (hb σ hσ).1
  refine ⟨hi,by rw [he]; exact hi.sub hE,?_⟩
  have hm : rectangularFiniteSmallVStarMoment c T σ f g Φ (T^(2+η)) (θ*Real.log T)=
      rectangularVStarAFEMoment T σ f g Φ-
        rectangularAmplifiedError T f g Φ
          (rectangularFiniteSmallVStarCombinedRemainder c T σ (T^(2+η)) (θ*Real.log T)) := by
    unfold rectangularFiniteSmallVStarMoment
    rw [he,integral_sub hi hE]
    rfl
  rw [hm,sub_sub_cancel]
  exact (hb σ hσ).2

end
end SixthMoment
