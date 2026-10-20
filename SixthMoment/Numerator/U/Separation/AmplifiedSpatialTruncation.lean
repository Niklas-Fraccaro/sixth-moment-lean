import SixthMoment.Numerator.U.Reconstruction.ActualCoreReduction
import SixthMoment.Numerator.U.Reconstruction.SpatialAFETail


namespace SixthMoment
open Complex Source MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def rectangularSpatialCombinedTail (T : ℝ) (σ : MomentShifts) (X t : ℝ) : ℂ :=
  bblrAFESpatialTail (polarPoleKiller T σ) (rawMomentShifts T σ) t X+
    bblrDualMultiplier t (rawMomentShifts T σ)*
      bblrAFESpatialTail (polarPoleKiller T σ)
        (bblrSixShifts (rawMomentShifts T σ) 1) t X

def rectangularSpatialTailMoment (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) (X : ℝ) : ℂ :=
  rectangularAmplifiedError T f g Φ (rectangularSpatialCombinedTail T σ X)

def rectangularAFEProductIntegrand (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) (X t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*
    (bblrAFEProductSum (polarPoleKiller T σ) (rawMomentShifts T σ) t X+
      bblrDualMultiplier t (rawMomentShifts T σ)*
        bblrAFEProductSum (polarPoleKiller T σ)
          (bblrSixShifts (rawMomentShifts T σ) 1) t X)

def rectangularAFEProductMoment (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) (X : ℝ) : ℂ :=
  ∫ t : ℝ, rectangularAFEProductIntegrand T σ f g Φ X t

theorem rectangularSpatialCombinedTail_stronglyMeasurable (T : ℝ) (σ : MomentShifts)
    (hα : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (X : ℝ) :
    StronglyMeasurable (rectangularSpatialCombinedTail T σ X) := by
  have hr : ∀ j, |(rawMomentShifts T σ j).re|<1/2 := fun j =>
    ((Complex.abs_re_le_norm _).trans (hα j)).trans_lt (by norm_num)
  have hs : ∀ j, -1/2<(rawMomentShifts T σ j).re := by
    intro j
    simpa only [neg_div] using (abs_lt.mp (hr j)).1
  have hd := rectangular_dual_shifts_strip _ hr
  exact (bblrAFESpatialTail_time_stronglyMeasurable (polarPoleKiller T σ)
    (polarPoleKiller_differentiable T σ).continuous _ hs X).add
    ((rectangular_dual_multiplier_continuous _ hr).stronglyMeasurable.mul
      (bblrAFESpatialTail_time_stronglyMeasurable (polarPoleKiller T σ)
        (polarPoleKiller_differentiable T σ).continuous _ hd X))

theorem rectangularSpatialCombinedTail_uniform_rapid_decay
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0<ε) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ t∈Icc T (2*T),
      ‖rectangularSpatialCombinedTail T σ (T^(2+ε)) t‖≤C*T^(-N) := by
  obtain ⟨C,hC,hb⟩ := bblrGaussianAFESpatialTail_uniform_power_bound K δ hδ hρ hε N
  obtain ⟨D,hD,hd⟩ := bblrDualMultiplier_uniform_normalized_bound K hK
  refine ⟨C*(1+D),by positivity,?_⟩
  filter_upwards [hb,hd,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (0:ℝ)] with T hb hd hs hT
  intro σ hσ t ht
  have hα := hs σ hσ
  have hdual : ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) 1 j‖≤1/4 := by
    intro j
    fin_cases j <;> simp [bblrSixShifts] <;>
      first | simpa using hα 0 | simpa using hα 1 | simpa using hα 2 | simpa using hα 3
  unfold rectangularSpatialCombinedTail
  calc
    _ ≤ ‖bblrAFESpatialTail (polarPoleKiller T σ) (rawMomentShifts T σ) t (T^(2+ε))‖+
        ‖bblrDualMultiplier t (rawMomentShifts T σ)*
          bblrAFESpatialTail (polarPoleKiller T σ)
            (bblrSixShifts (rawMomentShifts T σ) 1) t (T^(2+ε))‖ := norm_add_le _ _
    _ ≤ C*T^(-N)+D*(C*T^(-N)) := by
      rw [norm_mul]
      gcongr
      · exact hb σ hσ _ hα t ht
      · exact hd σ hσ t ht
      · exact hb σ hσ _ hdual t ht
    _ = _ := by ring

theorem rectangularSpatialTailMoment_uniform_rapid_decay
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0<ε) (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*
        rectangularSpatialCombinedTail T σ (T^(2+ε)) t) ∧
      ‖rectangularSpatialTailMoment T σ f g Φ (T^(2+ε))‖≤C*T^(-N) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨Gc,hGc,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨P,hP,hΦb⟩ := rectangular_supported_weight_bounded Φ hΦ
  obtain ⟨C,hC,hb⟩ := rectangularSpatialCombinedTail_uniform_rapid_decay K hK δ hδ hρ hε (1+a+b+N)
  have hfs := rectangular_supported_profile_zero_above f hf
  have hgs := rectangular_supported_profile_zero_above g hg
  refine ⟨P*F*Gc*C,by positivity,?_⟩
  filter_upwards [hb,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T hb hs hT
  intro σ hσ
  refine ⟨rectangular_amplified_error_integrable hT hF hGc hP hC a b f g Φ
    _ hfs hgs hfb hgb hΦ hΦb
    (rectangularSpatialCombinedTail_stronglyMeasurable T σ (hs σ hσ) _) (hb σ hσ),?_⟩
  have he := rectangular_amplified_error_norm_le hT hF hGc hP hC a b f g Φ
    _ hfs hgs hfb hgb hΦ hΦb (hb σ hσ)
  convert he using 1
  congr 1
  ring

theorem rectangularAFEProductIntegrand_eq (T : ℝ) (σ : MomentShifts)
    (hα : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (f g Φ : ℝ → ℝ) (X t : ℝ) :
    rectangularAFEProductIntegrand T σ f g Φ X t =
      rectangularMomentWeight T f g Φ t*shiftedFourthProduct t (rawMomentShifts T σ)-
        rectangularMomentWeight T f g Φ t*
          bblrAFEDiscrepancy (polarPoleKiller T σ) (rawMomentShifts T σ) t-
        rectangularMomentWeight T f g Φ t*rectangularSpatialCombinedTail T σ X t := by
  have hr : ∀ j, |(rawMomentShifts T σ j).re|<1/2 := fun j =>
    ((Complex.abs_re_le_norm _).trans (hα j)).trans_lt (by norm_num)
  have hs : ∀ j, -1/2<(rawMomentShifts T σ j).re := by
    intro j
    simpa only [neg_div] using (abs_lt.mp (hr j)).1
  have hd := rectangular_dual_shifts_strip _ hr
  unfold rectangularAFEProductIntegrand rectangularSpatialCombinedTail bblrAFEDiscrepancy
  rw [bblrAFESum_product_add_spatial_tail _ _ (polarPoleKiller_BBLREntireWeight T σ _) hs t X,
    bblrAFESum_product_add_spatial_tail _ _ (polarPoleKiller_BBLREntireWeight T σ _) hd t X]
  ring

theorem rectangularAFEProductMoment_actual_reconstruction
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0<ε) (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      Integrable (rectangularAFEProductIntegrand T σ f g Φ (T^(2+ε))) ∧
      twistedFourthMoment T (rawMomentShifts T σ) f g Φ =
        rectangularAFEProductMoment T σ f g Φ (T^(2+ε))+
          rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
          rectangularSpatialTailMoment T σ f g Φ (T^(2+ε)) := by
  obtain ⟨C,_hC,htail⟩ := rectangularSpatialTailMoment_uniform_rapid_decay
    K hK δ hδ hρ hε a b f g Φ hf hg hΦ 0
  have hfs := rectangular_supported_profile_zero_above f hf
  have hgs := rectangular_supported_profile_zero_above g hg
  filter_upwards [htail,compactNormalizedShifts_eventually_norm_small K hK (1/8)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T htail hs hT
  intro σ hσ
  have hα : ∀ j, ‖rawMomentShifts T σ j‖<1/4 := fun j =>
    (hs σ hσ j).trans_lt (by norm_num)
  have hr : ∀ j, |(rawMomentShifts T σ j).re|<1/2 := fun j =>
    (Complex.abs_re_le_norm _).trans_lt ((hα j).trans (by norm_num))
  have hreal : ∀ j, -1/2<(rawMomentShifts T σ j).re := by
    intro j
    simpa only [neg_div] using (abs_lt.mp (hr j)).1
  have hdual := rectangular_dual_shifts_strip _ hr
  have hw := rectangular_moment_weight_continuous hT a b f g Φ hfs hgs hΦ
  have hws := rectangular_moment_weight_compact (zero_lt_one.trans hT).ne' f g Φ hΦ
  have h₀ := rectangular_weighted_shifted_product_integrable hT a b f g Φ hfs hgs hΦ _ hα
  have h₁ := rectangular_actual_AFE_weighted_integrable (polarPoleKiller T σ) _
    (polarPoleKiller_BBLREntireWeight T σ _) hreal _ hw hws
  have h₂ := rectangular_actual_AFE_weighted_integrable (polarPoleKiller T σ) _
    (polarPoleKiller_BBLREntireWeight T σ _) hdual
    (fun t => rectangularMomentWeight T f g Φ t*bblrDualMultiplier t (rawMomentShifts T σ))
    (hw.mul (rectangular_dual_multiplier_continuous _ hr)) hws.mul_right
  have hE : Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*
      bblrAFEDiscrepancy (polarPoleKiller T σ) (rawMomentShifts T σ) t) := by
    convert h₀.sub (h₁.add h₂) using 1
    funext t
    unfold bblrAFEDiscrepancy
    simp only [Pi.sub_apply,Pi.add_apply]
    ring
  have hS := (htail σ hσ).1
  have he : rectangularAFEProductIntegrand T σ f g Φ (T^(2+ε)) =
      fun t => rectangularMomentWeight T f g Φ t*shiftedFourthProduct t (rawMomentShifts T σ)-
        rectangularMomentWeight T f g Φ t*
          bblrAFEDiscrepancy (polarPoleKiller T σ) (rawMomentShifts T σ) t-
        rectangularMomentWeight T f g Φ t*rectangularSpatialCombinedTail T σ (T^(2+ε)) t :=
    funext (rectangularAFEProductIntegrand_eq T σ (fun j => (hα j).le) f g Φ _)
  refine ⟨by rw [he]; exact (h₀.sub hE).sub hS,?_⟩
  have hi : rectangularAFEProductMoment T σ f g Φ (T^(2+ε)) =
      rectangularAmplifiedError T f g Φ (fun t => shiftedFourthProduct t (rawMomentShifts T σ))-
        rectangularAmplifiedError T f g Φ
          (bblrAFEDiscrepancy (polarPoleKiller T σ) (rawMomentShifts T σ))-
        rectangularSpatialTailMoment T σ f g Φ (T^(2+ε)) := by
    unfold rectangularAFEProductMoment
    rw [he]
    change (∫ t : ℝ, ((fun t => rectangularMomentWeight T f g Φ t*
        shiftedFourthProduct t (rawMomentShifts T σ))-
      (fun t => rectangularMomentWeight T f g Φ t*
        bblrAFEDiscrepancy (polarPoleKiller T σ) (rawMomentShifts T σ) t)-
      (fun t => rectangularMomentWeight T f g Φ t*
        rectangularSpatialCombinedTail T σ (T^(2+ε)) t)) t)=_
    rw [integral_sub' (h₀.sub hE) hS,integral_sub' h₀ hE]
    rfl
  rw [← rectangular_twisted_moment_eq_weighted,← rectangular_AFE_integrated_error_eq_amplified] at hi
  rw [hi]
  ring

theorem rectangularAFEProductMoment_uniform_actual_error
    (hsource : BBLRv1FixedApproximateFEInput)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0<ε) (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      ‖twistedFourthMoment T (rawMomentShifts T σ) f g Φ-
        rectangularAFEProductMoment T σ f g Φ (T^(2+ε))‖≤C*T^(-N) := by
  obtain ⟨A,hA⟩ := exists_nat_gt (1+a+b+N)
  obtain ⟨C₀,hC₀,hb₀⟩ := rectangular_concrete_AFE_integrated_uniform_bound
    hsource K hK δ hδ hρ a b f g Φ hf hg hΦ A
  obtain ⟨C₁,hC₁,hb₁⟩ := rectangularSpatialTailMoment_uniform_rapid_decay
    K hK δ hδ hρ hε a b f g Φ hf hg hΦ N
  have hr := rectangularAFEProductMoment_actual_reconstruction K hK δ hδ hρ hε a b f g Φ hf hg hΦ
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  filter_upwards [hb₀,hb₁,hr,eventually_ge_atTop (1:ℝ)] with T hb₀ hb₁ hr hT
  intro σ hσ
  rw [(hr σ hσ).2]
  have he : rectangularAFEProductMoment T σ f g Φ (T^(2+ε))+
      rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
      rectangularSpatialTailMoment T σ f g Φ (T^(2+ε))-
      rectangularAFEProductMoment T σ f g Φ (T^(2+ε)) =
      rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
      rectangularSpatialTailMoment T σ f g Φ (T^(2+ε)) := by ring
  rw [he]
  calc
    _ ≤ ‖rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖+
        ‖rectangularSpatialTailMoment T σ f g Φ (T^(2+ε))‖ := norm_add_le _ _
    _ ≤ C₀*T^(1+a+b-(A:ℝ))+C₁*T^(-N) := add_le_add (hb₀ σ hσ) (hb₁ σ hσ).2
    _ ≤ C₀*T^(-N)+C₁*T^(-N) := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT (by linarith)) hC₀
    _ = _ := by ring

theorem rectangularAFEProductMoment_discrepancy_reduction
    (hsource : BBLRv1FixedApproximateFEInput)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hρ : ∀ σ∈K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0<ε) (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (N : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      ‖bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
        (rectangularAFEProductMoment T σ f g Φ (T^(2+ε))-
          bblrSixMainTerms T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)‖≤C*T^(-N) := by
  obtain ⟨C,hC,hb⟩ := rectangularAFEProductMoment_uniform_actual_error
    hsource K hK δ hδ hρ hε a b f g Φ hf hg hΦ N
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with T hb
  intro σ hσ
  simpa only [bblrMomentDiscrepancy,sub_sub_sub_cancel_right] using hb σ hσ

end
end SixthMoment
