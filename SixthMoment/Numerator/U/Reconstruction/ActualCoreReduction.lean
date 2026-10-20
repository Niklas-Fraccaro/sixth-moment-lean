import SixthMoment.Numerator.U.Separation.AmplifiedGaussianTruncation


namespace SixthMoment
open Complex Source MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
noncomputable section

def rectangularGaussianCoreIntegrand (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) (R t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*
    (bblrGaussianAFECore T σ (rawMomentShifts T σ) t R+
      bblrDualMultiplier t (rawMomentShifts T σ)*
        bblrGaussianAFECore T σ (bblrSixShifts (rawMomentShifts T σ) 1) t R)

def rectangularGaussianCoreMoment (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) (R : ℝ) : ℂ :=
  ∫ t : ℝ, rectangularGaussianCoreIntegrand T σ f g Φ R t

theorem bblrAFEDiscrepancy_time_stronglyMeasurable (G : ℂ → ℂ) (hG : Continuous G)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ < 1/4) :
    StronglyMeasurable (bblrAFEDiscrepancy G α) := by
  have hr : ∀ j, |(α j).re| < 1/2 := fun j =>
    ((Complex.abs_re_le_norm _).trans_lt (hα j)).trans (by norm_num)
  have hs : ∀ j, -1/2 < (α j).re := by
    intro j
    simpa only [neg_div] using (abs_lt.mp (hr j)).1
  have hd := rectangular_dual_shifts_strip α hr
  have h₀ : StronglyMeasurable (fun t => bblrAFESum G α t) :=
    StronglyMeasurable.tsum (fun n =>
      rectangular_actual_AFE_summand_stronglyMeasurable G hG α hs n)
  have h₁ : StronglyMeasurable (fun t => bblrAFESum G (bblrSixShifts α 1) t) :=
    StronglyMeasurable.tsum (fun n =>
      rectangular_actual_AFE_summand_stronglyMeasurable G hG (bblrSixShifts α 1) hd n)
  exact (rectangular_shifted_product_continuous α hα).stronglyMeasurable.sub
    (h₀.add ((rectangular_dual_multiplier_continuous α hr).stronglyMeasurable.mul h₁))

theorem rectangular_twisted_moment_eq_weighted (T : ℝ) (α : MomentShifts)
    (f g Φ : ℝ → ℝ) :
    twistedFourthMoment T α f g Φ =
      rectangularAmplifiedError T f g Φ (fun t => shiftedFourthProduct t α) := by
  unfold twistedFourthMoment rectangularAmplifiedError
  apply integral_congr_ae
  filter_upwards [] with t
  unfold twistedFourthIntegrand rectangularMomentWeight
  ring

theorem rectangular_weighted_shifted_product_integrable {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ) (hf : ∀ x, a < x → f x=0)
    (hg : ∀ x, b < x → g x=0) (hΦ : SmoothDyadicWeight Φ)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ < 1/4) :
    Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*shiftedFourthProduct t α) :=
  ((rectangular_moment_weight_continuous hT a b f g Φ hf hg hΦ).mul
    (rectangular_shifted_product_continuous α hα)).integrable_of_hasCompactSupport
      ((rectangular_moment_weight_compact (zero_lt_one.trans hT).ne' f g Φ hΦ).mul_right)

theorem rectangularGaussianCoreIntegrand_eq {T : ℝ} (hT : 0 < T)
    (σ : MomentShifts) (hα : ∀ j, ‖rawMomentShifts T σ j‖ ≤ 1/4)
    (f g Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (R : ℝ) (hR : 0 ≤ R) (t : ℝ) :
    rectangularGaussianCoreIntegrand T σ f g Φ R t =
      rectangularMomentWeight T f g Φ t*shiftedFourthProduct t (rawMomentShifts T σ)-
        rectangularMomentWeight T f g Φ t*
          bblrAFEDiscrepancy (polarPoleKiller T σ) (rawMomentShifts T σ) t-
        rectangularMomentWeight T f g Φ t*rectangularGaussianCombinedTail T σ R t := by
  by_cases ht : t ∈ Icc T (2*T)
  · have htp : 0 ≤ t := by linarith [ht.1]
    have hd : ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) 1 j‖ ≤ 1/4 := by
      intro j
      fin_cases j <;> simp [bblrSixShifts] <;>
        first | simpa using hα 0 | simpa using hα 1 | simpa using hα 2 | simpa using hα 3
    unfold rectangularGaussianCoreIntegrand rectangularGaussianCombinedTail bblrAFEDiscrepancy
    rw [bblrGaussianAFE_core_add_tail T σ _ t R htp hR hα,
      bblrGaussianAFE_core_add_tail T σ _ t R htp hR hd]
    ring
  · simp [rectangularGaussianCoreIntegrand,
      rectangular_moment_weight_zero_outside hT f g Φ hΦ t ht]

theorem rectangularGaussianCoreMoment_actual_reconstruction
    (hsource : BBLRv1FixedApproximateFEInput)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0 < θ) (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      Integrable (rectangularGaussianCoreIntegrand T σ f g Φ (θ*Real.log T)) ∧
      twistedFourthMoment T (rawMomentShifts T σ) f g Φ =
        rectangularGaussianCoreMoment T σ f g Φ (θ*Real.log T)+
          rectangularAFEIntegratedError T (rawMomentShifts T σ)
            (polarPoleKiller T σ) f g Φ+
          rectangularGaussianTailMoment T σ f g Φ (θ*Real.log T) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨Gc,hGc,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨P,hP,hΦb⟩ := rectangular_supported_weight_bounded Φ hΦ
  obtain ⟨C,hC,hb⟩ := polarPoleKiller_AFE_uniform_remainder hsource K hK δ hδ hρ 0
  obtain ⟨D,_hD,htail⟩ := rectangularGaussianTailMoment_uniform_logarithmic_bound
    K hK δ hδ hρ hθ a b f g Φ hf hg hΦ 0
  have hfs := rectangular_supported_profile_zero_above f hf
  have hgs := rectangular_supported_profile_zero_above g hg
  filter_upwards [hb,htail,compactNormalizedShifts_eventually_norm_small K hK (1/8)
    (by norm_num),eventually_gt_atTop (1 : ℝ)] with T hb htail hs hT
  intro σ hσ
  have hα : ∀ j, ‖rawMomentShifts T σ j‖ < 1/4 := fun j =>
    (hs σ hσ j).trans_lt (by norm_num)
  have h₀ := rectangular_weighted_shifted_product_integrable hT a b f g Φ hfs hgs hΦ
    (rawMomentShifts T σ) hα
  have h₁ := rectangular_amplified_error_integrable hT hF hGc hP hC a b f g Φ
    (bblrAFEDiscrepancy (polarPoleKiller T σ) (rawMomentShifts T σ))
    hfs hgs hfb hgb hΦ hΦb
    (bblrAFEDiscrepancy_time_stronglyMeasurable (polarPoleKiller T σ)
      (polarPoleKiller_differentiable T σ).continuous (rawMomentShifts T σ) hα)
    (hb σ hσ)
  have h₂ := (htail σ hσ).1
  have he : rectangularGaussianCoreIntegrand T σ f g Φ (θ*Real.log T) =
      fun t => rectangularMomentWeight T f g Φ t*shiftedFourthProduct t (rawMomentShifts T σ)-
        rectangularMomentWeight T f g Φ t*
          bblrAFEDiscrepancy (polarPoleKiller T σ) (rawMomentShifts T σ) t-
        rectangularMomentWeight T f g Φ t*
          rectangularGaussianCombinedTail T σ (θ*Real.log T) t := by
    funext t
    exact rectangularGaussianCoreIntegrand_eq (zero_lt_one.trans hT) σ
      (fun j => (hα j).le) f g Φ hΦ _ (mul_nonneg hθ.le (Real.log_nonneg hT.le)) t
  refine ⟨by rw [he]; exact (h₀.sub h₁).sub h₂,?_⟩
  have hi : rectangularGaussianCoreMoment T σ f g Φ (θ*Real.log T) =
      rectangularAmplifiedError T f g Φ (fun t => shiftedFourthProduct t (rawMomentShifts T σ))-
        rectangularAmplifiedError T f g Φ
          (bblrAFEDiscrepancy (polarPoleKiller T σ) (rawMomentShifts T σ))-
        rectangularGaussianTailMoment T σ f g Φ (θ*Real.log T) := by
    unfold rectangularGaussianCoreMoment
    rw [he]
    change (∫ t : ℝ, ((fun t => rectangularMomentWeight T f g Φ t*
        shiftedFourthProduct t (rawMomentShifts T σ))-
      (fun t => rectangularMomentWeight T f g Φ t*
        bblrAFEDiscrepancy (polarPoleKiller T σ) (rawMomentShifts T σ) t)-
      (fun t => rectangularMomentWeight T f g Φ t*
        rectangularGaussianCombinedTail T σ (θ*Real.log T) t)) t) = _
    rw [integral_sub' (h₀.sub h₁) h₂,integral_sub' h₀ h₁]
    rfl
  rw [← rectangular_twisted_moment_eq_weighted,
    ← rectangular_AFE_integrated_error_eq_amplified] at hi
  rw [hi]
  ring

theorem rectangularGaussianCoreMoment_uniform_actual_error
    (hsource : BBLRv1FixedApproximateFEInput)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0 < θ) (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (N : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      ‖twistedFourthMoment T (rawMomentShifts T σ) f g Φ-
        rectangularGaussianCoreMoment T σ f g Φ (θ*Real.log T)‖ ≤ C*T^(-N) := by
  obtain ⟨A,hA⟩ := exists_nat_gt (1+a+b+N)
  obtain ⟨C₀,hC₀,hb₀⟩ := rectangular_concrete_AFE_integrated_uniform_bound
    hsource K hK δ hδ hρ a b f g Φ hf hg hΦ A
  obtain ⟨C₁,hC₁,hb₁⟩ := rectangularGaussianTailMoment_uniform_rapid_decay
    K hK δ hδ hρ hθ a b f g Φ hf hg hΦ N
  have hr := rectangularGaussianCoreMoment_actual_reconstruction
    hsource K hK δ hδ hρ hθ a b f g Φ hf hg hΦ
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  filter_upwards [hb₀,hb₁,hr,eventually_ge_atTop (1 : ℝ)] with T hb₀ hb₁ hr hT
  intro σ hσ
  rw [(hr σ hσ).2]
  have he : rectangularGaussianCoreMoment T σ f g Φ (θ*Real.log T)+
      rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
      rectangularGaussianTailMoment T σ f g Φ (θ*Real.log T)-
      rectangularGaussianCoreMoment T σ f g Φ (θ*Real.log T) =
      rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
      rectangularGaussianTailMoment T σ f g Φ (θ*Real.log T) := by ring
  rw [he]
  calc
    _ ≤ ‖rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖+
        ‖rectangularGaussianTailMoment T σ f g Φ (θ*Real.log T)‖ := norm_add_le _ _
    _ ≤ C₀*T^(1+a+b-(A : ℝ))+C₁*T^(-N) := add_le_add (hb₀ σ hσ) (hb₁ σ hσ)
    _ ≤ C₀*T^(-N)+C₁*T^(-N) := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ hC₀
      exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
    _ = _ := by ring

theorem rectangularGaussianCoreMoment_discrepancy_reduction
    (hsource : BBLRv1FixedApproximateFEInput)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0 < θ) (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (N : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      ‖bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
        (rectangularGaussianCoreMoment T σ f g Φ (θ*Real.log T)-
          bblrSixMainTerms T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)‖ ≤ C*T^(-N) := by
  obtain ⟨C,hC,hb⟩ := rectangularGaussianCoreMoment_uniform_actual_error
    hsource K hK δ hδ hρ hθ a b f g Φ hf hg hΦ N
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with T hb
  intro σ hσ
  simpa only [bblrMomentDiscrepancy,sub_sub_sub_cancel_right] using hb σ hσ

end
end SixthMoment
