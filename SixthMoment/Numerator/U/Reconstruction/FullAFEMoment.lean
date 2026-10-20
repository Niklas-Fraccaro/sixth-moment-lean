import SixthMoment.Numerator.U.Replacement.AmplifiedSmallContourMoment

namespace SixthMoment
open Complex Source MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

def rectangularFullAFEIntegrand (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) (t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*
    (bblrAFESum (polarPoleKiller T σ) (rawMomentShifts T σ) t+
      bblrDualMultiplier t (rawMomentShifts T σ)*
        bblrAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) 1) t)

def rectangularFullAFEMoment (T : ℝ) (σ : MomentShifts) (f g Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, rectangularFullAFEIntegrand T σ f g Φ t

theorem rectangularFullAFEMoment_actual_identity
    {T : ℝ} (hT : 1<T) (σ : MomentShifts)
    (hα : ∀ j, ‖rawMomentShifts T σ j‖<1/4)
    (a b : ℝ) (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (rectangularFullAFEIntegrand T σ f g Φ) ∧
    rectangularFullAFEMoment T σ f g Φ =
      twistedFourthMoment T (rawMomentShifts T σ) f g Φ-
        rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ := by
  have hfs := rectangular_supported_profile_zero_above f hf
  have hgs := rectangular_supported_profile_zero_above g hg
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
  have hfull : Integrable (rectangularFullAFEIntegrand T σ f g Φ) := by
    convert h₁.add h₂ using 1
    funext t
    unfold rectangularFullAFEIntegrand
    simp only [Pi.add_apply]
    ring
  have hE : Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*
      bblrAFEDiscrepancy (polarPoleKiller T σ) (rawMomentShifts T σ) t) := by
    convert h₀.sub hfull using 1
    funext t
    unfold rectangularFullAFEIntegrand bblrAFEDiscrepancy
    simp only [Pi.sub_apply]
    ring
  refine ⟨hfull,?_⟩
  rw [rectangular_twisted_moment_eq_weighted, rectangular_AFE_integrated_error_eq_amplified]
  unfold rectangularFullAFEMoment rectangularAmplifiedError
  rw [← integral_sub h₀ hE]
  congr 1
  funext t
  unfold rectangularFullAFEIntegrand bblrAFEDiscrepancy
  ring

theorem rectangularFullAFEMoment_uniform_finite_small_error
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      Integrable (rectangularFullAFEIntegrand T σ f g Φ) ∧
      Integrable (rectangularFiniteSmallGaussianGridIntegrand c T σ f g Φ
        (T^(2+η)) (θ*Real.log T)) ∧
      ‖rectangularFullAFEMoment T σ f g Φ-
        rectangularFiniteSmallGaussianGridMoment c T σ f g Φ
          (T^(2+η)) (θ*Real.log T)‖≤C*T^(-M) := by
  obtain ⟨A,hA,haT⟩ := rectangularFiniteGaussianTailMoment_uniform_rapid_decay
    K hK δ hδ hroot hη hθ a b f g Φ hf hg hΦ M
  obtain ⟨B,hB,hbT⟩ := rectangularSmallContourMomentError_uniform_rapid
    hc hc1 hη hθ K hK δ hδ hroot a b f g Φ hf hg hΦ M
  have hr := rectangularFiniteGaussianGridMoment_actual_reconstruction
    K hK δ hδ hroot hη hθ a b f g Φ hf hg hΦ
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  filter_upwards [haT,hbT,hr,compactNormalizedShifts_eventually_norm_small K hK (1/8)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T haT hbT hr hs hT
  intro σ hσ
  have hfull := rectangularFullAFEMoment_actual_identity hT σ
    (fun j => (hs σ hσ j).trans_lt (by norm_num)) a b f g Φ hf hg hΦ
  have he : rectangularFiniteSmallGaussianGridIntegrand c T σ f g Φ
      (T^(2+η)) (θ*Real.log T)=fun t : ℝ =>
        rectangularFiniteGaussianGridIntegrand T σ f g Φ (T^(2+η)) (θ*Real.log T) t-
          rectangularMomentWeight T f g Φ t*
            rectangularSmallContourCombinedError c T σ (T^(2+η)) (θ*Real.log T) t := by
    funext t
    unfold rectangularFiniteSmallGaussianGridIntegrand rectangularFiniteGaussianGridIntegrand
      rectangularSmallContourCombinedError
    ring
  have hi := (hr σ hσ).1
  have hE := (hbT σ hσ).1
  refine ⟨hfull.1,by rw [he]; exact hi.sub hE,?_⟩
  have hm : rectangularFiniteSmallGaussianGridMoment c T σ f g Φ
      (T^(2+η)) (θ*Real.log T)=
      rectangularFiniteGaussianGridMoment T σ f g Φ (T^(2+η)) (θ*Real.log T)-
        rectangularAmplifiedError T f g Φ
          (rectangularSmallContourCombinedError c T σ (T^(2+η)) (θ*Real.log T)) := by
    unfold rectangularFiniteSmallGaussianGridMoment
    rw [he,integral_sub hi hE]
    rfl
  have hd : rectangularFullAFEMoment T σ f g Φ-
      rectangularFiniteSmallGaussianGridMoment c T σ f g Φ (T^(2+η)) (θ*Real.log T)=
      rectangularFiniteGaussianTailMoment T σ f g Φ (T^(2+η)) (θ*Real.log T)+
        rectangularAmplifiedError T f g Φ
          (rectangularSmallContourCombinedError c T σ (T^(2+η)) (θ*Real.log T)) := by
    rw [hfull.2, (hr σ hσ).2,hm]
    ring
  rw [hd]
  calc
    _≤‖rectangularFiniteGaussianTailMoment T σ f g Φ (T^(2+η)) (θ*Real.log T)‖+
      ‖rectangularAmplifiedError T f g Φ
        (rectangularSmallContourCombinedError c T σ (T^(2+η)) (θ*Real.log T))‖ := norm_add_le _ _
    _≤A*T^(-M)+B*T^(-M) := add_le_add (haT σ hσ).2 (hbT σ hσ).2
    _=(A+B)*T^(-M) := by ring

end
end SixthMoment
