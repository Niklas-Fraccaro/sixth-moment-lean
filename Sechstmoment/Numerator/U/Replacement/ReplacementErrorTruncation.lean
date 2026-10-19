import Sechstmoment.Numerator.U.Replacement.ReplacementErrorDefinitions
import Sechstmoment.Numerator.U.Replacement.VStar.FiniteGrid

/-! Every literal separate unrestricted replacement error differs from its
finite small-contour version by a uniformly rapidly decreasing quantity.
The bounds use only actual spatial/contour tails, smooth profiles and compact
normalized shifts. No approximate-functional-equation input is needed. -/
namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

private theorem replacement_dual_raw_norm {T : ℝ} {σ : MomentShifts}
    (hα : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) :
    ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) 1 j‖≤1/4 := by
  intro j
  fin_cases j <;> simp [bblrSixShifts] <;>
    first | simpa using hα 0 | simpa using hα 1 | simpa using hα 2 | simpa using hα 3

private theorem replacement_AFE_stronglyMeasurable (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) :
    StronglyMeasurable (fun t : ℝ => bblrAFESum (polarPoleKiller T σ) α t) := by
  have hr : ∀ j, -1/2<(α j).re := by
    intro j
    have hh := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
    linarith
  exact StronglyMeasurable.tsum (fun n => rectangular_actual_AFE_summand_stronglyMeasurable
    _ (polarPoleKiller_differentiable T σ).continuous α hr n)

def rectangularGammaSmallRemainder (c T : ℝ) (σ α : MomentShifts)
    (X R t : ℝ) : ℂ :=
  bblrAFESum (polarPoleKiller T σ) α t-rectangularFiniteSmallGaussianCore c T σ α t X R

def rectangularStarSmallRemainder (c T : ℝ) (σ α : MomentShifts)
    (X R t : ℝ) : ℂ :=
  bblrVStarAFESum (polarPoleKiller T σ) α t-rectangularFiniteSmallVStarCore c T σ α t X R

theorem rectangularGammaSmallRemainder_time_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (X R : ℝ) :
    StronglyMeasurable (rectangularGammaSmallRemainder c T σ α X R) :=
  (replacement_AFE_stronglyMeasurable T σ α hα).sub
    (rectangularFiniteSmallGaussianCore_time_stronglyMeasurable hc T σ α hα X R)

theorem rectangularStarSmallRemainder_time_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T : ℝ) (σ α : MomentShifts) (X R : ℝ) :
    StronglyMeasurable (rectangularStarSmallRemainder c T σ α X R) :=
  (bblrVStarAFESum_time_stronglyMeasurable _ (polarPoleKiller_differentiable T σ).continuous α).sub
    (rectangularFiniteSmallVStarCore_time_stronglyMeasurable hc T σ α X R)

theorem rectangularGammaSmallRemainder_uniform_rapid
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      ‖rectangularGammaSmallRemainder c T σ α (T^(2+η)) (θ*Real.log T) t‖≤C*T^(-M) := by
  obtain ⟨A,hA,ha⟩ := rectangularFiniteGaussianRemainder_uniform_power_bound
    K δ hδ hroot hη hθ M
  obtain ⟨B,hB,hb⟩ := rectangular_actual_finite_small_contour_uniform_rapid_error
    hc hc1 hη hθ K δ hδ hroot M
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  filter_upwards [ha,hb] with T ha hb
  intro σ hσ α hα t ht
  have he : rectangularGammaSmallRemainder c T σ α (T^(2+η)) (θ*Real.log T) t=
      rectangularFiniteGaussianRemainder T σ α t (T^(2+η)) (θ*Real.log T)+
        (rectangularFiniteGaussianCore T σ α t (T^(2+η)) (θ*Real.log T)-
          rectangularFiniteSmallGaussianCore c T σ α t (T^(2+η)) (θ*Real.log T)) := by
    unfold rectangularGammaSmallRemainder
    rw [rectangular_actual_AFE_finite_gaussian_grid T σ α hα]
    ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (ha σ hσ α hα t ht)
    (hb σ hσ α hα t ht)).trans_eq (by ring))

theorem rectangularStarSmallRemainder_uniform_rapid
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ t∈Icc T (2*T),
      ‖rectangularStarSmallRemainder c T σ α (T^(2+η)) (θ*Real.log T) t‖≤C*T^(-M) := by
  simpa only [rectangularStarSmallRemainder] using bblrVStarAFESum_uniform_finite_small_error
    hc hc1 hη hθ K δ hδ hroot M

def rectangularReplacementTruncationBody (p : Fin 3) (c T : ℝ)
    (σ : MomentShifts) (X R t : ℝ) : ℂ :=
  if p=0 then
    rectangularGammaSmallRemainder c T σ (rawMomentShifts T σ) X R t-
      rectangularStarSmallRemainder c T σ (rawMomentShifts T σ) X R t
  else if p=1 then bblrDualMultiplier t (rawMomentShifts T σ)*
    (rectangularGammaSmallRemainder c T σ (bblrSixShifts (rawMomentShifts T σ) 1) X R t-
      rectangularStarSmallRemainder c T σ (bblrSixShifts (rawMomentShifts T σ) 1) X R t)
  else (bblrDualMultiplier t (rawMomentShifts T σ)-bblrDualLeadingMultiplier T σ (t/T))*
    rectangularStarSmallRemainder c T σ (bblrSixShifts (rawMomentShifts T σ) 1) X R t

theorem rectangularReplacementTruncationBody_integrand_identity
    (p : Fin 3) (c T : ℝ) (σ : MomentShifts) (f g Φ : ℝ→ℝ) (X R t : ℝ) :
    rectangularReplacementErrorPartIntegrand p T σ f g Φ t-
      rectangularFiniteReplacementErrorPartIntegrand p c T σ f g Φ X R t=
        rectangularMomentWeight T f g Φ t*rectangularReplacementTruncationBody p c T σ X R t := by
  fin_cases p <;>
    simp [rectangularReplacementErrorPartIntegrand,rectangularFiniteReplacementErrorPartIntegrand,
      rectangularOriginalWeightReplacementIntegrand,rectangularDualWeightReplacementIntegrand,
      rectangularDualPhaseReplacementIntegrand,rectangularFiniteOriginalWeightReplacementIntegrand,
      rectangularFiniteDualWeightReplacementIntegrand,rectangularFiniteDualPhaseReplacementIntegrand,
      rectangularReplacementTruncationBody,rectangularGammaSmallRemainder,rectangularStarSmallRemainder] <;> ring

theorem rectangularReplacementTruncationBody_time_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T : ℝ) (σ : MomentShifts)
    (hα : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (X R : ℝ) (p : Fin 3) :
    StronglyMeasurable (rectangularReplacementTruncationBody p c T σ X R) := by
  have hd := replacement_dual_raw_norm hα
  have hr : ∀ j, |(rawMomentShifts T σ j).re|<1/2 := fun j =>
    ((Complex.abs_re_le_norm _).trans (hα j)).trans_lt (by norm_num)
  have hχ := (rectangular_dual_multiplier_continuous _ hr).stronglyMeasurable
  have hlead := (bblrDualLeadingMultiplier_time_measurable T σ).stronglyMeasurable
  fin_cases p
  · change StronglyMeasurable (fun t : ℝ =>
      rectangularGammaSmallRemainder c T σ (rawMomentShifts T σ) X R t-
        rectangularStarSmallRemainder c T σ (rawMomentShifts T σ) X R t)
    exact (rectangularGammaSmallRemainder_time_stronglyMeasurable hc T σ _ hα X R).sub
        (rectangularStarSmallRemainder_time_stronglyMeasurable hc T σ _ X R)
  · change StronglyMeasurable (fun t : ℝ => bblrDualMultiplier t (rawMomentShifts T σ)*
      (rectangularGammaSmallRemainder c T σ (bblrSixShifts (rawMomentShifts T σ) 1) X R t-
        rectangularStarSmallRemainder c T σ (bblrSixShifts (rawMomentShifts T σ) 1) X R t))
    exact hχ.mul
      ((rectangularGammaSmallRemainder_time_stronglyMeasurable hc T σ _ hd X R).sub
        (rectangularStarSmallRemainder_time_stronglyMeasurable hc T σ _ X R))
  · change StronglyMeasurable (fun t : ℝ =>
      (bblrDualMultiplier t (rawMomentShifts T σ)-bblrDualLeadingMultiplier T σ (t/T))*
        rectangularStarSmallRemainder c T σ (bblrSixShifts (rawMomentShifts T σ) 1) X R t)
    exact (hχ.sub hlead).mul
      (rectangularStarSmallRemainder_time_stronglyMeasurable hc T σ _ X R)

theorem rectangularReplacementTruncationBody_uniform_rapid
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ p : Fin 3, ∀ t∈Icc T (2*T),
      ‖rectangularReplacementTruncationBody p c T σ (T^(2+η)) (θ*Real.log T) t‖≤C*T^(-M) := by
  obtain ⟨A,hA,ha⟩ := rectangularGammaSmallRemainder_uniform_rapid hc hc1 hη hθ K δ hδ hroot M
  obtain ⟨B,hB,hb⟩ := rectangularStarSmallRemainder_uniform_rapid hc hc1 hη hθ K δ hδ hroot M
  obtain ⟨D,hD,hd⟩ := bblrDualMultiplier_uniform_normalized_bound K hK
  obtain ⟨E,hE,he⟩ := bblrDualLeadingMultiplier_uniform_normalized_bound K hK
  refine ⟨(A+B)*(1+D+E),by positivity,?_⟩
  filter_upwards [ha,hb,hd,he,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (0:ℝ)] with T ha hb hd he hs hT
  intro σ hσ p t ht
  have hα := hs σ hσ
  have hdual := replacement_dual_raw_norm hα
  have hg₀ := ha σ hσ _ hα t ht
  have hs₀ := hb σ hσ _ hα t ht
  have hg₁ := ha σ hσ _ hdual t ht
  have hs₁ := hb σ hσ _ hdual t ht
  have hχ := hd σ hσ t ht
  have hl := he σ hσ t ht
  have hpow : 0≤T^(-M) := Real.rpow_nonneg hT.le _
  have hsum₀ := (norm_sub_le _ _).trans (add_le_add hg₀ hs₀)
  have hsum₁ := (norm_sub_le _ _).trans (add_le_add hg₁ hs₁)
  have hχsub := (norm_sub_le _ _).trans (add_le_add hχ hl)
  fin_cases p
  · change ‖rectangularGammaSmallRemainder c T σ (rawMomentShifts T σ) (T^(2+η)) (θ*Real.log T) t-
      rectangularStarSmallRemainder c T σ (rawMomentShifts T σ) (T^(2+η)) (θ*Real.log T) t‖≤_
    apply hsum₀.trans
    nlinarith [mul_nonneg (by linarith : 0≤D+E) (mul_nonneg (add_nonneg hA hB) hpow)]
  · change ‖bblrDualMultiplier t (rawMomentShifts T σ)*
      (rectangularGammaSmallRemainder c T σ (bblrSixShifts (rawMomentShifts T σ) 1) (T^(2+η)) (θ*Real.log T) t-
        rectangularStarSmallRemainder c T σ (bblrSixShifts (rawMomentShifts T σ) 1) (T^(2+η)) (θ*Real.log T) t)‖≤_
    rw [norm_mul]
    apply (mul_le_mul hχ hsum₁ (norm_nonneg _) hD.le).trans
    nlinarith [mul_nonneg (add_nonneg hA hB) hpow,
      mul_nonneg (by linarith : 0≤1+E) (mul_nonneg (add_nonneg hA hB) hpow)]
  · change ‖(bblrDualMultiplier t (rawMomentShifts T σ)-bblrDualLeadingMultiplier T σ (t/T))*
      rectangularStarSmallRemainder c T σ (bblrSixShifts (rawMomentShifts T σ) 1) (T^(2+η)) (θ*Real.log T) t‖≤_
    rw [norm_mul]
    apply (mul_le_mul hχsub hs₁ (norm_nonneg _) (by positivity)).trans
    nlinarith [mul_nonneg hA hpow,mul_nonneg (add_nonneg hD.le hE.le) (mul_nonneg hA hpow),
      mul_nonneg (add_nonneg hA hB) hpow]

def rectangularStarReplacementMultiplier (p : Fin 3) (T : ℝ) (σ : MomentShifts) (t : ℝ) : ℂ :=
  if p=0 then 1 else if p=1 then bblrDualMultiplier t (rawMomentShifts T σ)
  else bblrDualMultiplier t (rawMomentShifts T σ)-bblrDualLeadingMultiplier T σ (t/T)

def rectangularReplacementPartShifts (p : Fin 3) (T : ℝ) (σ : MomentShifts) : MomentShifts :=
  if p=0 then rawMomentShifts T σ else bblrSixShifts (rawMomentShifts T σ) 1

theorem rectangularStarReplacementMultiplier_time_stronglyMeasurable
    (T : ℝ) (σ : MomentShifts) (hα : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (p : Fin 3) :
    StronglyMeasurable (rectangularStarReplacementMultiplier p T σ) := by
  have hr : ∀ j, |(rawMomentShifts T σ j).re|<1/2 := fun j =>
    ((Complex.abs_re_le_norm _).trans (hα j)).trans_lt (by norm_num)
  have hχ := (rectangular_dual_multiplier_continuous _ hr).stronglyMeasurable
  have hl := (bblrDualLeadingMultiplier_time_measurable T σ).stronglyMeasurable
  unfold rectangularStarReplacementMultiplier
  split_ifs
  · exact stronglyMeasurable_const
  · exact hχ
  · exact hχ.sub hl

/-- The actual unrestricted Star AFE remains integrable with each of the
three concrete multiplier choices on the compact supported time interval. -/
theorem rectangularStarReplacementParts_eventually_integrable
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ p : Fin 3,
      Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*
        rectangularStarReplacementMultiplier p T σ t*
          bblrVStarAFESum (polarPoleKiller T σ) (rectangularReplacementPartShifts p T σ) t) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨P,hP,hΦb⟩ := rectangular_supported_weight_bounded Φ hΦ
  obtain ⟨C,hC,hb⟩ := bblrGaussianVStarAFESum_uniform_polynomial_bound K δ hδ hroot
  obtain ⟨D,hD,hd⟩ := bblrDualMultiplier_uniform_normalized_bound K hK
  obtain ⟨E,hE,he⟩ := bblrDualLeadingMultiplier_uniform_normalized_bound K hK
  filter_upwards [hb,hd,he,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T hb hd he hs hT
  intro σ hσ p
  have hα := hs σ hσ
  have hpα : ∀ j, ‖rectangularReplacementPartShifts p T σ j‖≤1/4 := by
    unfold rectangularReplacementPartShifts
    split_ifs
    · exact hα
    · exact replacement_dual_raw_norm hα
  have hmp (t : ℝ) (ht : t∈Icc T (2*T)) :
      ‖rectangularStarReplacementMultiplier p T σ t‖≤1+D+E := by
    unfold rectangularStarReplacementMultiplier
    split_ifs
    · simp only [norm_one]
      linarith
    · exact (hd σ hσ t ht).trans (by linarith)
    · exact ((norm_sub_le _ _).trans (add_le_add (hd σ hσ t ht) (he σ hσ t ht))).trans
        (by linarith)
  have hsm : StronglyMeasurable (fun t : ℝ => rectangularStarReplacementMultiplier p T σ t*
      bblrVStarAFESum (polarPoleKiller T σ) (rectangularReplacementPartShifts p T σ) t) :=
    (rectangularStarReplacementMultiplier_time_stronglyMeasurable T σ hα p).mul
      (bblrVStarAFESum_time_stronglyMeasurable _ (polarPoleKiller_differentiable T σ).continuous _)
  have hbound (t : ℝ) (ht : t∈Icc T (2*T)) :
      ‖rectangularStarReplacementMultiplier p T σ t*
        bblrVStarAFESum (polarPoleKiller T σ) (rectangularReplacementPartShifts p T σ) t‖≤
          ((1+D+E)*C)*T^(3:ℝ) := by
    rw [norm_mul]
    exact (mul_le_mul (hmp t ht) (hb σ hσ _ hpα t ht) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hi := rectangular_amplified_error_integrable hT hF hG hP (by positivity : 0≤(1+D+E)*C)
    a b f g Φ _ (rectangular_supported_profile_zero_above f hf)
    (rectangular_supported_profile_zero_above g hg) hfb hgb hΦ hΦb hsm hbound
  convert hi using 1
  funext t
  ring

/-- Integrability of every separate full error is proved from actual Gamma
AFE integrability and the actual Star polynomial majorant. -/
theorem rectangularReplacementErrorParts_eventually_integrable
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ p : Fin 3,
      Integrable (rectangularReplacementErrorPartIntegrand p T σ f g Φ) := by
  have hstar := rectangularStarReplacementParts_eventually_integrable
    K hK δ hδ hroot a b f g Φ hf hg hΦ
  filter_upwards [hstar,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T hstar hs hT
  intro σ hσ p
  have hα := hs σ hσ
  have hr : ∀ j, |(rawMomentShifts T σ j).re|<1/2 := fun j =>
    ((Complex.abs_re_le_norm _).trans (hα j)).trans_lt (by norm_num)
  have hreal : ∀ j, -1/2<(rawMomentShifts T σ j).re := by
    intro j
    have hh := (abs_lt.mp (hr j)).1
    linarith
  have hdualreal := rectangular_dual_shifts_strip _ hr
  have hfs := rectangular_supported_profile_zero_above f hf
  have hgs := rectangular_supported_profile_zero_above g hg
  have hw := rectangular_moment_weight_continuous hT a b f g Φ hfs hgs hΦ
  have hws := rectangular_moment_weight_compact (zero_lt_one.trans hT).ne' f g Φ hΦ
  have hΓ₀ := rectangular_actual_AFE_weighted_integrable (polarPoleKiller T σ) _
    (polarPoleKiller_BBLREntireWeight T σ _) hreal _ hw hws
  have hΓ₁ := rectangular_actual_AFE_weighted_integrable (polarPoleKiller T σ) _
    (polarPoleKiller_BBLREntireWeight T σ _) hdualreal
    (fun t => rectangularMomentWeight T f g Φ t*bblrDualMultiplier t (rawMomentShifts T σ))
    (hw.mul (rectangular_dual_multiplier_continuous _ hr)) hws.mul_right
  have hs₀ := hstar σ hσ (0:Fin 3)
  have hs₁ := hstar σ hσ (1:Fin 3)
  have hs₂ := hstar σ hσ (2:Fin 3)
  fin_cases p
  · change Integrable (rectangularOriginalWeightReplacementIntegrand T σ f g Φ)
    convert hΓ₀.sub hs₀ using 1
    funext t
    simp only [Fin.isValue,ite_true,Pi.sub_apply,
      rectangularOriginalWeightReplacementIntegrand,rectangularStarReplacementMultiplier,
      rectangularReplacementPartShifts]
    ring
  · change Integrable (rectangularDualWeightReplacementIntegrand T σ f g Φ)
    convert hΓ₁.sub hs₁ using 1
    funext t
    simp only [Fin.isValue,show ¬ ((1:Fin 3)=0) by decide,
      ite_false,ite_true,Pi.sub_apply,rectangularDualWeightReplacementIntegrand,
      rectangularStarReplacementMultiplier,rectangularReplacementPartShifts]
    ring
  · change Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*
      (bblrDualMultiplier t (rawMomentShifts T σ)-bblrDualLeadingMultiplier T σ (t/T))*
        bblrVStarAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) 1) t)
    exact hs₂

theorem rectangularReplacementTruncationMoment_uniform_rapid
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ p : Fin 3,
      Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*
        rectangularReplacementTruncationBody p c T σ (T^(2+η)) (θ*Real.log T) t) ∧
      ‖rectangularAmplifiedError T f g Φ
        (rectangularReplacementTruncationBody p c T σ (T^(2+η)) (θ*Real.log T))‖≤C*T^(-M) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨P,hP,hΦb⟩ := rectangular_supported_weight_bounded Φ hΦ
  obtain ⟨C,hC,hb⟩ := rectangularReplacementTruncationBody_uniform_rapid hc hc1 hη hθ
    K hK δ hδ hroot (1+a+b+M)
  refine ⟨P*F*G*C,by positivity,?_⟩
  filter_upwards [hb,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T hb hs hT
  intro σ hσ p
  refine ⟨rectangular_amplified_error_integrable hT hF hG hP hC a b f g Φ _
    (rectangular_supported_profile_zero_above f hf) (rectangular_supported_profile_zero_above g hg)
    hfb hgb hΦ hΦb (rectangularReplacementTruncationBody_time_stronglyMeasurable hc T σ
      (hs σ hσ) _ _ p) (hb σ hσ p),?_⟩
  have he := rectangular_amplified_error_norm_le hT hF hG hP hC a b f g Φ _
    (rectangular_supported_profile_zero_above f hf) (rectangular_supported_profile_zero_above g hg)
    hfb hgb hΦ hΦb (hb σ hσ p)
  convert he using 1
  congr 1
  ring

/-- Each of the three fully amplified unrestricted error integrals has an
integrable finite counterpart, with an arbitrary-power difference estimate.
All hypotheses describe the actual profiles and normalized shift set. -/
theorem rectangularReplacementErrorParts_uniform_finite_small_error
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ p : Fin 3,
      Integrable (rectangularReplacementErrorPartIntegrand p T σ f g Φ) ∧
      Integrable (rectangularFiniteReplacementErrorPartIntegrand p c T σ f g Φ
        (T^(2+η)) (θ*Real.log T)) ∧
      ‖rectangularReplacementErrorPart p T σ f g Φ-
        rectangularFiniteReplacementErrorPart p c T σ f g Φ (T^(2+η)) (θ*Real.log T)‖≤C*T^(-M) := by
  obtain ⟨C,hC,hb⟩ := rectangularReplacementTruncationMoment_uniform_rapid hc hc1 hη hθ
    K hK δ hδ hroot a b f g Φ hf hg hΦ M
  have hi := rectangularReplacementErrorParts_eventually_integrable K hK δ hδ hroot
    a b f g Φ hf hg hΦ
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,hi] with T hb hi
  intro σ hσ p
  have hfull := hi σ hσ p
  have hrem := (hb σ hσ p).1
  have hfin : Integrable (rectangularFiniteReplacementErrorPartIntegrand p c T σ f g Φ
      (T^(2+η)) (θ*Real.log T)) := by
    convert hfull.sub hrem using 1
    funext t
    have he := rectangularReplacementTruncationBody_integrand_identity p c T σ f g Φ
      (T^(2+η)) (θ*Real.log T) t
    dsimp only [Pi.sub_apply]
    linear_combination -he
  refine ⟨hfull,hfin,?_⟩
  have he : rectangularReplacementErrorPart p T σ f g Φ-
      rectangularFiniteReplacementErrorPart p c T σ f g Φ (T^(2+η)) (θ*Real.log T)=
      rectangularAmplifiedError T f g Φ
        (rectangularReplacementTruncationBody p c T σ (T^(2+η)) (θ*Real.log T)) := by
    unfold rectangularReplacementErrorPart rectangularFiniteReplacementErrorPart rectangularAmplifiedError
    rw [←integral_sub hfull hfin]
    apply integral_congr_ae
    filter_upwards [] with t
    exact rectangularReplacementTruncationBody_integrand_identity p c T σ f g Φ
      (T^(2+η)) (θ*Real.log T) t
  rw [he]
  exact (hb σ hσ p).2

end
end Sechstmoment
