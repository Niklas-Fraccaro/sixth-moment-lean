import Sechstmoment.Numerator.U.Replacement.ErrorBound

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem rectangularReplacementErrorParts_uniform_sharp_power_bound
    {a b : ℝ} (ha : 0<a) (hab : a≤b) {ε : ℝ} (hε : 0<ε)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ p : Fin 3,
      Integrable (rectangularReplacementErrorPartIntegrand p T σ f g Φ) ∧
      ‖rectangularReplacementErrorPart p T σ f g Φ‖≤
        C*T^(rectangularFirstExponent a b ε) := by
  let s : ℝ := min ε (1/16)
  have hs : 0<s := lt_min hε (by norm_num)
  have hsε : s≤ε := min_le_left _ _
  have hsmax : s≤1/16 := min_le_right _ _
  have hc : 0<s/128 := by positivity
  have hc1 : s/128≤1 := by linarith
  have hη : 0<s/16 := by positivity
  have hq : 0≤rectangularFirstExponent a b ε := by dsimp [rectangularFirstExponent]; linarith
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  have hσR (σ : MomentShifts) (hσ : σ∈K) (j : Fin 4) : ‖σ j‖≤R :=
    ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left _ _)
  obtain ⟨A,hA,haT⟩ := rectangularReplacementErrorParts_uniform_finite_small_error
    hc hc1 hη zero_lt_one K hK δ hδ hroot a b f g Φ hf hg hΦ 0
  have he : 2*(s/128)<s/16 := by linarith only [hs]
  have hρ1 : s/16≤1 := by linarith only [hsmax]
  have hd : 0<s/8 := by positivity
  have hp : a+b+s/16+(s/16)/2+s/16+s/8≤rectangularFirstExponent a b ε := by
    dsimp [rectangularFirstExponent]
    linarith only [hs,hsε,hε]
  have hr : 1/2+a+b+(s/16)/4+s/16+s/8≤rectangularFirstExponent a b ε := by
    dsimp [rectangularFirstExponent]
    linarith only [hs,hsε]
  obtain ⟨C₀,hC₀,h₀T⟩ := a03_actual_weight_replacement_finite_contour_uniform_power_bound
    hf hg hΦ hc hc1 he hδ (by norm_num : (0:ℝ)≤1) hR hη hη hρ1 hd hq hp hr
  obtain ⟨C₁,hC₁,h₁T⟩ := a03_actual_dual_error_part_finite_contour_uniform_power_bound
    hf hg hΦ hc hc1 he hδ (by norm_num : (0:ℝ)≤1) hR hη hη hρ1 hd hq hp hr
  refine ⟨A+C₀+C₁,by positivity,?_⟩
  filter_upwards [haT,h₀T,h₁T,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T haT h₀T h₁T hsmall hT
  intro σ hσ p
  obtain ⟨hfull,hfinite,htail⟩ := haT σ hσ p
  simp only [neg_zero,Real.rpow_zero,mul_one] at htail
  refine ⟨hfull,?_⟩
  have h₀ : ‖a03ActualWeightReplacementFiniteContour (s/128) T a b (s/16) 1 f g Φ σ
      (rawMomentShifts T σ)‖≤C₀*T^(rectangularFirstExponent a b ε) := by
    have hh := (h₀T σ (hσR σ hσ) (hroot σ hσ) 0 1).2.2
    have hb := (le_add_of_nonneg_right (norm_nonneg _)).trans hh
    simpa [bblrSixShifts] using hb
  have h₁ (phasePart : Bool) :
      ‖a03ActualDualErrorPartFiniteContour phasePart (s/128) T a b (s/16) 1 f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) 1)‖≤C₁*T^(rectangularFirstExponent a b ε) :=
    (h₁T σ (hσR σ hσ) (hroot σ hσ) phasePart 1).2
  have hfin : ‖rectangularFiniteReplacementErrorPart p (s/128) T σ f g Φ
      (T^(2+s/16)) (Real.log T)‖≤(C₀+C₁)*T^(rectangularFirstExponent a b ε) := by
    have hpow : 0≤T^(rectangularFirstExponent a b ε) := Real.rpow_nonneg (zero_lt_one.trans hT).le _
    fin_cases p
    · change ‖rectangularFiniteOriginalWeightReplacementError (s/128) T σ f g Φ
        (T^(2+s/16)) (Real.log T)‖≤_
      have he := rectangularFiniteOriginalWeightReplacementError_eq_contour
        hc hT a b f g Φ hf hg hΦ σ (hsmall σ hσ) (s/16) 1
      simp only [one_mul] at he
      rw [he]
      nlinarith [h₀]
    · change ‖rectangularFiniteDualWeightReplacementError (s/128) T σ f g Φ
        (T^(2+s/16)) (Real.log T)‖≤_
      have he := rectangularFiniteDualWeightReplacementError_eq_contour
        hc hT a b f g Φ hf hg hΦ σ (hsmall σ hσ) (s/16) 1
      simp only [one_mul] at he
      rw [he]
      nlinarith [h₁ false]
    · change ‖rectangularFiniteDualPhaseReplacementError (s/128) T σ f g Φ
        (T^(2+s/16)) (Real.log T)‖≤_
      have he := rectangularFiniteDualPhaseReplacementError_eq_contour
        hc hT a b f g Φ hf hg hΦ σ (hsmall σ hσ) (s/16) 1
      simp only [one_mul] at he
      rw [he]
      nlinarith [h₁ true]
  have htq : 1≤T^(rectangularFirstExponent a b ε) := Real.one_le_rpow hT.le hq
  have ht : ‖rectangularReplacementErrorPart p T σ f g Φ-
      rectangularFiniteReplacementErrorPart p (s/128) T σ f g Φ
        (T^(2+s/16)) (Real.log T)‖≤A := by simpa only [one_mul] using htail
  have hsum : rectangularReplacementErrorPart p T σ f g Φ=
      (rectangularReplacementErrorPart p T σ f g Φ-
        rectangularFiniteReplacementErrorPart p (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T))+
      rectangularFiniteReplacementErrorPart p (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T) := by ring
  rw [hsum]
  calc
    _≤‖rectangularReplacementErrorPart p T σ f g Φ-
        rectangularFiniteReplacementErrorPart p (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T)‖+
      ‖rectangularFiniteReplacementErrorPart p (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T)‖ := norm_add_le _ _
    _≤A+(C₀+C₁)*T^(rectangularFirstExponent a b ε) := add_le_add ht hfin
    _≤(A+C₀+C₁)*T^(rectangularFirstExponent a b ε) := by nlinarith


theorem rectangularFullWeightAndDualPhaseErrors_uniform_sharp_power_bound
    {a b : ℝ} (ha : 0<a) (hab : a≤b) {ε : ℝ} (hε : 0<ε)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖rectangularOriginalWeightReplacementError T σ f g Φ‖+
      ‖rectangularDualWeightReplacementError T σ f g Φ‖+
      ‖rectangularDualPhaseReplacementError T σ f g Φ‖≤
        C*T^(rectangularFirstExponent a b ε) := by
  obtain ⟨C,hC,hb⟩ := rectangularReplacementErrorParts_uniform_sharp_power_bound
    ha hab hε K hK κ hκ hroot f g Φ hf hg hΦ
  refine ⟨3*C,by positivity,?_⟩
  filter_upwards [hb] with T hb
  intro σ hσ
  have hsum := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => (hb σ hσ p).2)
  have hright : (∑ _p : Fin 3,C*T^(rectangularFirstExponent a b ε))=
      (3*C)*T^(rectangularFirstExponent a b ε) := by simp; ring
  rw [hright] at hsum
  simpa [Fin.sum_univ_succ,rectangularReplacementErrorPart,rectangularReplacementErrorPartIntegrand,
    rectangularOriginalWeightReplacementError,rectangularDualWeightReplacementError,
    rectangularDualPhaseReplacementError,add_assoc] using hsum

end
end Sechstmoment
