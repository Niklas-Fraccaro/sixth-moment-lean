import SixthMoment.Numerator.U.Replacement.CompleteWeightReplacement
import SixthMoment.Numerator.U.Replacement.DualErrorPartsBound
import SixthMoment.Numerator.U.Replacement.ReplacementErrorMellin
import SixthMoment.Numerator.U.Replacement.ReplacementErrorTruncation

namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem rectangularReplacementErrorParts_uniform_power_bound
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ p : Fin 3,
      Integrable (rectangularReplacementErrorPartIntegrand p T σ f g Φ) ∧
      ‖rectangularReplacementErrorPart p T σ f g Φ‖≤
        C*T^(rectangularFirstExponent a b (rectangularSlack a b)) := by
  let s := rectangularSlack a b
  have hs : 0<s := (rectangular_slack_bounds hab hrect).1
  have hsmax : s≤1/16 := by dsimp [s,rectangularSlack]; linarith
  have hc : 0<s/128 := by positivity
  have hc1 : s/128≤1 := by linarith
  have hη : 0<s/16 := by positivity
  have hq : 0≤rectangularFirstExponent a b s := by dsimp [rectangularFirstExponent]; linarith
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  have hσR (σ : MomentShifts) (hσ : σ∈K) (j : Fin 4) : ‖σ j‖≤R :=
    ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left _ _)
  obtain ⟨A,hA,haT⟩ := rectangularReplacementErrorParts_uniform_finite_small_error
    hc hc1 hη zero_lt_one K hK δ hδ hroot a b f g Φ hf hg hΦ 0
  obtain ⟨C₀,hC₀,h₀T⟩ := a03_actual_weight_replacement_rectangular_contour_uniform_power_bound
    hf hg hΦ ha hab hrect hδ hR
  obtain ⟨C₁,hC₁,h₁T⟩ := a03_actual_dual_error_part_rectangular_contour_uniform_power_bound
    hf hg hΦ ha hab hrect hδ hR
  refine ⟨A+C₀+C₁,by positivity,?_⟩
  filter_upwards [haT,h₀T,h₁T,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T haT h₀T h₁T hsmall hT
  intro σ hσ p
  obtain ⟨hfull,hfinite,htail⟩ := haT σ hσ p
  simp only [neg_zero,Real.rpow_zero,mul_one] at htail
  refine ⟨hfull,?_⟩
  have h₀ : ‖a03ActualWeightReplacementFiniteContour (s/128) T a b (s/16) 1 f g Φ σ
      (rawMomentShifts T σ)‖≤C₀*T^(rectangularFirstExponent a b s) := by
    have hh := h₀T σ (hσR σ hσ) (hroot σ hσ) 0 1
    have hb := (le_add_of_nonneg_right (norm_nonneg _)).trans hh
    simpa [bblrSixShifts] using hb
  have h₁ (phasePart : Bool) :
      ‖a03ActualDualErrorPartFiniteContour phasePart (s/128) T a b (s/16) 1 f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) 1)‖≤C₁*T^(rectangularFirstExponent a b s) :=
    h₁T σ (hσR σ hσ) (hroot σ hσ) phasePart 1
  have hfin : ‖rectangularFiniteReplacementErrorPart p (s/128) T σ f g Φ
      (T^(2+s/16)) (Real.log T)‖≤(C₀+C₁)*T^(rectangularFirstExponent a b s) := by
    have hpow : 0≤T^(rectangularFirstExponent a b s) := Real.rpow_nonneg (zero_lt_one.trans hT).le _
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
  have htq : 1≤T^(rectangularFirstExponent a b s) := Real.one_le_rpow hT.le hq
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
    _≤A+(C₀+C₁)*T^(rectangularFirstExponent a b s) := add_le_add ht hfin
    _≤(A+C₀+C₁)*T^(rectangularFirstExponent a b s) := by nlinarith

theorem rectangularReplacementErrorParts_uniform_oT
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      (∑ p : Fin 3, ‖rectangularReplacementErrorPart p T σ f g Φ‖)≤ε*T := by
  obtain ⟨C,hC,hb⟩ := rectangularReplacementErrorParts_uniform_power_bound
    ha hab hrect K hK δ hδ hroot f g Φ hf hg hΦ
  have hs := rectangular_slack_bounds hab hrect
  have hq : rectangularFirstExponent a b (rectangularSlack a b)<1 := by linarith [hs.1,hs.2.1]
  have ho := (rpow_isLittleO_id_of_lt_one hq).const_mul_left (3*C)
  intro ε hε
  filter_upwards [hb,ho.bound hε,eventually_gt_atTop (0:ℝ)] with T hb ho hT
  intro σ hσ
  calc
    _≤∑ p : Fin 3, C*T^(rectangularFirstExponent a b (rectangularSlack a b)) :=
      Finset.sum_le_sum (fun p _ => (hb σ hσ p).2)
    _=(3*C)*T^(rectangularFirstExponent a b (rectangularSlack a b)) := by simp; ring
    _≤ε*T := by
      have hn : 0≤(3*C)*T^(rectangularFirstExponent a b (rectangularSlack a b)) := by positivity
      simpa only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_pos hT] using ho

theorem rectangularFullWeightAndDualPhaseErrors_uniform_oT
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      ‖rectangularOriginalWeightReplacementError T σ f g Φ‖+
      ‖rectangularDualWeightReplacementError T σ f g Φ‖+
      ‖rectangularDualPhaseReplacementError T σ f g Φ‖≤ε*T := by
  intro ε hε
  filter_upwards [rectangularReplacementErrorParts_uniform_oT ha hab hrect K hK δ hδ hroot
    f g Φ hf hg hΦ ε hε] with T hT
  intro σ hσ
  simpa [Fin.sum_univ_succ,rectangularReplacementErrorPart,
    rectangularReplacementErrorPartIntegrand,rectangularOriginalWeightReplacementError,
    rectangularDualWeightReplacementError,rectangularDualPhaseReplacementError,add_assoc] using hT σ hσ

end
end SixthMoment
