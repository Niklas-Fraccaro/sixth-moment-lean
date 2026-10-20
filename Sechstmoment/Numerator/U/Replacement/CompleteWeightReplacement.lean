import Sechstmoment.Numerator.U.Reconstruction.FullAFEMoment
import Sechstmoment.Numerator.U.Replacement.AmplifiedVStarFiniteGrid
import Sechstmoment.Numerator.U.Replacement.ReplacementMomentMellin
import Sechstmoment.Numerator.U.Replacement.WeightReplacementFiniteBound

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

def rectangularCompleteReplacementError (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) : ℂ :=
  ∫ t : ℝ, rectangularFullAFEIntegrand T σ f g Φ t-
    rectangularVStarAFEIntegrand T σ f g Φ t

theorem rectangularCompleteReplacementError_eq_moment_difference
    (T : ℝ) (σ : MomentShifts) (f g Φ : ℝ→ℝ)
    (hΓ : Integrable (rectangularFullAFEIntegrand T σ f g Φ))
    (hV : Integrable (rectangularVStarAFEIntegrand T σ f g Φ)) :
    rectangularCompleteReplacementError T σ f g Φ=
      rectangularFullAFEMoment T σ f g Φ-rectangularVStarAFEMoment T σ f g Φ := by
  exact integral_sub hΓ hV

theorem rectangularCompleteReplacementError_uniform_power_bound
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      Integrable (rectangularFullAFEIntegrand T σ f g Φ) ∧
      Integrable (rectangularVStarAFEIntegrand T σ f g Φ) ∧
      Integrable (fun t : ℝ => rectangularFullAFEIntegrand T σ f g Φ t-
        rectangularVStarAFEIntegrand T σ f g Φ t) ∧
      ‖rectangularCompleteReplacementError T σ f g Φ‖≤
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
  obtain ⟨A,hA,haT⟩ := rectangularFullAFEMoment_uniform_finite_small_error
    hc hc1 hη zero_lt_one K hK δ hδ hroot a b f g Φ hf hg hΦ 0
  obtain ⟨D,hD,hdT⟩ := rectangularVStarAFEMoment_uniform_finite_small_error
    hc hc1 hη zero_lt_one K hK δ hδ hroot a b f g Φ hf hg hΦ 0
  obtain ⟨C,hC,hcT⟩ := a03_actual_weight_replacement_rectangular_contour_uniform_power_bound
    hf hg hΦ ha hab hrect hδ hR
  refine ⟨A+C+D,by positivity,?_⟩
  filter_upwards [haT,hdT,hcT,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T haT hdT hcT hsmall hT
  intro σ hσ
  obtain ⟨hiΓ,hiΓfin,hΓb⟩ := haT σ hσ
  obtain ⟨hiV,hiVfin,hVb⟩ := hdT σ hσ
  simp only [neg_zero,Real.rpow_zero,mul_one] at hΓb hVb
  refine ⟨hiΓ,hiV,hiΓ.sub hiV,?_⟩
  have he := rectangularFiniteSmallGaussianGridMoment_sub_VStar_eq_contours
    hc hT a b f g Φ hf hg hΦ σ (hsmall σ hσ) (s/16) 1
  simp only [one_mul] at he
  have hcont := hcT σ (hσR σ hσ) (hroot σ hσ) 0 1
  have hfin : ‖rectangularFiniteSmallGaussianGridMoment (s/128) T σ f g Φ
      (T^(2+s/16)) (Real.log T)-
      rectangularFiniteSmallVStarMoment (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T)‖≤
      C*T^(rectangularFirstExponent a b s) := by
    rw [he]
    exact (norm_add_le _ _).trans (by simpa [bblrSixShifts] using hcont)
  rw [rectangularCompleteReplacementError_eq_moment_difference T σ f g Φ hiΓ hiV]
  have htq : 1≤T^(rectangularFirstExponent a b s) := Real.one_le_rpow hT.le hq
  have htail : A+D≤(A+D)*T^(rectangularFirstExponent a b s) :=
    le_mul_of_one_le_right (add_nonneg hA hD) htq
  have halg : rectangularFullAFEMoment T σ f g Φ-rectangularVStarAFEMoment T σ f g Φ=
      (rectangularFullAFEMoment T σ f g Φ-
        rectangularFiniteSmallGaussianGridMoment (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T))+
      (rectangularFiniteSmallGaussianGridMoment (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T)-
        rectangularFiniteSmallVStarMoment (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T))+
      (rectangularFiniteSmallVStarMoment (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T)-
        rectangularVStarAFEMoment T σ f g Φ) := by ring
  rw [halg]
  have hVb' : ‖rectangularFiniteSmallVStarMoment (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T)-
      rectangularVStarAFEMoment T σ f g Φ‖≤D := by simpa only [norm_sub_rev,one_mul] using hVb
  have hΓb' : ‖rectangularFullAFEMoment T σ f g Φ-
      rectangularFiniteSmallGaussianGridMoment (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T)‖≤A := by
    simpa only [one_mul] using hΓb
  calc
    _≤(‖rectangularFullAFEMoment T σ f g Φ-
        rectangularFiniteSmallGaussianGridMoment (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T)‖+
      ‖rectangularFiniteSmallGaussianGridMoment (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T)-
        rectangularFiniteSmallVStarMoment (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T)‖)+
      ‖rectangularFiniteSmallVStarMoment (s/128) T σ f g Φ (T^(2+s/16)) (Real.log T)-
        rectangularVStarAFEMoment T σ f g Φ‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _≤A+C*T^(rectangularFirstExponent a b s)+D := by gcongr
    _≤(A+C+D)*T^(rectangularFirstExponent a b s) := by nlinarith [htail]

theorem rectangularCompleteReplacementError_uniform_oT
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      ‖rectangularCompleteReplacementError T σ f g Φ‖≤ε*T := by
  obtain ⟨C,hC,hb⟩ := rectangularCompleteReplacementError_uniform_power_bound
    ha hab hrect K hK δ hδ hroot f g Φ hf hg hΦ
  have hs := rectangular_slack_bounds hab hrect
  have hq : rectangularFirstExponent a b (rectangularSlack a b)<1 := by linarith [hs.1,hs.2.1]
  have ho := (rpow_isLittleO_id_of_lt_one hq).const_mul_left C
  intro ε hε
  filter_upwards [hb,ho.bound hε,eventually_gt_atTop (0:ℝ)] with T hb ho hT
  intro σ hσ
  exact (hb σ hσ).2.2.2.trans (by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hT.le _)),
      abs_of_pos hT] using ho)

end
end Sechstmoment
