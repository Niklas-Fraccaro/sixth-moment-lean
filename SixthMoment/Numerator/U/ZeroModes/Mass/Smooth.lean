import SixthMoment.Numerator.U.ZeroModes.Mass.Definitions

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03ZeroMode_masked_inverse_integrable {L : ℝ} (hL : 0<L)
    (W : ℝ→ℝ) (hWm : Measurable W) (hW : ∀ x,0≤W x ∧ W x≤1)
    (hzero : ∀ x,x∉Icc L (2*L) → W x=0) :
    IntegrableOn (fun x : ℝ => W x/x) (Ioi 0) := by
  have hmaj : Integrable ((Icc L (2*L)).indicator (fun x : ℝ => 1/x))
      (volume.restrict (Ioi 0)) :=
    ((integrable_indicator_iff measurableSet_Icc).mpr (a03ZeroMode_dyadic_inverse_integrable hL)).restrict
  apply hmaj.mono' (hWm.div measurable_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  by_cases hs : x∈Icc L (2*L)
  · change ‖W x/x‖≤_
    rw [indicator_of_mem hs,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hW x).1 hx.le)]
    exact div_le_div_of_nonneg_right (hW x).2 hx.le
  · simp [indicator_of_notMem hs,hzero x hs]

theorem a03ZeroMode_masked_inverse_integral_le {L : ℝ} (hL : 0<L)
    (W : ℝ→ℝ) (hWm : Measurable W) (hW : ∀ x,0≤W x ∧ W x≤1)
    (hzero : ∀ x,x∉Icc L (2*L) → W x=0) :
    (∫ x : ℝ in Ioi 0,W x/x)≤Real.log 2 := by
  have hmaj : Integrable ((Icc L (2*L)).indicator (fun x : ℝ => 1/x))
      (volume.restrict (Ioi 0)) :=
    ((integrable_indicator_iff measurableSet_Icc).mpr (a03ZeroMode_dyadic_inverse_integrable hL)).restrict
  have hbound : (fun x : ℝ => W x/x)≤ᵐ[volume.restrict (Ioi 0)]
      (Icc L (2*L)).indicator (fun x : ℝ => 1/x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    by_cases hs : x∈Icc L (2*L)
    · rw [indicator_of_mem hs]
      exact div_le_div_of_nonneg_right (hW x).2 hx.le
    · simp [indicator_of_notMem hs,hzero x hs]
  have hi := integral_mono_ae (a03ZeroMode_masked_inverse_integrable hL W hWm hW hzero) hmaj hbound
  have hsub : Icc L (2*L)⊆Ioi (0:ℝ) := fun x hx => hL.trans_le hx.1
  rwa [integral_indicator measurableSet_Icc,Measure.restrict_restrict_of_subset hsub,
    a03ZeroMode_dyadic_inverse_integral hL] at hi

def a03ZeroModeContinuousSmoothWeight (a b m n d M₂ N₂ x : ℝ) : ℝ :=
  rectangularSmoothBlockWeight (b*n*x/(d*M₂))*rectangularSmoothBlockWeight (a*m*x/(d*N₂))

theorem a03ZeroModeContinuousSmoothWeight_bounds (a b m n d M₂ N₂ x : ℝ) :
    0≤a03ZeroModeContinuousSmoothWeight a b m n d M₂ N₂ x ∧
      a03ZeroModeContinuousSmoothWeight a b m n d M₂ N₂ x≤1 := by
  unfold a03ZeroModeContinuousSmoothWeight
  exact ⟨mul_nonneg (rectangularSmoothBlockWeight_nonneg _) (rectangularSmoothBlockWeight_nonneg _),
    by simpa only [one_mul] using (mul_le_mul (rectangularSmoothBlockWeight_le_one _) (rectangularSmoothBlockWeight_le_one _)
      (rectangularSmoothBlockWeight_nonneg _) (by norm_num : (0:ℝ)≤1))⟩

theorem a03ZeroModeContinuousSmoothWeight_measurable (a b m n d M₂ N₂ : ℝ) :
    Measurable (a03ZeroModeContinuousSmoothWeight a b m n d M₂ N₂) := by
  unfold a03ZeroModeContinuousSmoothWeight
  exact ((rectangularSmoothBlockWeight_contDiff.continuous.comp (by fun_prop)).mul
    (rectangularSmoothBlockWeight_contDiff.continuous.comp (by fun_prop))).measurable

theorem a03ZeroModeContinuousSmoothWeight_zero_outside {a b m n d M₂ N₂ : ℝ}
    (hb : 0<b) (hn : 0<n) (hd : 0<d) (hM₂ : 0<M₂) (x : ℝ)
    (hx : x∉Icc (d*M₂/(b*n)) (2*(d*M₂/(b*n)))) :
    a03ZeroModeContinuousSmoothWeight a b m n d M₂ N₂ x=0 := by
  unfold a03ZeroModeContinuousSmoothWeight
  have hz : rectangularSmoothBlockWeight (b*n*x/(d*M₂))=0 := by
    by_contra hw
    have hs := rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hw)
    have hbnp : 0<b*n := mul_pos hb hn
    have hdp : 0<d*M₂ := mul_pos hd hM₂
    apply hx
    refine ⟨(div_le_iff₀ hbnp).mpr ?_,?_⟩
    · have hlow := (le_div_iff₀ hdp).mp hs.1
      nlinarith only [hlow]
    · have hhigh := (div_le_iff₀ hdp).mp hs.2
      have he : 2*(d*M₂/(b*n))=(2*d*M₂)/(b*n) := by ring
      rw [he]
      apply (le_div_iff₀ hbnp).mpr
      nlinarith only [hhigh]
  rw [hz,zero_mul]

def a03ZeroModeContinuousSmoothMass (a b m n d M₂ N₂ : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 0,a03ZeroModeContinuousSmoothWeight a b m n d M₂ N₂ x*
    a03ZeroModeSixDensity a b m n d x

theorem a03ZeroModeContinuousSmoothMass_integrable {a b m n d M₂ N₂ : ℝ}
    (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) (hd : 0<d) (hM₂ : 0<M₂) :
    IntegrableOn (fun x : ℝ => a03ZeroModeContinuousSmoothWeight a b m n d M₂ N₂ x*
      a03ZeroModeSixDensity a b m n d x) (Ioi 0) := by
  have hL : 0<d*M₂/(b*n) := by positivity
  have hi := (a03ZeroMode_masked_inverse_integrable hL _
    (a03ZeroModeContinuousSmoothWeight_measurable a b m n d M₂ N₂)
    (a03ZeroModeContinuousSmoothWeight_bounds a b m n d M₂ N₂)
    (a03ZeroModeContinuousSmoothWeight_zero_outside hb hn hd hM₂)).const_mul (d/(a*b*m*n))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [a03ZeroModeSixDensity_eq ha hb hm hn hd hx]
  ring

theorem a03ZeroModeContinuousSmoothMass_nonneg (a b m n d M₂ N₂ : ℝ) :
    0≤a03ZeroModeContinuousSmoothMass a b m n d M₂ N₂ := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro x _
  exact mul_nonneg (a03ZeroModeContinuousSmoothWeight_bounds a b m n d M₂ N₂ x).1 (by
    unfold a03ZeroModeSixDensity
    positivity)

theorem a03ZeroModeContinuousSmoothMass_le {a b m n d M₂ N₂ : ℝ}
    (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) (hd : 0<d) (hM₂ : 0<M₂) :
    a03ZeroModeContinuousSmoothMass a b m n d M₂ N₂≤d/(a*b*m*n)*Real.log 2 := by
  have hL : 0<d*M₂/(b*n) := by positivity
  have hweight := a03ZeroMode_masked_inverse_integral_le hL _
    (a03ZeroModeContinuousSmoothWeight_measurable a b m n d M₂ N₂)
    (a03ZeroModeContinuousSmoothWeight_bounds a b m n d M₂ N₂)
    (a03ZeroModeContinuousSmoothWeight_zero_outside hb hn hd hM₂)
  have he : a03ZeroModeContinuousSmoothMass a b m n d M₂ N₂=
      (d/(a*b*m*n))*∫ x : ℝ in Ioi 0,a03ZeroModeContinuousSmoothWeight a b m n d M₂ N₂ x/x := by
    unfold a03ZeroModeContinuousSmoothMass
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [a03ZeroModeSixDensity_eq ha hb hm hn hd hx]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hweight (by positivity)

def a03ZeroModeLiteralPairMass (a b m n d H M₁ M₂ N₁ N₂ : ℝ) : ℝ :=
  a03ZeroModeGapWeightSum d H*rectangularSmoothBlockWeight (m/M₁)*
    rectangularSmoothBlockWeight (n/N₁)*a03ZeroModeContinuousSmoothMass a b m n d M₂ N₂

theorem a03ZeroModeLiteralPairMass_nonneg (a b m n d H M₁ M₂ N₁ N₂ : ℝ) :
    0≤a03ZeroModeLiteralPairMass a b m n d H M₁ M₂ N₁ N₂ := by
  unfold a03ZeroModeLiteralPairMass
  exact mul_nonneg (mul_nonneg (mul_nonneg (a03ZeroModeGapWeightSum_nonneg _ _)
    (rectangularSmoothBlockWeight_nonneg _)) (rectangularSmoothBlockWeight_nonneg _))
      (a03ZeroModeContinuousSmoothMass_nonneg _ _ _ _ _ _ _)

theorem a03ZeroModeLiteralPairMass_le {a b m n d H M₁ M₂ N₁ N₂ : ℝ}
    (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) (hd : 0<d) (hH : 0<H) (hM₂ : 0<M₂) :
    a03ZeroModeLiteralPairMass a b m n d H M₁ M₂ N₁ N₂≤2*H*Real.log 2/(a*b*m*n) := by
  have hfirst : a03ZeroModeGapWeightSum d H*rectangularSmoothBlockWeight (m/M₁)*
      rectangularSmoothBlockWeight (n/N₁)≤a03ZeroModeGapWeightSum d H := by
    calc
      _=a03ZeroModeGapWeightSum d H*(rectangularSmoothBlockWeight (m/M₁)*rectangularSmoothBlockWeight (n/N₁)) := by ring
      _≤a03ZeroModeGapWeightSum d H*1 := mul_le_mul_of_nonneg_left
        (by simpa only [one_mul] using (mul_le_mul (rectangularSmoothBlockWeight_le_one (m/M₁))
          (rectangularSmoothBlockWeight_le_one (n/N₁)) (rectangularSmoothBlockWeight_nonneg _) (by norm_num : (0:ℝ)≤1)))
        (a03ZeroModeGapWeightSum_nonneg _ _)
      _=_ := mul_one _
  unfold a03ZeroModeLiteralPairMass
  calc
    _≤a03ZeroModeGapWeightSum d H*(d/(a*b*m*n)*Real.log 2) :=
      mul_le_mul hfirst (a03ZeroModeContinuousSmoothMass_le ha hb hm hn hd hM₂)
        (a03ZeroModeContinuousSmoothMass_nonneg _ _ _ _ _ _ _) (a03ZeroModeGapWeightSum_nonneg _ _)
    _≤(2*H/d)*(d/(a*b*m*n)*Real.log 2) :=
      mul_le_mul_of_nonneg_right (a03ZeroModeGapWeightSum_le hd hH) (by positivity)
    _=_ := by field_simp

end
end SixthMoment
