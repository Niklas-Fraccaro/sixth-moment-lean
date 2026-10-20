import Mathlib.Analysis.Normed.Group.Bounded
import Sechstmoment.Denominator.Balanced.SharpLogCutoff


namespace Sechstmoment
open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 0

def d02FourProfileProduct (ρ : Fin 4 → ℝ → ℂ) (y : D01LogSpace) : ℂ :=
  ρ 0 (y.1 1) * ρ 1 (y.1 2) * ρ 2 (y.2 1) * ρ 3 (y.2 2)

theorem d02FourProfileProduct_continuous (ρ : Fin 4 → ℝ → ℂ)
    (hρ : ∀ k, Continuous (ρ k)) : Continuous (d02FourProfileProduct ρ) := by
  unfold d02FourProfileProduct
  fun_prop

private def d02ZetaLocalization (t : ℝ) : ℝ :=
  max 0 (min 1 (t+1)) * max 0 (min 1 (2-t))

private theorem d02ZetaLocalization_continuous : Continuous d02ZetaLocalization := by
  unfold d02ZetaLocalization
  fun_prop

private theorem d02ZetaLocalization_eq_one {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    d02ZetaLocalization t = 1 := by
  have h₁ : (1:ℝ) ≤ t+1 := by linarith [ht.1]
  have h₂ : (1:ℝ) ≤ 2-t := by linarith [ht.2]
  simp [d02ZetaLocalization, min_eq_left h₁, min_eq_left h₂]

private theorem d02ZetaLocalization_support {t : ℝ}
    (ht : d02ZetaLocalization t ≠ 0) : t ∈ Icc (-1:ℝ) 2 := by
  constructor
  · by_contra h
    have h₀ : min (1:ℝ) (t+1) ≤ 0 := by
      exact (min_le_right _ _).trans (by linarith)
    exact ht (by simp [d02ZetaLocalization, max_eq_left h₀])
  · by_contra h
    have h₀ : min (1:ℝ) (2-t) ≤ 0 := by
      exact (min_le_right _ _).trans (by linarith)
    exact ht (by simp [d02ZetaLocalization, max_eq_left h₀])

def d02LocalizedFourProfile (ρ : Fin 4 → ℝ → ℂ) (y : D01LogSpace) : ℂ :=
  (d02ZetaLocalization (y.1 0) : ℂ) *
    (d02ZetaLocalization (y.2 0) : ℂ) * d02FourProfileProduct ρ y

theorem d02LocalizedFourProfile_continuous (ρ : Fin 4 → ℝ → ℂ)
    (hρ : ∀ k, Continuous (ρ k)) : Continuous (d02LocalizedFourProfile ρ) := by
  have hleft : Continuous (fun y : D01LogSpace => d02ZetaLocalization (y.1 0)) :=
    d02ZetaLocalization_continuous.comp ((continuous_apply 0).comp continuous_fst)
  have hright : Continuous (fun y : D01LogSpace => d02ZetaLocalization (y.2 0)) :=
    d02ZetaLocalization_continuous.comp ((continuous_apply 0).comp continuous_snd)
  exact ((Complex.continuous_ofReal.comp hleft).mul
    (Complex.continuous_ofReal.comp hright)).mul (d02FourProfileProduct_continuous ρ hρ)

theorem d02LocalizedFourProfile_compact_support
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ)
    (hρ : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k)) :
    HasCompactSupport (d02LocalizedFourProfile ρ) := by
  let lo : D01LogSpace := (![-1,0,0], ![-1,0,0])
  let hi : D01LogSpace := (![2,a 0,a 1], ![2,a 2,a 3])
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := lo) (b := hi))
  intro y hy
  change d02LocalizedFourProfile ρ y ≠ 0 at hy
  have hb₁ : d02ZetaLocalization (y.1 0) ≠ 0 := by
    intro h
    exact hy (by simp [d02LocalizedFourProfile, h])
  have hb₂ : d02ZetaLocalization (y.2 0) ≠ 0 := by
    intro h
    exact hy (by simp [d02LocalizedFourProfile, h])
  have h₀ : ρ 0 (y.1 1) ≠ 0 := by
    intro h
    exact hy (by simp [d02LocalizedFourProfile, d02FourProfileProduct, h])
  have h₁ : ρ 1 (y.1 2) ≠ 0 := by
    intro h
    exact hy (by simp [d02LocalizedFourProfile, d02FourProfileProduct, h])
  have h₂ : ρ 2 (y.2 1) ≠ 0 := by
    intro h
    exact hy (by simp [d02LocalizedFourProfile, d02FourProfileProduct, h])
  have h₃ : ρ 3 (y.2 2) ≠ 0 := by
    intro h
    exact hy (by simp [d02LocalizedFourProfile, d02FourProfileProduct, h])
  have hz₁ := d02ZetaLocalization_support hb₁
  have hz₂ := d02ZetaLocalization_support hb₂
  have hp₀ := hρ 0 _ h₀
  have hp₁ := hρ 1 _ h₁
  have hp₂ := hρ 2 _ h₂
  have hp₃ := hρ 3 _ h₃
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro i
    fin_cases i <;> simp [lo] <;> linarith [hz₁.1, hp₀.1, hp₁.1]
  · intro i
    fin_cases i <;> simp [lo] <;> linarith [hz₂.1, hp₂.1, hp₃.1]
  · intro i
    fin_cases i <;> simp [hi] <;> linarith [hz₁.2, hp₀.2, hp₁.2]
  · intro i
    fin_cases i <;> simp [hi] <;> linarith [hz₂.2, hp₂.2, hp₃.2]

theorem d02SharpLogTest_localizedFourProfile_eq
    (ρ : Fin 4 → ℝ → ℂ) {y : D01LogSpace} (hy : y ∈ d01PositiveOrthant) :
    d02SharpLogTest (d02LocalizedFourProfile ρ) y =
      d02SharpLogTest (d02FourProfileProduct ρ) y := by
  by_cases hcut : y ∈ d02SharpLogRegion
  · have hc : y.1 0+y.2 0 ≤ 1 := hcut
    have h₁ : y.1 0 ∈ Icc (0:ℝ) 1 := ⟨hy.1 0, by linarith [hy.2 0]⟩
    have h₂ : y.2 0 ∈ Icc (0:ℝ) 1 := ⟨hy.2 0, by linarith [hy.1 0]⟩
    simp [d02SharpLogTest, indicator_of_mem hcut, d02LocalizedFourProfile,
      d02ZetaLocalization_eq_one h₁, d02ZetaLocalization_eq_one h₂]
  · simp [d02SharpLogTest, indicator_of_notMem hcut]

theorem d02DiagonalMeasure_four_profile_sharp_log_limit
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (w : D01LogSpace → ℂ)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k))
    (hw : Continuous w) :
    Tendsto (fun L : ℝ => ∫ y,
      w y * d02SharpLogTest (d02FourProfileProduct ρ) y ∂d01DiagonalMeasure L) atTop
      (𝓝 ((arithmeticFactor : ℂ) * ∫ x : D01EdgeSpace,
        w (d01RowColumnSums x) *
          d02SharpLogTest (d02FourProfileProduct ρ) (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) := by
  have hfc := d02LocalizedFourProfile_continuous ρ hρc
  have hK := d02LocalizedFourProfile_compact_support ρ a hρcap
  obtain ⟨C, hbound⟩ := hK.exists_bound_of_continuous hfc
  have hlim := d02DiagonalMeasure_complex_weighted_sharp_log_limit
    (d02LocalizedFourProfile ρ) w hfc hK hbound hw
  have hright : (∫ x : D01EdgeSpace,
      w (d01RowColumnSums x) *
        d02SharpLogTest (d02LocalizedFourProfile ρ) (d01RowColumnSums x)
          ∂volume.restrict d01NonnegativeOrthant) =
      ∫ x : D01EdgeSpace, w (d01RowColumnSums x) *
        d02SharpLogTest (d02FourProfileProduct ρ) (d01RowColumnSums x)
          ∂volume.restrict d01NonnegativeOrthant := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem d01NonnegativeOrthant_measurable] with x hx
    rw [d02SharpLogTest_localizedFourProfile_eq ρ (d01RowColumnSums_nonnegative hx)]
  rw [hright] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  apply integral_congr_ae
  filter_upwards [d01DiagonalMeasure_ae_orthant hL] with y hy
  rw [d02SharpLogTest_localizedFourProfile_eq ρ hy]

theorem d02DiagonalMeasure_four_profile_shifted_sharp_log_height_limit
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (ab : PolarShiftSpace)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k)) :
    Tendsto (fun T : ℝ => ∫ y,
      d01ComplexLaplaceWeight ab y *
        d02SharpLogTest (d02FourProfileProduct ρ) y
          ∂d01DiagonalMeasure (Real.log T)) atTop
      (𝓝 ((arithmeticFactor : ℂ) * ∫ x : D01EdgeSpace,
        d01ComplexLaplaceWeight ab (d01RowColumnSums x) *
          d02SharpLogTest (d02FourProfileProduct ρ) (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) :=
  (d02DiagonalMeasure_four_profile_sharp_log_limit ρ a (d01ComplexLaplaceWeight ab)
    hρc hρcap (d01ComplexLaplaceWeight_continuous ab)).comp Real.tendsto_log_atTop

theorem d02FourProfile_sharp_diagonal_tsum (ρ : Fin 4 → ℝ → ℂ)
    (w : D01LogSpace → ℂ) {L : ℝ} (hL : 0 < L) :
    (∫ y, w y * d02SharpLogTest (d02FourProfileProduct ρ) y
      ∂d01DiagonalMeasure L) =
      ∑' x : DiagonalSixIndices, d01AtomicWeight L x •
        (w (d01LogPoint L x) *
          if (d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ) ≤ Real.exp L
          then d02FourProfileProduct ρ (d01LogPoint L x) else 0) := by
  classical
  rw [d01DiagonalMeasure_integral hL.le]
  apply tsum_congr
  intro x
  congr 2
  rw [d02SharpLogTest, Set.indicator_apply, d02SharpLogRegion_logPoint_iff hL]

theorem d02FourProfile_shifted_sharp_diagonal_tsum_limit
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (ab : PolarShiftSpace)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t ≠ 0 → t ∈ Icc 0 (a k)) :
    Tendsto (fun L : ℝ => ∑' x : DiagonalSixIndices, d01AtomicWeight L x •
      (d01ComplexLaplaceWeight ab (d01LogPoint L x) *
        if (d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ) ≤ Real.exp L
        then d02FourProfileProduct ρ (d01LogPoint L x) else 0)) atTop
      (𝓝 ((arithmeticFactor : ℂ) * ∫ x : D01EdgeSpace,
        d01ComplexLaplaceWeight ab (d01RowColumnSums x) *
          d02SharpLogTest (d02FourProfileProduct ρ) (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) := by
  have h := d02DiagonalMeasure_four_profile_sharp_log_limit ρ a
    (d01ComplexLaplaceWeight ab) hρc hρcap (d01ComplexLaplaceWeight_continuous ab)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  exact d02FourProfile_sharp_diagonal_tsum ρ (d01ComplexLaplaceWeight ab) hL

end
end Sechstmoment
