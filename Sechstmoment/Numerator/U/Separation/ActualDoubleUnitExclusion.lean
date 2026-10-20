import Sechstmoment.Numerator.U.Separation.ShapeActualPowerNear


namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phase_actual_double_m_unit_near_block_excluded
    {a T A B H η : ℝ} (hT : 1 < T) (hA : 0 < A) (hB : 0 < B) (hH : 0 < H)
    (hη0 : 0 ≤ η) (hη : η ≤ 1/2) (hsmall : 4*η*T^a < 1)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f)
    (k : Fin 4 → ℕ) (hk₀ : k 0 = 0) (hk₁ : k 1 = 0) :
    ¬ phaseActualActiveNearBlock T A B H η f g k := by
  intro hactive
  obtain ⟨p,q,h,n,positive,hp,hq,hw,hh,hrel,hnear⟩ := hactive
  obtain ⟨ν,hν,hflen⟩ := phase_actual_nonzero_amplifier_lengths f hf
  have hlength := (hflen T A hT hA p hp).2
  have hsupport := phase_actual_source_tuple_support T A B H f g hA hB hH
    k n p q h hp hq hw hh
  have hpositive := phase_actual_source_tuple_positive T A B H f g hA hB hH
    k n p q h hp hq hw hh
  have hn₀ : n 0 = 0 := by
    by_contra hn
    exact hw (rectangular_AFE_smooth_low_block_zero k n 0 hk₀ hn)
  have hn₁ : n 1 = 0 := by
    by_contra hn
    exact hw (rectangular_AFE_smooth_low_block_zero k n 1 hk₁ hn)
  have hpbound : ((rectangularAFESourceTuple p q n h) 0 : ℝ) ≤ 2*T^a := by
    have hs := (hsupport 0).2
    norm_num [phaseActualScales, QuadraticScales.size] at hs
    exact hs.trans (by linarith)
  apply rectangular_near_double_m_unit_excluded positive
    (rectangularAFESourceTuple p q n h) hη0 hη
    (by nlinarith) (hpositive 0) hpbound (hpositive 6) _ _ hrel hnear
  · simp [rectangularAFESourceTuple,hn₀]
  · simp [rectangularAFESourceTuple,hn₁]

theorem phase_actual_double_n_unit_near_block_excluded
    {b T A B H η : ℝ} (hT : 1 < T) (hA : 0 < A) (hB : 0 < B) (hH : 0 < H)
    (hη0 : 0 ≤ η) (hη : η ≤ 1/2) (hsmall : 4*η*T^b < 1)
    (f g : ℝ → ℝ) (hg : SmoothInteriorProfile b g)
    (k : Fin 4 → ℕ) (hk₂ : k 2 = 0) (hk₃ : k 3 = 0) :
    ¬ phaseActualActiveNearBlock T A B H η f g k := by
  intro hactive
  obtain ⟨p,q,h,n,positive,hp,hq,hw,hh,hrel,hnear⟩ := hactive
  obtain ⟨ν,hν,hglen⟩ := phase_actual_nonzero_amplifier_lengths g hg
  have hlength := (hglen T B hT hB q hq).2
  have hsupport := phase_actual_source_tuple_support T A B H f g hA hB hH
    k n p q h hp hq hw hh
  have hpositive := phase_actual_source_tuple_positive T A B H f g hA hB hH
    k n p q h hp hq hw hh
  have hn₂ : n 2 = 0 := by
    by_contra hn
    exact hw (rectangular_AFE_smooth_low_block_zero k n 2 hk₂ hn)
  have hn₃ : n 3 = 0 := by
    by_contra hn
    exact hw (rectangular_AFE_smooth_low_block_zero k n 3 hk₃ hn)
  have hqbound : ((rectangularAFESourceTuple p q n h) 1 : ℝ) ≤ 2*T^b := by
    have hs := (hsupport 1).2
    norm_num [phaseActualScales, QuadraticScales.size] at hs
    exact hs.trans (by linarith)
  apply rectangular_near_double_n_unit_excluded positive
    (rectangularAFESourceTuple p q n h) hη0 hη
    (by nlinarith) (hpositive 1) hqbound (hpositive 6) _ _ hrel hnear
  · simp [rectangularAFESourceTuple,hn₂]
  · simp [rectangularAFESourceTuple,hn₃]

theorem phase_actual_power_near_double_unit_blocks_excluded
    {a b s : ℝ} (hs : s < 1) (hsa : s+a < 1) (hsb : s+b < 1)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0 < A → 0 < B → 0 < H →
      ∀ k : Fin 4 → ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ¬ (k 0 = 0 ∧ k 1 = 0) ∧ ¬ (k 2 = 0 ∧ k 3 = 0) := by
  have hηsmall : ∀ᶠ T : ℝ in atTop, T^(s-1) < 1/2 := by
    have h := ((tendsto_order.1 (tendsto_rpow_neg_atTop
      (show 0 < 1-s by linarith))).2 (1/2) (by norm_num))
    simpa only [neg_sub] using h
  have ha_small : ∀ᶠ T : ℝ in atTop, T^(s-1+a) < 1/4 := by
    have h := ((tendsto_order.1 (tendsto_rpow_neg_atTop
      (show 0 < 1-s-a by linarith))).2 (1/4) (by norm_num))
    simpa only [show -(1-s-a)=s-1+a by ring] using h
  have hb_small : ∀ᶠ T : ℝ in atTop, T^(s-1+b) < 1/4 := by
    have h := ((tendsto_order.1 (tendsto_rpow_neg_atTop
      (show 0 < 1-s-b by linarith))).2 (1/4) (by norm_num))
    simpa only [show -(1-s-b)=s-1+b by ring] using h
  filter_upwards [hηsmall,ha_small,hb_small,eventually_gt_atTop (1 : ℝ)]
    with T hη haT hbT hT
  intro A B H hA hB hH k hactive
  have hTp : 0 < T := zero_lt_one.trans hT
  have hma : 4*T^(s-1)*T^a < 1 := by
    rw [mul_assoc,← Real.rpow_add hTp]
    linarith
  have hmb : 4*T^(s-1)*T^b < 1 := by
    rw [mul_assoc,← Real.rpow_add hTp]
    linarith
  constructor
  · rintro ⟨hk₀,hk₁⟩
    exact phase_actual_double_m_unit_near_block_excluded hT hA hB hH
      (Real.rpow_nonneg hTp.le _) hη.le hma f g hf k hk₀ hk₁ hactive
  · rintro ⟨hk₂,hk₃⟩
    exact phase_actual_double_n_unit_near_block_excluded hT hA hB hH
      (Real.rpow_nonneg hTp.le _) hη.le hmb f g hg k hk₂ hk₃ hactive

theorem phase_actual_source_near_double_unit_blocks_excluded
    {a b s : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hlen : 3*a+5*b < 2)
    (hs : s < 1/2) (f g : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0 < A → 0 < B → 0 < H →
      ∀ k : Fin 4 → ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ¬ (k 0 = 0 ∧ k 1 = 0) ∧ ¬ (k 2 = 0 ∧ k 3 = 0) := by
  exact phase_actual_power_near_double_unit_blocks_excluded (by linarith)
    (by linarith) (by linarith) f g hf hg

end
end Sechstmoment
