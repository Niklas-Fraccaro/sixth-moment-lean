import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Sechstmoment.Analysis.Beta.Profiles

namespace Sechstmoment

open Filter

noncomputable def betaScaledProfile (η : ℝ) (n k : ℕ) (x : ℝ) : ℝ :=
  η⁻¹ * betaUnitProfile n k (x / η)

noncomputable def betaProfileIndex (η a : ℝ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) * a / η⌋₊

noncomputable def betaScaledTailMass (η : ℝ) (n k : ℕ) (a δ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..η,
    {x : ℝ | δ ≤ |x - a|}.indicator (betaScaledProfile η n k) x

theorem betaUnit_nonneg (n k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ betaUnitProfile n k x := by
  unfold betaUnitProfile
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (pow_nonneg hx.1 _)) (pow_nonneg (sub_nonneg.mpr hx.2) _)

theorem betaUnit_zero_left {n k : ℕ} (hk : 0 < k) :
    betaUnitProfile n k 0 = 0 := by
  simp [betaUnitProfile, zero_pow (Nat.ne_of_gt hk)]

theorem betaUnit_zero_right {n k : ℕ} (hk : k < n) :
    betaUnitProfile n k 1 = 0 := by
  simp [betaUnitProfile, zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hk))]

theorem betaScaled_nonneg {η : ℝ} (hη : 0 < η) (n k : ℕ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) η) :
    0 ≤ betaScaledProfile η n k x := by
  unfold betaScaledProfile
  apply mul_nonneg (inv_nonneg.mpr hη.le)
  apply betaUnit_nonneg
  constructor
  · exact div_nonneg hx.1 hη.le
  · exact (div_le_one hη).mpr hx.2

theorem betaScaled_zero_left {η : ℝ} {n k : ℕ} (hk : 0 < k) :
    betaScaledProfile η n k 0 = 0 := by
  simp [betaScaledProfile, betaUnit_zero_left hk]

theorem betaScaled_zero_right {η : ℝ} (hη : η ≠ 0) {n k : ℕ} (hk : k < n) :
    betaScaledProfile η n k η = 0 := by
  simp [betaScaledProfile, hη, betaUnit_zero_right hk]

theorem betaScaled_integral {η : ℝ} (hη : η ≠ 0) (n k : ℕ) (g : ℝ → ℝ) :
    (∫ x in (0 : ℝ)..η, g x * betaScaledProfile η n k x) =
      ∫ u in (0 : ℝ)..1, g (η * u) * betaUnitProfile n k u := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1)
    (f := fun x : ℝ => g x * betaScaledProfile η n k x) η
  simp only [mul_zero, mul_one] at h
  rw [← h]
  have he (u : ℝ) : g (η * u) * betaScaledProfile η n k (η * u) =
      η⁻¹ * (g (η * u) * betaUnitProfile n k u) := by
    unfold betaScaledProfile
    rw [mul_div_cancel_left₀ u hη]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hη, one_mul]

theorem betaScaled_mass {η : ℝ} (hη : η ≠ 0) {n k : ℕ} (hk : k ≤ n) :
    (∫ x in (0 : ℝ)..η, betaScaledProfile η n k x) = 1 := by
  have h := betaScaled_integral hη n k (fun _ => 1)
  simpa only [one_mul, betaUnit_mass hk] using h

theorem betaScaled_mean {η : ℝ} (hη : η ≠ 0) {n k : ℕ} (hk : k ≤ n) :
    (∫ x in (0 : ℝ)..η, x * betaScaledProfile η n k x) =
      η * ((k + 1 : ℝ) / (n + 2)) := by
  rw [betaScaled_integral hη]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul, betaUnit_mean hk]

theorem betaScaled_continuous (η : ℝ) (n k : ℕ) :
    Continuous (betaScaledProfile η n k) := by
  unfold betaScaledProfile betaUnitProfile
  fun_prop

theorem betaScaled_second_moment {η : ℝ} (hη : η ≠ 0) {n k : ℕ} (hk : k ≤ n) :
    (∫ x in (0 : ℝ)..η, x ^ 2 * betaScaledProfile η n k x) =
      η ^ 2 * ((k + 1 : ℝ) * (k + 2) / ((n + 2) * (n + 3))) := by
  rw [betaScaled_integral hη]
  have he (u : ℝ) : (η * u) ^ 2 * betaUnitProfile n k u =
      η ^ 2 * (u ^ 2 * betaUnitProfile n k u) := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, betaUnit_second_moment hk]

theorem betaScaled_variance {η : ℝ} (hη : η ≠ 0) {n k : ℕ} (hk : k ≤ n) :
    (∫ x in (0 : ℝ)..η,
      (x - η * ((k + 1 : ℝ) / (n + 2))) ^ 2 * betaScaledProfile η n k x) =
      η ^ 2 * (((k : ℝ) + 1) * (((n - k : ℕ) : ℝ) + 1) /
        (((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3))) := by
  rw [betaScaled_integral hη]
  have he (u : ℝ) :
      (η * u - η * ((k + 1 : ℝ) / (n + 2))) ^ 2 * betaUnitProfile n k u =
      η ^ 2 * ((u - ((k + 1 : ℝ) / (n + 2))) ^ 2 * betaUnitProfile n k u) := by
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, betaUnit_variance hk]

theorem betaScaled_variance_bound {η : ℝ} (hη : η ≠ 0) {n k : ℕ} (hk : k ≤ n) :
    (∫ x in (0 : ℝ)..η,
      (x - η * ((k + 1 : ℝ) / (n + 2))) ^ 2 * betaScaledProfile η n k x) ≤
      η ^ 2 / (4 * ((n : ℝ) + 3)) := by
  rw [betaScaled_variance hη hk]
  calc
    _ ≤ η ^ 2 * (1 / (4 * ((n : ℝ) + 3))) :=
      mul_le_mul_of_nonneg_left (betaUnit_variance_bound hk) (sq_nonneg η)
    _ = _ := by ring

theorem betaScaled_target_second_moment {η : ℝ} (hη : η ≠ 0)
    {n k : ℕ} (hk : k ≤ n) (a : ℝ) :
    (∫ x in (0 : ℝ)..η, (x - a) ^ 2 * betaScaledProfile η n k x) =
      η ^ 2 * (((k : ℝ) + 1) * (((n - k : ℕ) : ℝ) + 1) /
        (((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3))) +
      (η * ((k + 1 : ℝ) / (n + 2)) - a) ^ 2 := by
  have he (x : ℝ) : (x - a) ^ 2 * betaScaledProfile η n k x =
      x ^ 2 * betaScaledProfile η n k x -
        2 * a * (x * betaScaledProfile η n k x) +
        a ^ 2 * betaScaledProfile η n k x := by ring
  simp_rw [he]
  have h₁ : Continuous (fun x : ℝ => x ^ 2 * betaScaledProfile η n k x) :=
    (continuous_id.pow 2).mul (betaScaled_continuous η n k)
  have h₂ : Continuous (fun x : ℝ => 2 * a * (x * betaScaledProfile η n k x)) :=
    continuous_const.mul (continuous_id.mul (betaScaled_continuous η n k))
  have h₃ : Continuous (fun x : ℝ => a ^ 2 * betaScaledProfile η n k x) :=
    continuous_const.mul (betaScaled_continuous η n k)
  have h₁₂ : Continuous (fun x : ℝ => x ^ 2 * betaScaledProfile η n k x -
      2 * a * (x * betaScaledProfile η n k x)) := by fun_prop
  rw [intervalIntegral.integral_add (h₁₂.intervalIntegrable 0 η)
      (h₃.intervalIntegrable 0 η),
    intervalIntegral.integral_sub (h₁.intervalIntegrable 0 η) (h₂.intervalIntegrable 0 η),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    betaScaled_second_moment hη hk, betaScaled_mean hη hk, betaScaled_mass hη hk]
  rw [← betaUnit_variance_algebra hk]
  ring

theorem betaProfileIndex_le {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (haη : a ≤ η)
    (n : ℕ) : betaProfileIndex η a n ≤ n := by
  have hfloor := Nat.floor_le (show 0 ≤ (n : ℝ) * a / η by positivity)
  have hbound : (n : ℝ) * a / η ≤ n := by
    apply (div_le_iff₀ hη).mpr
    nlinarith [mul_le_mul_of_nonneg_left haη (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact_mod_cast hfloor.trans hbound

theorem betaProfileIndex_lt {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (haη : a < η)
    {n : ℕ} (hn : 0 < n) : betaProfileIndex η a n < n := by
  have hfloor := Nat.floor_le (show 0 ≤ (n : ℝ) * a / η by positivity)
  have hbound : (n : ℝ) * a / η < n := by
    apply (div_lt_iff₀ hη).mpr
    nlinarith [mul_lt_mul_of_pos_left haη (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
  exact_mod_cast hfloor.trans_lt hbound

theorem betaProfileIndex_pos {η a : ℝ} (hη : 0 < η) {n : ℕ}
    (hn : η ≤ (n : ℝ) * a) : 0 < betaProfileIndex η a n := by
  have hone : (1 : ℝ) ≤ (n : ℝ) * a / η := (le_div_iff₀ hη).mpr (by simpa using hn)
  exact Nat.floor_pos.mpr hone

theorem betaProfile_endpoints {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (haη : a < η)
    {n : ℕ} (hn : 0 < n) (hthreshold : η ≤ (n : ℝ) * a) :
    betaScaledProfile η n (betaProfileIndex η a n) 0 = 0 ∧
      betaScaledProfile η n (betaProfileIndex η a n) η = 0 := by
  exact ⟨betaScaled_zero_left (betaProfileIndex_pos hη hthreshold),
    betaScaled_zero_right hη.ne' (betaProfileIndex_lt hη ha haη hn)⟩

theorem betaProfile_mean_error {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (haη : a ≤ η)
    (n : ℕ) :
    |η * ((betaProfileIndex η a n + 1 : ℝ) / (n + 2)) - a| ≤
      2 * η / ((n : ℝ) + 2) := by
  let k := betaProfileIndex η a n
  have hklo : (n : ℝ) * a < η * ((k : ℝ) + 1) := by
    have h := (div_lt_iff₀ hη).mp (Nat.lt_floor_add_one ((n : ℝ) * a / η))
    simpa [k, betaProfileIndex, mul_comm] using h
  have hkup : η * (k : ℝ) ≤ (n : ℝ) * a := by
    have h := (le_div_iff₀ hη).mp
      (Nat.floor_le (show 0 ≤ (n : ℝ) * a / η by positivity))
    simpa [k, betaProfileIndex, mul_comm] using h
  have hn₂ : 0 < (n : ℝ) + 2 := by positivity
  have he : η * (((k : ℝ) + 1) / ((n : ℝ) + 2)) - a =
      (η * ((k : ℝ) + 1) - a * ((n : ℝ) + 2)) / ((n : ℝ) + 2) := by
    field_simp
  change |η * (((k : ℝ) + 1) / ((n : ℝ) + 2)) - a| ≤ _
  rw [he]
  apply abs_le.mpr
  constructor
  · rw [← neg_div]
    apply (div_le_div_iff_of_pos_right hn₂).mpr
    nlinarith
  · apply (div_le_div_iff_of_pos_right hn₂).mpr
    nlinarith

theorem betaProfile_target_second_moment_bound {η a : ℝ} (hη : 0 < η)
    (ha : 0 ≤ a) (haη : a ≤ η) (n : ℕ) :
    (∫ x in (0 : ℝ)..η, (x - a) ^ 2 *
      betaScaledProfile η n (betaProfileIndex η a n) x) ≤
      η ^ 2 / (4 * ((n : ℝ) + 3)) + (2 * η / ((n : ℝ) + 2)) ^ 2 := by
  rw [betaScaled_target_second_moment hη.ne' (betaProfileIndex_le hη ha haη n)]
  have hm := betaProfile_mean_error hη ha haη n
  have hs := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ 2 * η / ((n : ℝ) + 2) by positivity)).mpr hm
  rw [sq_abs] at hs
  calc
    _ ≤ η ^ 2 * (1 / (4 * ((n : ℝ) + 3))) + (2 * η / ((n : ℝ) + 2)) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left
        (betaUnit_variance_bound (betaProfileIndex_le hη ha haη n)) (sq_nonneg η)) hs
    _ = _ := by ring

theorem beta_const_div_shift_tendsto_zero (C : ℝ) (s : ℕ) :
    Tendsto (fun n : ℕ => C / ((n : ℝ) + s)) atTop (nhds 0) := by
  simpa only [Nat.cast_add] using
    (tendsto_add_atTop_iff_nat s).mpr (tendsto_const_div_atTop_nhds_zero_nat C)

theorem betaProfile_mean_tendsto {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (haη : a ≤ η) :
    Tendsto (fun n : ℕ => η * ((betaProfileIndex η a n + 1 : ℝ) / (n + 2)))
      atTop (nhds a) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun n : ℕ => |η * ((betaProfileIndex η a n + 1 : ℝ) / (n + 2)) - a|)
    atTop (nhds 0)
  apply squeeze_zero (fun _ => abs_nonneg _) (betaProfile_mean_error hη ha haη)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (tendsto_add_atTop_iff_nat 2).mpr (tendsto_const_div_atTop_nhds_zero_nat (2 * η))

theorem betaProfile_variance_tendsto {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (haη : a ≤ η) :
    Tendsto (fun n : ℕ =>
      ∫ x in (0 : ℝ)..η,
        (x - η * ((betaProfileIndex η a n + 1 : ℝ) / (n + 2))) ^ 2 *
          betaScaledProfile η n (betaProfileIndex η a n) x)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    rw [betaScaled_variance hη.ne' (betaProfileIndex_le hη ha haη n)]
    positivity
  · intro n
    exact betaScaled_variance_bound hη.ne' (betaProfileIndex_le hη ha haη n)
  · have h : Tendsto (fun n : ℕ => (η ^ 2 / 4) / ((n : ℝ) + 3)) atTop (nhds 0) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_add_atTop_iff_nat 3).mpr
          (tendsto_const_div_atTop_nhds_zero_nat (η ^ 2 / 4))
    simpa only [div_div] using h

theorem betaProfile_endpoints_eventually {η a : ℝ} (hη : 0 < η)
    (ha : 0 < a) (haη : a < η) :
    ∀ᶠ n : ℕ in atTop,
      betaScaledProfile η n (betaProfileIndex η a n) 0 = 0 ∧
        betaScaledProfile η n (betaProfileIndex η a n) η = 0 := by
  have hna : Tendsto (fun n : ℕ => (n : ℝ) * a) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const ha
  have hthreshold : ∀ᶠ n : ℕ in atTop, η ≤ (n : ℝ) * a :=
    hna.eventually (eventually_ge_atTop η)
  filter_upwards [hthreshold, eventually_gt_atTop (0 : ℕ)] with n ht hn
  exact betaProfile_endpoints hη ha.le haη hn ht

theorem betaProfile_target_second_moment_tendsto {η a : ℝ} (hη : 0 < η)
    (ha : 0 ≤ a) (haη : a ≤ η) :
    Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..η,
      (x - a) ^ 2 * betaScaledProfile η n (betaProfileIndex η a n) x)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    apply intervalIntegral.integral_nonneg hη.le
    intro x hx
    exact mul_nonneg (sq_nonneg (x - a)) (betaScaled_nonneg hη n _ hx)
  · exact betaProfile_target_second_moment_bound hη ha haη
  · have h := (beta_const_div_shift_tendsto_zero (η ^ 2 / 4) 3).add
      ((beta_const_div_shift_tendsto_zero (2 * η) 2).pow 2)
    simpa [div_div] using h

theorem betaScaled_tail_nonneg {η : ℝ} (hη : 0 < η) (n k : ℕ) (a δ : ℝ) :
    0 ≤ betaScaledTailMass η n k a δ := by
  unfold betaScaledTailMass
  apply intervalIntegral.integral_nonneg hη.le
  intro x hx
  by_cases h : x ∈ {x : ℝ | δ ≤ |x - a|}
  · rw [Set.indicator_of_mem h]
    exact betaScaled_nonneg hη n k hx
  · rw [Set.indicator_of_notMem h]

theorem betaScaled_tail_le_second_moment {η : ℝ} (hη : 0 < η) (n k : ℕ)
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    betaScaledTailMass η n k a δ ≤
      (∫ x in (0 : ℝ)..η, (x - a) ^ 2 * betaScaledProfile η n k x) / δ ^ 2 := by
  have hs : MeasurableSet {x : ℝ | δ ≤ |x - a|} :=
    (isClosed_le continuous_const ((continuous_id.sub continuous_const).abs)).measurableSet
  have hi : IntervalIntegrable (betaScaledProfile η n k) MeasureTheory.volume (0 : ℝ) η :=
    (betaScaled_continuous η n k).intervalIntegrable (0 : ℝ) η
  have ht : IntervalIntegrable
      ({x : ℝ | δ ≤ |x - a|}.indicator (betaScaledProfile η n k))
      MeasureTheory.volume (0 : ℝ) η := ⟨hi.1.indicator hs, hi.2.indicator hs⟩
  have hc : Continuous (fun x : ℝ => (x - a) ^ 2 * betaScaledProfile η n k x) :=
    ((continuous_id.sub continuous_const).pow 2).mul (betaScaled_continuous η n k)
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
  rw [mul_comm _ (δ ^ 2)]
  unfold betaScaledTailMass
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hη.le (ht.const_mul (δ ^ 2))
    (hc.intervalIntegrable 0 η)
  intro x hx
  by_cases h : x ∈ {x : ℝ | δ ≤ |x - a|}
  · rw [Set.indicator_of_mem h]
    have hsq : δ ^ 2 ≤ (x - a) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ hδ.le (abs_nonneg (x - a))).mpr h
    exact mul_le_mul_of_nonneg_right hsq (betaScaled_nonneg hη n k hx)
  · rw [Set.indicator_of_notMem h, mul_zero]
    exact mul_nonneg (sq_nonneg (x - a)) (betaScaled_nonneg hη n k hx)

theorem betaProfile_tail_bound {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (haη : a ≤ η)
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    betaScaledTailMass η n (betaProfileIndex η a n) a δ ≤
      (η ^ 2 / (4 * ((n : ℝ) + 3)) + (2 * η / ((n : ℝ) + 2)) ^ 2) / δ ^ 2 := by
  exact (betaScaled_tail_le_second_moment hη n _ a hδ).trans
    ((div_le_div_iff_of_pos_right (sq_pos_of_pos hδ)).mpr
      (betaProfile_target_second_moment_bound hη ha haη n))

theorem betaProfile_tail_tendsto_zero {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a)
    (haη : a ≤ η) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => betaScaledTailMass η n (betaProfileIndex η a n) a δ)
      atTop (nhds 0) := by
  apply squeeze_zero (fun n => betaScaled_tail_nonneg hη n _ a δ)
    (fun n => betaScaled_tail_le_second_moment hη n _ a hδ)
  simpa only [zero_div] using
    (betaProfile_target_second_moment_tendsto hη ha haη).div_const (δ ^ 2)

end Sechstmoment
