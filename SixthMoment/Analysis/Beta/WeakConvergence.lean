import Mathlib.Analysis.Normed.Group.Bounded
import SixthMoment.Analysis.Beta.Concentration

namespace SixthMoment

open Filter MeasureTheory

theorem betaScaled_test_error_bound {η : ℝ} (hη : 0 < η) {n k : ℕ} (hk : k ≤ n)
    (g : ℝ → ℝ) (a ε M δ : ℝ) (hε : 0 ≤ ε)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) η))
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) η, |g x - g a| ≤ M)
    (hnear : ∀ x ∈ Set.Icc (0 : ℝ) η, |x - a| < δ → |g x - g a| ≤ ε) :
    |(∫ x in (0 : ℝ)..η, g x * betaScaledProfile η n k x) - g a| ≤
      ε + M * betaScaledTailMass η n k a δ := by
  have hp : ContinuousOn (betaScaledProfile η n k) (Set.Icc (0 : ℝ) η) :=
    (betaScaled_continuous η n k).continuousOn
  have hgp : IntervalIntegrable (fun x : ℝ => g x * betaScaledProfile η n k x)
      volume (0 : ℝ) η := (hg.mul hp).intervalIntegrable_of_Icc hη.le
  have hcp : IntervalIntegrable (fun x : ℝ => g a * betaScaledProfile η n k x)
      volume (0 : ℝ) η := (continuous_const.mul (betaScaled_continuous η n k)).intervalIntegrable 0 η
  have hid : (∫ x in (0 : ℝ)..η, g x * betaScaledProfile η n k x) - g a =
      ∫ x in (0 : ℝ)..η, (g x - g a) * betaScaledProfile η n k x := by
    have he (x : ℝ) : (g x - g a) * betaScaledProfile η n k x =
        g x * betaScaledProfile η n k x - g a * betaScaledProfile η n k x := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_sub hgp hcp, intervalIntegral.integral_const_mul,
      betaScaled_mass hη.ne' hk]
    ring
  have hs : MeasurableSet {x : ℝ | δ ≤ |x - a|} :=
    (isClosed_le continuous_const ((continuous_id.sub continuous_const).abs)).measurableSet
  have hi : IntervalIntegrable (betaScaledProfile η n k) volume (0 : ℝ) η :=
    (betaScaled_continuous η n k).intervalIntegrable 0 η
  have ht : IntervalIntegrable
      ({x : ℝ | δ ≤ |x - a|}.indicator (betaScaledProfile η n k)) volume (0 : ℝ) η :=
    ⟨hi.1.indicator hs, hi.2.indicator hs⟩
  have hεp := hi.const_mul ε
  have hMt := ht.const_mul M
  have habs : IntervalIntegrable (fun x : ℝ => |(g x - g a) * betaScaledProfile η n k x|)
      volume (0 : ℝ) η := ((hg.sub continuousOn_const).mul hp).abs.intervalIntegrable_of_Icc hη.le
  rw [hid]
  calc
    _ ≤ ∫ x in (0 : ℝ)..η, |(g x - g a) * betaScaledProfile η n k x| :=
      intervalIntegral.abs_integral_le_integral_abs hη.le
    _ ≤ ∫ x in (0 : ℝ)..η, ε * betaScaledProfile η n k x +
        M * {x : ℝ | δ ≤ |x - a|}.indicator (betaScaledProfile η n k) x := by
      apply intervalIntegral.integral_mono_on hη.le habs (hεp.add hMt)
      intro x hx
      have hp0 := betaScaled_nonneg hη n k hx
      rw [abs_mul, abs_of_nonneg hp0]
      by_cases h : x ∈ {x : ℝ | δ ≤ |x - a|}
      · rw [Set.indicator_of_mem h]
        exact (mul_le_mul_of_nonneg_right (hbound x hx) hp0).trans
          (le_add_of_nonneg_left (mul_nonneg hε hp0))
      · rw [Set.indicator_of_notMem h, mul_zero, add_zero]
        have hxδ : |x - a| < δ := lt_of_not_ge h
        exact mul_le_mul_of_nonneg_right (hnear x hx hxδ) hp0
    _ = ε + M * betaScaledTailMass η n k a δ := by
      rw [intervalIntegral.integral_add hεp hMt, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, betaScaled_mass hη.ne' hk]
      simp only [mul_one, betaScaledTailMass]

theorem betaProfile_continuous_test_tendsto {η a : ℝ} (hη : 0 < η)
    (ha : 0 ≤ a) (haη : a ≤ η) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) η)) :
    Tendsto (fun n : ℕ =>
      ∫ x in (0 : ℝ)..η, g x * betaScaledProfile η n (betaProfileIndex η a n) x)
      atTop (nhds (g a)) := by
  have hamem : a ∈ Set.Icc (0 : ℝ) η := ⟨ha, haη⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.sub continuousOn_const)
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) η, |g x - g a| ≤ M := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using hM
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hlocal⟩ := Metric.continuousWithinAt_iff.mp (hg a hamem) (ε / 2) (half_pos hε)
  have hmul : Tendsto
      (fun n : ℕ => M * betaScaledTailMass η n (betaProfileIndex η a n) a δ)
      atTop (nhds 0) := by
    simpa only [mul_zero] using (betaProfile_tail_tendsto_zero hη ha haη hδ).const_mul M
  have hevent : ∀ᶠ n : ℕ in atTop,
      M * betaScaledTailMass η n (betaProfileIndex η a n) a δ < ε / 2 :=
    (tendsto_order.mp hmul).2 (ε / 2) (half_pos hε)
  filter_upwards [hevent] with n hn
  rw [Real.dist_eq]
  have hb := betaScaled_test_error_bound hη (betaProfileIndex_le hη ha haη n)
    g a (ε / 2) M δ (half_pos hε).le hg hbound (by
      intro x hx hxδ
      simpa only [Real.dist_eq] using (hlocal hx (by simpa only [Real.dist_eq] using hxδ)).le)
  linarith

end SixthMoment
