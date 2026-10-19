import Sechstmoment.Analysis.Gaussian.Weight
import Sechstmoment.Denominator.Balanced.SharpLogCutoff

/-! Continuous shrinking band majorants and uniform bounded-offset estimates
for the moving Gaussian cutoff. -/
namespace Sechstmoment
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 0

/-- Continuous majorant of the band of width `1/(n+1)` around the cut. -/
def d02CutBandMajorant (n : ℕ) (q : ℝ) : ℝ :=
  max 0 (min 1 (2-((n:ℝ)+1)*|q-1|))

theorem d02CutBandMajorant_continuous (n : ℕ) :
    Continuous (d02CutBandMajorant n) := by
  unfold d02CutBandMajorant
  fun_prop

theorem d02CutBandMajorant_nonneg (n : ℕ) (q : ℝ) :
    0 ≤ d02CutBandMajorant n q := le_max_left _ _

theorem d02CutBandMajorant_le_one (n : ℕ) (q : ℝ) :
    d02CutBandMajorant n q ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

theorem d02CutBandMajorant_eq_one {n : ℕ} {q : ℝ}
    (hq : |q-1| ≤ 1/((n:ℝ)+1)) : d02CutBandMajorant n q = 1 := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hm : ((n:ℝ)+1)*|q-1| ≤ 1 := by
    have h := (le_div_iff₀ hn).mp hq
    nlinarith
  have h₂ : (1:ℝ) ≤ 2-((n:ℝ)+1)*|q-1| := by linarith
  simp [d02CutBandMajorant, min_eq_left h₂]

theorem d02CutBandMajorant_tendsto_zero {q : ℝ} (hq : q ≠ 1) :
    Tendsto (fun n : ℕ => d02CutBandMajorant n q) atTop (𝓝 0) := by
  have ha : 0 < |q-1| := abs_pos.mpr (sub_ne_zero.mpr hq)
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)+1)*|q-1|) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const ha
  apply tendsto_const_nhds.congr'
  filter_upwards [ht.eventually_ge_atTop (2:ℝ)] with n hn
  have h₂ : 2-((n:ℝ)+1)*|q-1| ≤ 0 := by linarith
  have hmin : min (1:ℝ) (2-((n:ℝ)+1)*|q-1|) ≤ 0 :=
    (min_le_right _ _).trans h₂
  exact (max_eq_left hmin).symm

theorem d02GaussianLogWeight_measurable (L c : ℝ) :
    Measurable (fun q => d02GaussianLogWeight L q c) := by
  exact d02GaussianTail_antitone.measurable.comp (by fun_prop)

private theorem d02GaussianLogWeight_minus_cut_abs_le_one (L q c : ℝ) :
    |d02GaussianLogWeight L q c - if q ≤ 1 then 1 else 0| ≤ 1 := by
  have hg0 := d02GaussianTail_nonneg ((L*(q-1)+c)/2)
  have hg1 := d02GaussianTail_le_one ((L*(q-1)+c)/2)
  change 0 ≤ d02GaussianLogWeight L q c at hg0
  change d02GaussianLogWeight L q c ≤ 1 at hg1
  by_cases hq : q ≤ 1
  · simp only [ite_eq_left hq, abs_of_nonpos (sub_nonpos.mpr hg1)]
    linarith
  · simpa only [ite_eq_right hq, sub_zero, abs_of_nonneg hg0] using hg1

theorem d02GaussianLogWeight_uniform_band_bound (n : ℕ) {δ C : ℝ} (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ q c : ℝ, |c| ≤ C →
      |d02GaussianLogWeight L q c - if q ≤ 1 then 1 else 0| ≤
        δ+d02CutBandMajorant n q := by
  have hη : 0 < 1/((n:ℝ)+1) := by positivity
  filter_upwards [d02GaussianLogWeight_uniform_above (C := C) hη hδ,
    d02GaussianLogWeight_uniform_below (C := C) hη hδ] with L habove hbelow
  intro q c hc
  by_cases hband : |q-1| ≤ 1/((n:ℝ)+1)
  · rw [d02CutBandMajorant_eq_one hband]
    exact (d02GaussianLogWeight_minus_cut_abs_le_one L q c).trans (by linarith)
  · have hband' : 1/((n:ℝ)+1) < |q-1| := not_le.mp hband
    have hb0 := d02CutBandMajorant_nonneg n q
    have hg0 := d02GaussianTail_nonneg ((L*(q-1)+c)/2)
    have hg1 := d02GaussianTail_le_one ((L*(q-1)+c)/2)
    change 0 ≤ d02GaussianLogWeight L q c at hg0
    change d02GaussianLogWeight L q c ≤ 1 at hg1
    by_cases hq : q ≤ 1
    · have hqgap : q ≤ 1-1/((n:ℝ)+1) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hq)] at hband'
        linarith
      have h := hbelow q c hqgap hc
      simp only [ite_eq_left hq, abs_of_nonpos (sub_nonpos.mpr hg1)]
      linarith
    · have hqgap : 1+1/((n:ℝ)+1) ≤ q := by
        rw [abs_of_pos (sub_pos.mpr (not_le.mp hq))] at hband'
        linarith
      have h := habove q c hqgap hc
      simp only [ite_eq_right hq, sub_zero, abs_of_nonneg hg0]
      linarith

end
end Sechstmoment
