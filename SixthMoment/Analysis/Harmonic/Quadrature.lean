import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import SixthMoment.Analysis.Harmonic.Distribution


namespace SixthMoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

theorem cell_quadrature_error {F : ℝ → ℂ} {a b w δ B D : ℝ}
    (hab : a ≤ b) (hw : b-a ≤ w) (hδ : b-a ≤ δ) (hD : 0 ≤ D)
    (hF : ContinuousOn F (Icc a b)) (hFa : ‖F a‖ ≤ B)
    (hLip : ∀ x ∈ Icc a b, ‖F a - F x‖ ≤ D*|a-x|) :
    ‖(w:ℂ)*F a - ∫ x in a..b, F x‖ ≤
      B*(w-(b-a)) + D*δ*(b-a) := by
  have hi : IntervalIntegrable F volume a b := hF.intervalIntegrable_of_Icc hab
  have hconst : IntervalIntegrable (fun _ : ℝ => F a) volume a b := intervalIntegrable_const
  have hid : (w:ℂ)*F a - ∫ x in a..b, F x =
      ((w-(b-a):ℝ):ℂ)*F a + ∫ x in a..b, F a-F x := by
    rw [intervalIntegral.integral_sub hconst hi, intervalIntegral.integral_const]
    simp only [real_smul, Complex.ofReal_sub]
    ring
  have hInt : ‖∫ x in a..b, F a-F x‖ ≤ D*δ*(b-a) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := D*δ) ?_).trans_eq
      (by rw [abs_of_nonneg (sub_nonneg.mpr hab)])
    intro x hx
    rw [uIoc_of_le hab] at hx
    have hax : |a-x| ≤ δ := by rw [abs_of_nonpos (by linarith [hx.1])]; linarith [hx.2]
    exact (hLip x ⟨hx.1.le,hx.2⟩).trans (mul_le_mul_of_nonneg_left hax hD)
  rw [hid]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ w-(b-a))]
  calc
    _ ≤ (w-(b-a))*B + D*δ*(b-a) := add_le_add
      (mul_le_mul_of_nonneg_left hFa (by linarith)) hInt
    _ = _ := by ring

theorem finite_quadrature_error {F : ℝ → ℂ} {grid weight : ℕ → ℝ}
    {N : ℕ} (hN : 1 ≤ N) {a δ B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hfirst : grid 1 = 0)
    (hnodes : ∀ n ∈ Finset.Icc 1 N, grid n ∈ Icc 0 a)
    (hmesh : ∀ n ∈ Finset.Ico 1 N, 0 ≤ grid (n+1)-grid n ∧ grid (n+1)-grid n ≤ δ)
    (hweight : ∀ n ∈ Finset.Ico 1 N, grid (n+1)-grid n ≤ weight n)
    (hmass : (∑ n ∈ Finset.Ico 1 N, (weight n - (grid (n+1) - grid n))) ≤ δ)
    (hlast : 0 ≤ weight N ∧ weight N ≤ δ)
    (htail : 0 ≤ a-grid N ∧ a-grid N ≤ δ)
    (hF : ContinuousOn F (Icc 0 a)) (hbound : ∀ x ∈ Icc 0 a, ‖F x‖ ≤ B)
    (hLip : ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, ‖F x-F y‖ ≤ D*|x-y|) :
    ‖(∑ n ∈ Finset.Icc 1 N, (weight n:ℂ)*F (grid n)) - ∫ x in 0..a, F x‖ ≤
      δ*(3*B+D*a) := by
  have hδ : 0 ≤ δ := hlast.1.trans hlast.2
  have hGN := hnodes N (Finset.right_mem_Icc.mpr hN)
  have hcell (n : ℕ) (hn : n ∈ Finset.Ico 1 N) :
      Icc (grid n) (grid (n+1)) ⊆ Icc 0 a := by
    have hn' : n ∈ Finset.Icc 1 N := by
      have := Finset.mem_Ico.mp hn
      exact Finset.mem_Icc.mpr ⟨this.1,this.2.le⟩
    have hn1 : n+1 ∈ Finset.Icc 1 N := by
      have := Finset.mem_Ico.mp hn
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    exact Icc_subset_Icc (hnodes n hn').1 (hnodes (n+1) hn1).2
  have hi (n : ℕ) (hn : n ∈ Finset.Ico 1 N) :
      IntervalIntegrable F volume (grid n) (grid (n+1)) :=
    (hF.mono (hcell n hn)).intervalIntegrable_of_Icc (by linarith [(hmesh n hn).1])
  have hsumInt : (∑ n ∈ Finset.Ico 1 N, ∫ x in grid n..grid (n+1), F x) =
      ∫ x in 0..grid N, F x := by
    simpa only [hfirst] using intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := grid) (f := F) (μ := volume) hN
      (fun n hn => hi n (by simpa only [Finset.mem_Ico, Set.mem_Ico] using hn))
  have hmain : ‖(∑ n ∈ Finset.Ico 1 N, (weight n:ℂ)*F (grid n)) -
      ∫ x in 0..grid N, F x‖ ≤ B*δ + D*δ*a := by
    rw [← hsumInt, ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ n ∈ Finset.Ico 1 N,
          (B*(weight n-(grid (n+1)-grid n)) + D*δ*(grid (n+1)-grid n)) := by
        apply Finset.sum_le_sum
        intro n hn
        have hna : grid n ∈ Icc 0 a := (hcell n hn) ⟨le_rfl,by linarith [(hmesh n hn).1]⟩
        exact cell_quadrature_error (by linarith [(hmesh n hn).1])
          (hweight n hn) (hmesh n hn).2 hD (hF.mono (hcell n hn))
          (hbound _ hna) (fun x hx => hLip _ hna x (hcell n hn hx))
      _ = B*(∑ n ∈ Finset.Ico 1 N, (weight n - (grid (n+1) - grid n))) +
          D*δ*(grid N-grid 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_Ico_sub (f := grid) hN]
      _ ≤ B*δ + D*δ*a := by
        rw [hfirst, sub_zero]
        gcongr
        exact hGN.2
  have hi0 : IntervalIntegrable F volume 0 (grid N) :=
    (hF.mono (Icc_subset_Icc le_rfl hGN.2)).intervalIntegrable_of_Icc hGN.1
  have hitail : IntervalIntegrable F volume (grid N) a :=
    (hF.mono (Icc_subset_Icc hGN.1 le_rfl)).intervalIntegrable_of_Icc hGN.2
  have htailInt : ‖∫ x in grid N..a, F x‖ ≤ B*δ := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := B) ?_).trans
    · rw [abs_of_nonneg htail.1]
      exact mul_le_mul_of_nonneg_left htail.2 hB
    · intro x hx
      rw [uIoc_of_le hGN.2] at hx
      exact hbound x ⟨hGN.1.trans hx.1.le,hx.2⟩
  have htailSum : ‖(weight N:ℂ)*F (grid N) - ∫ x in grid N..a, F x‖ ≤ 2*B*δ := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlast.1]
    have hp : weight N*‖F (grid N)‖ ≤ δ*B :=
      mul_le_mul hlast.2 (hbound _ hGN) (norm_nonneg _) hδ
    nlinarith
  have hid : (∑ n ∈ Finset.Icc 1 N, (weight n:ℂ)*F (grid n)) - ∫ x in 0..a, F x =
      ((∑ n ∈ Finset.Ico 1 N, (weight n:ℂ)*F (grid n)) - ∫ x in 0..grid N, F x) +
        ((weight N:ℂ)*F (grid N) - ∫ x in grid N..a, F x) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top hN,
      ← intervalIntegral.integral_add_adjacent_intervals hi0 hitail]
    ring
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add hmain htailSum).trans_eq (by ring))

end
end SixthMoment.Source.NoDPHarmonic
