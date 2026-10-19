import Sechstmoment.Analysis.Harmonic.Quadrature

/-! Uniform weighted harmonic quadrature on the literal log(n)/L grid. -/

namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

def harmonicQuadrature (L a : ℝ) (F : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*a)⌋₊, ((1/(L*n):ℝ):ℂ)*F (Real.log n/L)

def strictHarmonicQuadrature (L a : ℝ) (F : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*a)⌋₊,
    if Real.log n/L < a then ((1/(L*n):ℝ):ℂ)*F (Real.log n/L) else 0

theorem log_floor_bounds {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) :
    1 ≤ ⌊Real.exp (L*a)⌋₊ ∧
    Real.log ⌊Real.exp (L*a)⌋₊/L ∈ Icc 0 a ∧
    a-Real.log ⌊Real.exp (L*a)⌋₊/L ≤ 1/L := by
  let N := ⌊Real.exp (L*a)⌋₊
  have hN : 1 ≤ N := Nat.le_floor (by
    simpa only [Nat.cast_one] using (Real.one_le_exp_iff.mpr (mul_nonneg hL.le ha)))
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hl : Real.log N ≤ L*a := by
    have h := Real.log_le_log hN0 (Nat.floor_le (Real.exp_pos (L*a)).le)
    simpa only [Real.log_exp] using h
  have hu : L*a < Real.log (N+1:ℕ) := by
    have h := Real.log_lt_log (Real.exp_pos (L*a)) (Nat.lt_floor_add_one (Real.exp (L*a)))
    simpa only [Real.log_exp, Nat.cast_add, Nat.cast_one] using h
  have hinv : 1/(N:ℝ) ≤ 1 := (div_le_one hN0).mpr hN1
  have hgap : L*a-Real.log N ≤ 1 := by
    have hcell := (log_cell_bounds hN).2
    linarith
  refine ⟨hN, ⟨div_nonneg (Real.log_nonneg hN1) hL.le, (div_le_iff₀ hL).mpr (by nlinarith)⟩, ?_⟩
  change a-Real.log N/L ≤ 1/L
  calc
    _ = (L*a-Real.log N)/L := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hgap hL.le

theorem harmonicQuadrature_error {L a B D : ℝ} {F : ℝ → ℂ}
    (hL : 0 < L) (ha : 0 ≤ a) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hF : ContinuousOn F (Icc 0 a)) (hbound : ∀ x ∈ Icc 0 a, ‖F x‖ ≤ B)
    (hLip : ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, ‖F x-F y‖ ≤ D*|x-y|) :
    ‖harmonicQuadrature L a F - ∫ x in 0..a, F x‖ ≤ (3*B+D*a)/L := by
  let N := ⌊Real.exp (L*a)⌋₊
  let grid : ℕ → ℝ := fun n => Real.log n/L
  let weight : ℕ → ℝ := fun n => 1/(L*n)
  have hcut := log_floor_bounds hL ha
  have hN : 1 ≤ N := hcut.1
  have hN0 : (0:ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hfirst : grid 1 = 0 := by simp [grid]
  have hnodes (n : ℕ) (hn : n ∈ Finset.Icc 1 N) : grid n ∈ Icc 0 a := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn0 : (0:ℝ) < n := by linarith
    refine ⟨div_nonneg (Real.log_nonneg hn1) hL.le, ?_⟩
    exact (div_le_div_of_nonneg_right (Real.log_le_log hn0
      (by exact_mod_cast (Finset.mem_Icc.mp hn).2)) hL.le).trans hcut.2.1.2
  have hcell (n : ℕ) (hn : n ∈ Finset.Ico 1 N) :
      0 ≤ grid (n+1)-grid n ∧ grid (n+1)-grid n ≤ weight n ∧ weight n ≤ 1/L := by
    have hnN := (Finset.mem_Ico.mp hn).1
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnN
    have hn0 : (0:ℝ) < n := by linarith
    obtain ⟨hlo,hhi⟩ := log_cell_bounds hnN
    have heq : grid (n+1)-grid n = (Real.log (n+1:ℕ)-Real.log n)/L := by
      dsimp only [grid]
      ring
    rw [heq]
    refine ⟨div_nonneg hlo hL.le, ?_, ?_⟩
    · apply (div_le_div_of_nonneg_right hhi hL.le).trans_eq
      dsimp only [weight]
      field_simp
    · exact one_div_le_one_div_of_le hL (by nlinarith)
  have hmass : (∑ n ∈ Finset.Ico 1 N, (weight n - (grid (n+1) - grid n))) ≤ 1/L := by
    have hw : (∑ n ∈ Finset.Ico 1 N, weight n) =
        (∑ n ∈ Finset.Ico 1 N, 1/(n:ℝ))/L := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n _
      dsimp only [weight]
      field_simp
    rw [Finset.sum_sub_distrib, hw, Finset.sum_Ico_sub (f := grid) hN, hfirst, sub_zero]
    dsimp only [grid]
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hL.le
    linarith [harmonic_Ico_bound N]
  have hlast : 0 ≤ weight N ∧ weight N ≤ 1/L := by
    constructor
    · dsimp only [weight]; positivity
    · exact one_div_le_one_div_of_le hL (by nlinarith)
  have h := finite_quadrature_error hN hB hD hfirst hnodes
    (fun n hn => ⟨(hcell n hn).1,(hcell n hn).2.1.trans (hcell n hn).2.2⟩)
    (fun n hn => (hcell n hn).2.1) hmass hlast
    ⟨by linarith [hcut.2.1.2],hcut.2.2⟩ hF hbound hLip
  calc
    _ ≤ (1/L)*(3*B+D*a) := h
    _ = _ := by ring

theorem log_node_mem {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) {n : ℕ}
    (hn : n ∈ Finset.Icc 1 ⌊Real.exp (L*a)⌋₊) : Real.log n/L ∈ Icc 0 a := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn0 : (0:ℝ) < n := by linarith
  refine ⟨div_nonneg (Real.log_nonneg hn1) hL.le, ?_⟩
  exact (div_le_div_of_nonneg_right (Real.log_le_log hn0
    (by exact_mod_cast (Finset.mem_Icc.mp hn).2)) hL.le).trans (log_floor_bounds hL ha).2.1.2

theorem strictHarmonicQuadrature_endpoint_error {L a B : ℝ} {F : ℝ → ℂ}
    (hL : 0 < L) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Icc 0 a, ‖F x‖ ≤ B) :
    ‖strictHarmonicQuadrature L a F - harmonicQuadrature L a F‖ ≤ B/L := by
  let N := ⌊Real.exp (L*a)⌋₊
  have hcut := log_floor_bounds hL ha
  have hN : 1 ≤ N := hcut.1
  have hN0 : (0:ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hinner : (∑ n ∈ Finset.Ico 1 N,
      if Real.log n/L < a then ((1/(L*n):ℝ):ℂ)*F (Real.log n/L) else 0) =
      ∑ n ∈ Finset.Ico 1 N, ((1/(L*n):ℝ):ℂ)*F (Real.log n/L) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt (Finset.mem_Ico.mp hn).1
    have hlog : Real.log n < Real.log N := Real.log_lt_log hn0 (by exact_mod_cast (Finset.mem_Ico.mp hn).2)
    have hlt : Real.log n/L < a := (div_lt_div_of_pos_right hlog hL).trans_le hcut.2.1.2
    rw [ite_eq_left hlt]
  have hid : strictHarmonicQuadrature L a F - harmonicQuadrature L a F =
      (if Real.log N/L < a then ((1/(L*N):ℝ):ℂ)*F (Real.log N/L) else 0) -
        ((1/(L*N):ℝ):ℂ)*F (Real.log N/L) := by
    unfold strictHarmonicQuadrature harmonicQuadrature
    change (∑ n ∈ Finset.Icc 1 N, _) - (∑ n ∈ Finset.Icc 1 N, _) = _
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top hN,
      Finset.sum_Ico_succ_top hN, hinner]
    ring
  rw [hid]
  split_ifs
  · simp only [sub_self, norm_zero]
    positivity
  · rw [zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1/(L*N))]
    calc
      _ ≤ (1/(L*N))*B := mul_le_mul_of_nonneg_left (hbound _ hcut.2.1) (by positivity)
      _ ≤ (1/L)*B := mul_le_mul_of_nonneg_right
        (one_div_le_one_div_of_le hL (by nlinarith)) hB
      _ = _ := by ring

theorem strictHarmonicQuadrature_error {L a B D : ℝ} {F : ℝ → ℂ}
    (hL : 0 < L) (ha : 0 ≤ a) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hF : ContinuousOn F (Icc 0 a)) (hbound : ∀ x ∈ Icc 0 a, ‖F x‖ ≤ B)
    (hLip : ∀ x ∈ Icc 0 a, ∀ y ∈ Icc 0 a, ‖F x-F y‖ ≤ D*|x-y|) :
    ‖strictHarmonicQuadrature L a F - ∫ x in 0..a, F x‖ ≤ (4*B+D*a)/L := by
  have h := norm_add_le (strictHarmonicQuadrature L a F - harmonicQuadrature L a F)
    (harmonicQuadrature L a F - ∫ x in 0..a, F x)
  rw [sub_add_sub_cancel] at h
  exact h.trans ((add_le_add (strictHarmonicQuadrature_endpoint_error hL ha hB hbound)
    (harmonicQuadrature_error hL ha hB hD hF hbound hLip)).trans_eq (by ring))

theorem strictHarmonicQuadrature_norm {L a B : ℝ} {F : ℝ → ℂ}
    (hL : 0 < L) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Icc 0 a, ‖F x‖ ≤ B) :
    ‖strictHarmonicQuadrature L a F‖ ≤ B*(a+1/L) := by
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊Real.exp (L*a)⌋₊) :
      ‖if Real.log n/L < a then ((1/(L*n):ℝ):ℂ)*F (Real.log n/L) else 0‖ ≤
        (1/(L*n))*B := by
    have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1/(L*n))]
      exact mul_le_mul_of_nonneg_left (hbound _ (log_node_mem hL ha hn)) (by positivity)
    · simp only [norm_zero]
      positivity
  have hsum : (∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*a)⌋₊, (1/(L*n))*B) = B*harmonicMass L a := by
    rw [harmonicMass, harmonic_eq_real_sum, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [one_div, mul_inv_rev]
    ring
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*a)⌋₊, (1/(L*n))*B :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hpoint)
    _ = B*harmonicMass L a := hsum
    _ ≤ B*(a+1/L) := mul_le_mul_of_nonneg_left (by linarith [(harmonicMass_error hL ha).2]) hB

end
end Sechstmoment.Source.NoDPHarmonic
