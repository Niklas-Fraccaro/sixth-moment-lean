import Sechstmoment.Arithmetic.Euler.Residues.TailEstimates

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPResidues
open NoDPLocal
open scoped BigOperators
noncomputable def diagonalTerm (W : ℕ → ℂ) (U V : ℂ) (p : ℕ × ℕ) : ℂ :=
  W (p.1+p.2)*U^p.1*V^p.2
noncomputable def doubleSeries (W : ℕ → ℂ) (U V : ℂ) : ℂ := ∑' p : ℕ × ℕ, diagonalTerm W U V p

theorem quadratic_split_bound (m n : ℕ) :
    ((m:ℝ)+(n:ℝ)+4)^2 ≤ ((m:ℝ)+4)^2*((n:ℝ)+4)^2 := by
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have H : (m:ℝ)+(n:ℝ)+4 ≤ ((m:ℝ)+4)*((n:ℝ)+4) := by nlinarith [mul_nonneg hm hn]
  calc
    _ ≤ (((m:ℝ)+4)*((n:ℝ)+4))^2 := pow_le_pow_left₀ (by positivity) H 2
    _ = _ := by ring

theorem diagonalTerm_norm (W : ℕ → ℂ) (U V : ℂ) (p : ℕ × ℕ) :
    ‖diagonalTerm W U V p‖ = ‖W (p.1+p.2)‖*‖U‖^p.1*‖V‖^p.2 := by
  simp only [diagonalTerm, norm_mul, norm_pow]

theorem diagonal_majorant (W : ℕ → ℂ) (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hW : ∀ n, ‖W n‖ ≤ C*((n:ℝ)+4)^2*r^n) (U V : ℂ) (p : ℕ × ℕ) :
    ‖diagonalTerm W U V p‖ ≤ C*
      ((((p.1:ℝ)+4)^2*(r*‖U‖)^p.1)*(((p.2:ℝ)+4)^2*(r*‖V‖)^p.2)) := by
  rw [diagonalTerm_norm]
  have H := quadratic_split_bound p.1 p.2
  calc
    _ ≤ (C*(((p.1+p.2:ℕ):ℝ)+4)^2*r^(p.1+p.2))*‖U‖^p.1*‖V‖^p.2 := by gcongr; exact hW _
    _ ≤ (C*(((p.1:ℝ)+4)^2*((p.2:ℝ)+4)^2)*r^(p.1+p.2))*‖U‖^p.1*‖V‖^p.2 := by
      push_cast
      gcongr
    _ = _ := by rw [pow_add, mul_pow, mul_pow]; ring

theorem diagonal_summable (W : ℕ → ℂ) (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hW : ∀ n, ‖W n‖ ≤ C*((n:ℝ)+4)^2*r^n) (U V : ℂ)
    (hU : r*‖U‖ < 1) (hV : r*‖V‖ < 1) : Summable (diagonalTerm W U V) := by
  have hqU : ‖r*‖U‖‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hU
  have hqV : ‖r*‖V‖‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hV
  have H1 := quadratic_geometric_summable (r*‖U‖) 4 hqU
  have H2 := quadratic_geometric_summable (r*‖V‖) 4 hqV
  have H := (summable_mul_of_summable_norm H1.norm H2.norm).mul_left C
  apply H.of_norm_bounded
  intro p
  exact diagonal_majorant W C r hC hr hW U V p

theorem diagonal_norm_summable (W : ℕ → ℂ) (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hW : ∀ n, ‖W n‖ ≤ C*((n:ℝ)+4)^2*r^n) (U V : ℂ)
    (hU : r*‖U‖ < 1) (hV : r*‖V‖ < 1) :
    Summable (fun p : ℕ × ℕ => ‖diagonalTerm W U V p‖) :=
  (diagonal_summable W C r hC hr hW U V hU hV).norm

theorem weightedResidue_double_summable (ai a b c x U V : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖x*a/ai‖ ≤ r) (hb : ‖x*b/ai‖ ≤ r) (hc : ‖x*c/ai‖ ≤ r) (hr1 : r ≤ 1)
    (hU : (‖ai‖*r)*‖U‖ < 1) (hV : (‖ai‖*r)*‖V‖ < 1) :
    Summable (diagonalTerm (weightedResidue ai a b c x) U V) := by
  apply diagonal_summable _ 12 (‖ai‖*r) (by norm_num) (by positivity) _ U V hU hV
  intro n
  simpa only [quadraticHeight, mul_assoc] using weightedResidue_bound ai a b c x r hr ha hb hc hr1 n

theorem weightedResidue_double_norm_summable (ai a b c x U V : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖x*a/ai‖ ≤ r) (hb : ‖x*b/ai‖ ≤ r) (hc : ‖x*c/ai‖ ≤ r) (hr1 : r ≤ 1)
    (hU : (‖ai‖*r)*‖U‖ < 1) (hV : (‖ai‖*r)*‖V‖ < 1) :
    Summable (fun p : ℕ × ℕ => ‖diagonalTerm (weightedResidue ai a b c x) U V p‖) :=
  (weightedResidue_double_summable ai a b c x U V r hr ha hb hc hr1 hU hV).norm

theorem doubleSeries_iterated_left (W : ℕ → ℂ) (U V : ℂ) (hs : Summable (diagonalTerm W U V)) :
    doubleSeries W U V = ∑' m : ℕ, ∑' n : ℕ, W (m+n)*U^m*V^n := hs.tsum_prod

theorem doubleSeries_iterated_right (W : ℕ → ℂ) (U V : ℂ) (hs : Summable (diagonalTerm W U V)) :
    doubleSeries W U V = ∑' n : ℕ, ∑' m : ℕ, W (m+n)*U^m*V^n := by
  rw [doubleSeries_iterated_left W U V hs]
  have hs' : Summable (Function.uncurry (fun m n : ℕ => W (m+n)*U^m*V^n)) := hs
  exact hs'.tsum_comm.symm

theorem doubleSeries_swap (W : ℕ → ℂ) (U V : ℂ) : doubleSeries W U V = doubleSeries W V U := by
  have H := (Equiv.prodComm ℕ ℕ).tsum_eq (diagonalTerm W V U)
  simpa [doubleSeries, diagonalTerm, Nat.add_comm, mul_comm, mul_left_comm, mul_assoc] using H

theorem doubleSeries_axis_left (W : ℕ → ℂ) (U : ℂ) (hs : Summable (diagonalTerm W U 0)) :
    doubleSeries W U 0 = ∑' m : ℕ, W m*U^m := by
  rw [doubleSeries_iterated_left W U 0 hs]
  apply tsum_congr
  intro m
  rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

theorem doubleSeries_axis_right (W : ℕ → ℂ) (V : ℂ) (hs : Summable (diagonalTerm W 0 V)) :
    doubleSeries W 0 V = ∑' n : ℕ, W n*V^n := by
  rw [doubleSeries_swap]
  apply doubleSeries_axis_left
  have H := hs.prod_symm
  change Summable (fun p : ℕ × ℕ => W (p.1+p.2)*V^p.1*(0:ℂ)^p.2)
  simpa [diagonalTerm, Nat.add_comm, mul_comm, mul_left_comm, mul_assoc] using H

theorem weightedResidue_double_origin (ai a b c x : ℂ) :
    doubleSeries (weightedResidue ai a b c x) 0 0 = 1 := by
  unfold doubleSeries
  rw [tsum_eq_single (0,0)]
  · simp [diagonalTerm]
  · intro p hp
    obtain ⟨m,n⟩ := p
    by_cases hm : m = 0
    · subst m
      have hn : n ≠ 0 := by intro hn; exact hp (by simp [hn])
      simp [diagonalTerm, zero_pow hn]
    · simp [diagonalTerm, zero_pow hm]

theorem diagonal_row_summable (W : ℕ → ℂ) (U V : ℂ)
    (hs : Summable (diagonalTerm W U V)) (m : ℕ) :
    Summable (fun n : ℕ => W (m+n)*U^m*V^n) := hs.prod_factor m

theorem diagonal_outer_summable (W : ℕ → ℂ) (U V : ℂ)
    (hs : Summable (diagonalTerm W U V)) :
    Summable (fun m : ℕ => ∑' n : ℕ, W (m+n)*U^m*V^n) := hs.prod

theorem residueRest_linear_norm_bound (ai a b c x : ℂ) (hai : ai ≠ 0)
    (r : ℝ) (hr : 0 ≤ r) (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) :
    ‖residueRest ai a b c x 1 0‖ ≤ ‖x‖^2/‖ai‖*(3*r^2+(‖x‖/‖ai‖)*r^3) := by
  have E : residueRest ai a b c x 1 0 = weightedResidue ai a b c x 1-x*(a+b+c) := by
    rw [(residueRest_linear ai a b c x hai).1, weightedResidue_first ai a b c x hai]
    ring
  rw [E]
  exact weightedResidue_first_error_bound ai a b c x hai r hr ha hb hc

end Sechstmoment.Source.NoDPResidues
