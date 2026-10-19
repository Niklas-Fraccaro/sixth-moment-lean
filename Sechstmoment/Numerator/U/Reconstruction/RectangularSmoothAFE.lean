import Mathlib.Topology.Algebra.InfiniteSum.Real
import Sechstmoment.Analysis.Dyadic.Partition
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEInterchange

/-! The actual convergent fourfold AFE is regrouped using a genuine
nonnegative smooth partition. The bounded-small-scale edge is retained. -/

namespace Sechstmoment
open Complex Source MeasureTheory Set
open scoped BigOperators Topology
open Classical
noncomputable section

set_option maxHeartbeats 2000000

theorem rectangular_finitePi_hasSum_prod_nonneg (d : ℕ) (f : Fin d → ℕ → ℝ)
    (s : Fin d → ℝ) (hf0 : ∀ j k, 0 ≤ f j k) (hf : ∀ j, HasSum (f j) (s j)) :
    HasSum (fun k : Fin d → ℕ => ∏ j, f j (k j)) (∏ j, s j) := by
  induction d with
  | zero => simp
  | succ d ih =>
    let e := Fin.insertNthEquiv (fun _ : Fin (d+1) => ℕ) 0
    have ht := ih (fun j => f j.succ) (fun j => s j.succ)
      (fun j k => hf0 j.succ k) (fun j => hf j.succ)
    have hp := (hf 0).summable.mul_of_nonneg ht.summable (hf0 0)
      (fun k => Finset.prod_nonneg (fun j _ => hf0 j.succ (k j)))
    apply e.hasSum_iff.mp
    simpa [Function.comp_def, e, Fin.insertNthEquiv, Fin.prod_univ_succ] using
      (hf 0).mul ht hp

def rectangularAFESmoothScale (k : ℕ) : ℝ := (3/2)^k/(3/2)

def rectangularAFESmoothWeight (k n : Fin 4 → ℕ) : ℝ :=
  ∏ j : Fin 4, rectangularSmoothBlockWeight ((3/2)*(n j+1 : ℝ)/(3/2)^(k j))

theorem rectangular_AFE_smooth_weight_nonneg (k n : Fin 4 → ℕ) :
    0 ≤ rectangularAFESmoothWeight k n :=
  Finset.prod_nonneg (fun _j _ => rectangularSmoothBlockWeight_nonneg _)

/-- The partition of the actual four positive integer variables sums exactly
to one, rather than being supplied as a decomposition hypothesis. -/
theorem rectangular_AFE_smooth_weight_hasSum (n : Fin 4 → ℕ) :
    HasSum (fun k => rectangularAFESmoothWeight k n) 1 := by
  have h := rectangular_finitePi_hasSum_prod_nonneg 4
    (fun j k => rectangularSmoothBlockWeight ((3/2)*(n j+1 : ℝ)/(3/2)^k)) (fun _ => 1)
    (fun j k => rectangularSmoothBlockWeight_nonneg _)
    (fun j => by
      have hs := rectangularSmoothBlockWeight_summable (n j+1 : ℝ)
      have he := rectangularSmoothBlockWeight_tsum (show (1:ℝ) ≤ n j+1 by
        linarith [Nat.cast_nonneg (α := ℝ) (n j)])
      simpa only [he] using hs.hasSum)
  simpa [rectangularAFESmoothWeight] using h

/-- Absolute summability of the complete double smooth-block expansion is
inherited from the original convergent series by nonnegativity and sum one. -/
theorem rectangular_AFE_smooth_double_summable (f : (Fin 4 → ℕ) → ℂ) (hf : Summable f) :
    Summable (fun p : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
      (rectangularAFESmoothWeight p.2 p.1 : ℂ)*f p.1) := by
  let R : ((Fin 4 → ℕ) × (Fin 4 → ℕ)) → ℝ := fun p =>
    rectangularAFESmoothWeight p.2 p.1*‖f p.1‖
  have hInner (n : Fin 4 → ℕ) : Summable (fun k : Fin 4 → ℕ => R (n,k)) := by
    dsimp only [R]
    exact (rectangular_AFE_smooth_weight_hasSum n).summable.mul_right ‖f n‖
  have hOuter : Summable (fun n : Fin 4 → ℕ => ∑' k : Fin 4 → ℕ, R (n,k)) := by
    apply hf.norm.congr
    intro n
    dsimp only [R]
    rw [tsum_mul_right, (rectangular_AFE_smooth_weight_hasSum n).tsum_eq, one_mul]
  have hR : Summable R := (summable_prod_of_nonneg (f := R) (fun p =>
    mul_nonneg (rectangular_AFE_smooth_weight_nonneg p.2 p.1) (norm_nonneg _))).mpr ⟨hInner,hOuter⟩
  apply Summable.of_norm
  apply hR.congr
  intro p
  simp only [R, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (rectangular_AFE_smooth_weight_nonneg p.2 p.1)]

theorem rectangular_AFE_smooth_grouping (f : (Fin 4 → ℕ) → ℂ) (hf : Summable f) :
    (∑' n, f n) = ∑' k : Fin 4 → ℕ, ∑' n : Fin 4 → ℕ,
      (rectangularAFESmoothWeight k n : ℂ)*f n := by
  have hs := rectangular_AFE_smooth_double_summable f hf
  calc
    _ = ∑' n : Fin 4 → ℕ, ∑' k : Fin 4 → ℕ,
        (rectangularAFESmoothWeight k n : ℂ)*f n := by
      apply tsum_congr
      intro n
      have hh : HasSum (fun k => (rectangularAFESmoothWeight k n : ℂ)*f n) (f n) := by
        have he := ((Complex.ofRealCLM.hasSum (rectangular_AFE_smooth_weight_hasSum n)).mul_right (f n))
        simpa using he
      exact hh.tsum_eq.symm
    _ = _ := hs.tsum_comm.symm

def rectangularAFESmoothBox (k : Fin 4 → ℕ) : Finset (Fin 4 → ℕ) :=
  Fintype.piFinset fun j => Finset.range ⌊2*rectangularAFESmoothScale (k j)⌋₊

/-- Each actual smooth block contains only finitely many positive integers.
The lowest scale `2/3` is present, so integer one is retained. -/
theorem rectangular_AFE_smooth_weight_zero_outside (k n : Fin 4 → ℕ)
    (hn : n ∉ rectangularAFESmoothBox k) : rectangularAFESmoothWeight k n = 0 := by
  simp only [rectangularAFESmoothBox, Fintype.mem_piFinset, Finset.mem_range] at hn
  push Not at hn
  obtain ⟨j, hj⟩ := hn
  have hjr : (⌊2*rectangularAFESmoothScale (k j)⌋₊ : ℝ) ≤ n j := by exact_mod_cast hj
  have hb : 2*rectangularAFESmoothScale (k j) < (n j+1 : ℝ) := by
    have hh := Nat.lt_floor_add_one (2*rectangularAFESmoothScale (k j))
    linarith
  have hb' : 2*(3/2 : ℝ)^(k j)/(3/2) < (n j+1 : ℝ) := by
    simpa only [rectangularAFESmoothScale, mul_div_assoc] using hb
  have ha : 2 ≤ (3/2)*(n j+1 : ℝ)/(3/2)^(k j) := by
    apply (le_div_iff₀ (pow_pos (by norm_num : (0:ℝ) < 3/2) _)).mpr
    have hh := (div_lt_iff₀ (by norm_num : (0:ℝ) < 3/2)).mp hb'
    linarith
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  exact rectangularSmoothBlockWeight_zero_ge ha

theorem rectangular_AFE_smooth_block_finite (f : (Fin 4 → ℕ) → ℂ) (k : Fin 4 → ℕ) :
    (∑' n : Fin 4 → ℕ, (rectangularAFESmoothWeight k n : ℂ)*f n) =
      ∑ n ∈ rectangularAFESmoothBox k, (rectangularAFESmoothWeight k n : ℂ)*f n := by
  apply tsum_eq_sum
  intro n hn
  simp only [rectangular_AFE_smooth_weight_zero_outside k n hn, Complex.ofReal_zero, zero_mul]

/-- The genuine full AFE is now the sum of actual finite smooth blocks,
with absolute regrouping proved from its actual fourfold convergence. -/
theorem rectangular_actual_AFE_smooth_blocks (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re) :
    bblrAFESum G α t = ∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFESmoothBox k,
      (rectangularAFESmoothWeight k n : ℂ)*bblrAFESummand G α t n := by
  rw [bblrAFESum, rectangular_AFE_smooth_grouping _
    (rectangular_actual_AFE_summable G α hG t hα)]
  exact tsum_congr (fun k => rectangular_AFE_smooth_block_finite _ k)

/-- The all-source-scale range starts at index one. The omitted index-zero
edge is not discarded by the exact smooth reconstruction. -/
theorem rectangular_AFE_smooth_scale_ge_one {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ rectangularAFESmoothScale k := by
  unfold rectangularAFESmoothScale
  apply (le_div_iff₀ (by norm_num : (0:ℝ) < 3/2)).mpr
  have he : (3/2 : ℝ) = (3/2 : ℝ)^1 := by simp
  rw [he]
  exact pow_le_pow_right₀ (by norm_num) hk

theorem rectangular_AFE_smooth_low_scale : rectangularAFESmoothScale 0 = 2/3 := by
  norm_num [rectangularAFESmoothScale]

/-- A lowest-scale block contributes only when the corresponding positive
integer AFE variable is exactly one. This boundary is retained explicitly. -/
theorem rectangular_AFE_smooth_low_block_zero (k n : Fin 4 → ℕ) (j : Fin 4)
    (hk : k j = 0) (hn : n j ≠ 0) : rectangularAFESmoothWeight k n = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [hk, pow_zero, div_one]
  apply rectangularSmoothBlockWeight_zero_ge
  have hn' : (1:ℝ) ≤ n j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  linarith

theorem rectangular_AFE_smooth_blocks_summable (f : (Fin 4 → ℕ) → ℂ) (hf : Summable f) :
    Summable (fun k : Fin 4 → ℕ => ∑ n ∈ rectangularAFESmoothBox k,
      (rectangularAFESmoothWeight k n : ℂ)*f n) := by
  apply (rectangular_AFE_smooth_double_summable f hf).prod_symm.prod.congr
  intro k
  exact rectangular_AFE_smooth_block_finite f k

/-- The actual full AFE splits into source-domain smooth blocks and the
explicit boundary blocks containing at least one integer-one variable. -/
theorem rectangular_actual_AFE_smooth_interior_boundary (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (t : ℝ) (hα : ∀ j, -1/2 < (α j).re) :
    bblrAFESum G α t =
      (∑' k : Fin 4 → ℕ, if (∀ j, 1 ≤ k j) then
        ∑ n ∈ rectangularAFESmoothBox k, (rectangularAFESmoothWeight k n : ℂ)*bblrAFESummand G α t n
        else 0)+
      (∑' k : Fin 4 → ℕ, if ¬(∀ j, 1 ≤ k j) then
        ∑ n ∈ rectangularAFESmoothBox k, (rectangularAFESmoothWeight k n : ℂ)*bblrAFESummand G α t n
        else 0) := by
  let F := fun k : Fin 4 → ℕ => ∑ n ∈ rectangularAFESmoothBox k,
    (rectangularAFESmoothWeight k n : ℂ)*bblrAFESummand G α t n
  have hs : Summable F := rectangular_AFE_smooth_blocks_summable _
    (rectangular_actual_AFE_summable G α hG t hα)
  have hi : Summable (fun k => if (∀ j, 1 ≤ k j) then F k else 0) := by
    apply hs.norm.of_norm_bounded
    intro k
    by_cases hk : ∀ j, 1 ≤ k j <;> simp [hk]
  have he : Summable (fun k => if ¬(∀ j, 1 ≤ k j) then F k else 0) := by
    apply hs.norm.of_norm_bounded
    intro k
    by_cases hk : ∀ j, 1 ≤ k j <;> simp [hk]
  rw [rectangular_actual_AFE_smooth_blocks G α hG t hα, ← hi.tsum_add he]
  apply tsum_congr
  intro k
  by_cases hk : ∀ j, 1 ≤ k j <;> simp [F, hk]

/-- After the genuine time-series interchange, the actual weighted moment
AFE integral is the absolutely convergent sum of finite smooth blocks. -/
theorem rectangular_actual_AFE_integrated_smooth_blocks (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, -1/2 < (α j).re)
    (w : ℝ → ℂ) (hw : Continuous w) (hws : HasCompactSupport w) :
    (∫ t : ℝ, w t*bblrAFESum G α t) =
      ∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFESmoothBox k,
        (rectangularAFESmoothWeight k n : ℂ)*(∫ t : ℝ, w t*bblrAFESummand G α t n) := by
  rw [rectangular_actual_AFE_weighted_integral G α hG hα w hw hws,
    rectangular_AFE_smooth_grouping _
      (rectangular_actual_AFE_weighted_hasSum G α hG hα w hw hws).summable]
  exact tsum_congr (fun k => rectangular_AFE_smooth_block_finite _ k)

end
end Sechstmoment
