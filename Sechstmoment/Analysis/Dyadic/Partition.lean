import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Sechstmoment.Analysis.Profiles.Classes

/-! An actual smooth partition on overlapping geometric scales. -/

namespace Sechstmoment
open Real Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 500000

noncomputable def rectangularSmoothCutoff (x : ℝ) : ℝ :=
  1-Real.smoothTransition (2*x-3)

noncomputable def rectangularSmoothBlockWeight (x : ℝ) : ℝ :=
  rectangularSmoothCutoff x-rectangularSmoothCutoff ((3/2)*x)

theorem rectangularSmoothCutoff_one {x : ℝ} (hx : x ≤ 3/2) :
    rectangularSmoothCutoff x = 1 := by
  unfold rectangularSmoothCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

theorem rectangularSmoothCutoff_zero {x : ℝ} (hx : 2 ≤ x) :
    rectangularSmoothCutoff x = 0 := by
  unfold rectangularSmoothCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem rectangularSmoothBlockWeight_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) rectangularSmoothBlockWeight := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) rectangularSmoothCutoff := by
    unfold rectangularSmoothCutoff
    exact contDiff_const.sub
      (Real.smoothTransition.contDiff.comp
        (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => 2*x-3)))
  exact hc.sub (hc.comp (by fun_prop))

theorem rectangularSmoothBlockWeight_zero_le {x : ℝ} (hx : x ≤ 1) :
    rectangularSmoothBlockWeight x = 0 := by
  unfold rectangularSmoothBlockWeight
  rw [rectangularSmoothCutoff_one (by linarith),
    rectangularSmoothCutoff_one (by linarith)]
  ring

theorem rectangularSmoothBlockWeight_zero_ge {x : ℝ} (hx : 2 ≤ x) :
    rectangularSmoothBlockWeight x = 0 := by
  unfold rectangularSmoothBlockWeight
  rw [rectangularSmoothCutoff_zero hx, rectangularSmoothCutoff_zero (by linarith)]
  ring

theorem rectangularSmoothBlockWeight_tsupport :
    tsupport rectangularSmoothBlockWeight ⊆ Icc 1 2 := by
  apply closure_minimal
  · intro x hx
    constructor
    · by_contra h
      exact hx (rectangularSmoothBlockWeight_zero_le (le_of_not_ge h))
    · by_contra h
      exact hx (rectangularSmoothBlockWeight_zero_ge (le_of_not_ge h))
  · exact isClosed_Icc

theorem rectangularSmoothBlockWeight_smoothDyadic :
    SmoothDyadicWeight rectangularSmoothBlockWeight :=
  ⟨rectangularSmoothBlockWeight_contDiff, rectangularSmoothBlockWeight_tsupport⟩

theorem rectangularSmoothBlockWeight_nonneg (x : ℝ) :
    0 ≤ rectangularSmoothBlockWeight x := by
  by_cases hx : x ≤ 1
  · rw [rectangularSmoothBlockWeight_zero_le hx]
  · have hx0 : 0 ≤ x := by linarith
    have h := Real.smoothTransition.monotone (show 2*x-3 ≤ 2*((3/2)*x)-3 by nlinarith)
    unfold rectangularSmoothBlockWeight rectangularSmoothCutoff
    linarith

theorem rectangularSmoothBlockWeight_le_one (x : ℝ) :
    rectangularSmoothBlockWeight x ≤ 1 := by
  unfold rectangularSmoothBlockWeight rectangularSmoothCutoff
  linarith [Real.smoothTransition.le_one (2*((3/2)*x)-3),
    Real.smoothTransition.nonneg (2*x-3)]

theorem rectangularSmoothBlockWeight_hasCompactSupport :
    HasCompactSupport rectangularSmoothBlockWeight :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) rectangularSmoothBlockWeight_tsupport

theorem rectangularSmoothBlockWeight_iteratedDeriv_hasCompactSupport (j : ℕ) :
    HasCompactSupport (iteratedDeriv j rectangularSmoothBlockWeight) := by
  induction j with
  | zero => simpa using rectangularSmoothBlockWeight_hasCompactSupport
  | succ j hj => rw [iteratedDeriv_succ]; exact hj.deriv

/-- Every derivative of the fixed source weight has an actual global bound. -/
theorem rectangularSmoothBlockWeight_derivative_bounds :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ j x, ‖iteratedDeriv j rectangularSmoothBlockWeight x‖ ≤ B j := by
  have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, ‖iteratedDeriv j rectangularSmoothBlockWeight x‖ ≤ C := by
    obtain ⟨C,hC⟩ := (rectangularSmoothBlockWeight_iteratedDeriv_hasCompactSupport j).exists_bound_of_continuous
        (rectangularSmoothBlockWeight_contDiff.continuous_iteratedDeriv j (by simp))
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
  choose B hB hbounds using hb
  exact ⟨B,hB,hbounds⟩

theorem rectangularSmoothBlockWeight_weightSeminormBound (J : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ WeightSeminormBound J B rectangularSmoothBlockWeight := by
  obtain ⟨C,hC,hbounds⟩ := rectangularSmoothBlockWeight_derivative_bounds
  refine ⟨∑ j ∈ Finset.range (J+1), C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro j hj x
  exact (hbounds j x).trans
    (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

/-- Finite telescoping is exact, with no analytically assumed partition. -/
theorem rectangularSmoothBlockWeight_sum (x : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), rectangularSmoothBlockWeight ((3/2)*x/(3/2)^k) =
      rectangularSmoothCutoff ((3/2)*x/(3/2)^n)-rectangularSmoothCutoff ((3/2)^2*x) := by
  induction n with
  | zero => simp [rectangularSmoothBlockWeight]; congr 1; ring
  | succ n hn =>
    rw [Finset.sum_range_succ, hn]
    unfold rectangularSmoothBlockWeight
    have he : (3/2)*((3/2)*x/(3/2)^(n+1)) = (3/2)*x/(3/2)^n := by
      rw [pow_succ]
      field_simp
    rw [he]
    ring

/-- For each positive source variable, the smooth geometric partition is
already finite and its finite sums stabilize exactly to one. -/
theorem rectangularSmoothBlockWeight_partition {x : ℝ} (hx : 1 ≤ x) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∑ k ∈ Finset.range (n+1), rectangularSmoothBlockWeight ((3/2)*x/(3/2)^k) = 1 := by
  have ht : Tendsto (fun n : ℕ => (3/2)*x/(3/2)^n) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have he : ∀ᶠ n : ℕ in atTop, (3/2)*x/(3/2)^n ≤ 3/2 :=
    ht.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 3/2))
  obtain ⟨N,hN⟩ := eventually_atTop.1 he
  refine ⟨N,fun n hn => ?_⟩
  rw [rectangularSmoothBlockWeight_sum,
    rectangularSmoothCutoff_one (hN n hn),
    rectangularSmoothCutoff_zero (by nlinarith)]
  ring

/-- Local finiteness holds for the actual numerical geometric weights. -/
theorem rectangularSmoothBlockWeight_eventually_zero (x : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, rectangularSmoothBlockWeight ((3/2)*x/(3/2)^n) = 0 := by
  have ht : Tendsto (fun n : ℕ => (3/2)*x/(3/2)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have he : ∀ᶠ n : ℕ in atTop, (3/2)*x/(3/2)^n ≤ 1 :=
    ht.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  obtain ⟨N,hN⟩ := eventually_atTop.1 he
  exact ⟨N,fun n hn => rectangularSmoothBlockWeight_zero_le (hN n hn)⟩

theorem rectangularSmoothBlockWeight_hasFiniteSupport (x : ℝ) :
    Function.HasFiniteSupport (fun k : ℕ => rectangularSmoothBlockWeight ((3/2)*x/(3/2)^k)) := by
  obtain ⟨N,hN⟩ := rectangularSmoothBlockWeight_eventually_zero x
  apply (Finset.range N).finite_toSet.subset
  intro k hk
  apply Finset.mem_range.mpr
  by_contra h
  exact hk (hN k (Nat.le_of_not_gt h))

theorem rectangularSmoothBlockWeight_summable (x : ℝ) :
    Summable (fun k : ℕ => rectangularSmoothBlockWeight ((3/2)*x/(3/2)^k)) :=
  summable_of_hasFiniteSupport (rectangularSmoothBlockWeight_hasFiniteSupport x)

theorem rectangularSmoothBlockWeight_tsum {x : ℝ} (hx : 1 ≤ x) :
    ∑' k : ℕ, rectangularSmoothBlockWeight ((3/2)*x/(3/2)^k) = 1 := by
  obtain ⟨N,hN⟩ := rectangularSmoothBlockWeight_eventually_zero x
  obtain ⟨M,hM⟩ := rectangularSmoothBlockWeight_partition hx
  have hz (k : ℕ) (hk : k ∉ Finset.range (max N M+1)) :
      rectangularSmoothBlockWeight ((3/2)*x/(3/2)^k)=0 := by
    apply hN k
    have h := Nat.le_of_not_gt (fun hl => hk (Finset.mem_range.mpr hl))
    exact (le_max_left N M).trans ((Nat.le_succ _).trans h)
  rw [tsum_eq_sum hz]
  exact hM _ (le_max_right _ _)

/-- One finite cutoff works simultaneously for an actual finite set of
source variables; thus finite block sums can be inserted before rearranging. -/
theorem rectangularSmoothBlockWeight_finite_partition {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, 1 ≤ x i) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ s,
      ∑ k ∈ Finset.range (n+1), rectangularSmoothBlockWeight ((3/2)*x i/(3/2)^k) = 1 := by
  classical
  have h (i : ι) : ∃ N : ℕ, ∀ n ≥ N, i ∈ s →
      ∑ k ∈ Finset.range (n+1), rectangularSmoothBlockWeight ((3/2)*x i/(3/2)^k) = 1 := by
    by_cases hi : i ∈ s
    · obtain ⟨N,hN⟩ := rectangularSmoothBlockWeight_partition (hx i hi)
      exact ⟨N,fun n hn _ => hN n hn⟩
    · exact ⟨0,fun _ _ hi' => (hi hi').elim⟩
  choose N hN using h
  refine ⟨s.sup N,fun n hn i hi => hN i n ?_ hi⟩
  exact (Finset.le_sup hi).trans hn

/-- The actual product partition used for simultaneous BBLR block variables.
The dimensions may include both amplifiers and all four AFE indices. -/
theorem rectangularSmoothBlockWeight_product_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, 1 ≤ x i) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∑ k ∈ Fintype.piFinset (fun _ : ι => Finset.range (n+1)),
        ∏ i, rectangularSmoothBlockWeight ((3/2)*x i/(3/2)^(k i)) = 1 := by
  classical
  obtain ⟨N,hN⟩ := rectangularSmoothBlockWeight_finite_partition Finset.univ x
    (fun i _ => hx i)
  refine ⟨N,fun n hn => ?_⟩
  rw [← Finset.prod_univ_sum (fun _ : ι => Finset.range (n+1))
    (fun i k => rectangularSmoothBlockWeight ((3/2)*x i/(3/2)^k))]
  simp only [hN n hn _ (Finset.mem_univ _),Finset.prod_const_one]

/-- Exact insertion of the genuine smooth partition into any finite complex
source sum, with a common finite index range. -/
theorem rectangularSmoothBlockWeight_finite_sum_reconstruction {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (a : ι → ℂ) (hx : ∀ i ∈ s, 1 ≤ x i) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∑ i ∈ s, a i =
        ∑ k ∈ Finset.range (n+1), ∑ i ∈ s,
          (rectangularSmoothBlockWeight ((3/2)*x i/(3/2)^k) : ℂ)*a i := by
  classical
  obtain ⟨N,hN⟩ := rectangularSmoothBlockWeight_finite_partition s x hx
  refine ⟨N,fun n hn => ?_⟩
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul,← Complex.ofReal_sum,hN n hn i hi,Complex.ofReal_one,one_mul]

end Sechstmoment
