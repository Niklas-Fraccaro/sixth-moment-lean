import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact
import Sechstmoment.Analysis.Integration.FiniteFubini
import Sechstmoment.Analysis.Simplex.Moments
import Sechstmoment.Arithmetic.Exact.Polynomials

/-!
# The eight masks in the unbalanced denominator

This module supplies the set-theoretic inclusion–exclusion step needed for D05.
Its masks use exactly `Finite.bit`, in the order used by `Finite.dminus`.
All upper-bound violations are strict, so the identity includes the boundary
points of the closed box without an exceptional-set convention.
-/

namespace Sechstmoment
open MeasureTheory
open scoped BigOperators

/-- The affine two-dimensional slice `r₁+r₂+r₃=H`, with `r₃=H-r₁-r₂`. -/
def simplexSlice (H : ℝ) : Set (Fin 2 → ℝ) :=
  {r | 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ H-r 0-r 1}

/-- The slice truncated by the three upper bounds. -/
def boundedSimplexSlice (a b c H : ℝ) : Set (Fin 2 → ℝ) :=
  {r | r ∈ simplexSlice H ∧ r 0 ≤ a ∧ r 1 ≤ b ∧ H-r 0-r 1 ≤ c}

/-- An intersection of upper-bound violations, selected by the evaluator's bits. -/
def simplexUpperMask (a b c H : ℝ) (mask : Fin 8) : Set (Fin 2 → ℝ) :=
  {r | r ∈ simplexSlice H ∧
    (if Finite.bit mask.val 0 then a < r 0 else True) ∧
    (if Finite.bit mask.val 1 then b < r 1 else True) ∧
    (if Finite.bit mask.val 2 then c < H-r 0-r 1 else True)}

/-- The same alternating sign as in the integer evaluator. -/
def simplexMaskSign (mask : Fin 8) : ℝ :=
  (-1)^((List.range 3).filter (Finite.bit mask.val)).length

theorem simplexSlice_closed (H : ℝ) : IsClosed (simplexSlice H) := by
  unfold simplexSlice
  simp only [Set.ofPred_and]
  repeat' apply IsClosed.inter
  all_goals apply isClosed_le <;> fun_prop

theorem simplexSlice_compact (H : ℝ) : IsCompact (simplexSlice H) := by
  apply (isCompact_Icc (a := fun _ : Fin 2 => (0 : ℝ))
    (b := fun _ => max H 0)).of_isClosed_subset (simplexSlice_closed H)
  intro r hr
  rcases hr with ⟨h0, h1, h2⟩
  constructor
  · intro i
    fin_cases i <;> assumption
  · intro i
    fin_cases i <;> dsimp
    all_goals exact le_trans (by linarith) (le_max_left _ _)

theorem simplexUpperMask_measurable (a b c H : ℝ) (mask : Fin 8) :
    MeasurableSet (simplexUpperMask a b c H mask) := by
  have hcap (flag : Bool) (cap : ℝ) (g : (Fin 2 → ℝ) → ℝ)
      (hg : Continuous g) :
      MeasurableSet {r | if flag then cap < g r else True} := by
    cases flag
    · simp
    · simpa only [Bool.coe_true, ite_true] using
        (isOpen_lt continuous_const hg).measurableSet
  unfold simplexUpperMask
  simp only [Set.ofPred_and]
  exact (simplexSlice_closed H).measurableSet.inter
    ((hcap _ a (fun r => r 0) (by fun_prop)).inter
      ((hcap _ b (fun r => r 1) (by fun_prop)).inter
        (hcap _ c (fun r => H-r 0-r 1) (by fun_prop))))

theorem simplexUpperMask_indicator_integrable (a b c H : ℝ) (mask : Fin 8)
    (f : (Fin 2 → ℝ) → ℝ) (hf : Continuous f) :
    Integrable ((simplexUpperMask a b c H mask).indicator f) := by
  have hbase : IntegrableOn f (simplexSlice H) volume :=
    hf.continuousOn.integrableOn_compact (simplexSlice_compact H)
  exact (hbase.mono_set (fun _ hr => hr.1)).integrable_indicator
    (simplexUpperMask_measurable a b c H mask)

/-- Explicit verification of the eight evaluator signs. -/
theorem simplexMaskSign_eq (mask : Fin 8) :
    simplexMaskSign mask = ![(1 : ℝ), -1, -1, 1, -1, 1, 1, -1] mask := by
  fin_cases mask <;> norm_num [simplexMaskSign, Finite.bit, List.range_succ]

/-- Inclusion–exclusion is pointwise, including all upper and lower faces. -/
theorem boundedSimplexSlice_indicator (a b c H : ℝ)
    (f : (Fin 2 → ℝ) → ℝ) (r : Fin 2 → ℝ) :
    (boundedSimplexSlice a b c H).indicator f r =
      ∑ mask : Fin 8, simplexMaskSign mask *
        (simplexUpperMask a b c H mask).indicator f r := by
  classical
  have hab : (r 0 ≤ a) ↔ ¬ (a < r 0) := not_lt.symm
  have hbb : (r 1 ≤ b) ↔ ¬ (b < r 1) := not_lt.symm
  have hcb : (H-r 0-r 1 ≤ c) ↔ ¬ (c < H-r 0-r 1) := not_lt.symm
  simp only [boundedSimplexSlice, simplexUpperMask, Set.indicator_apply,
    Set.mem_ofPred_eq, hab, hbb, hcb]
  by_cases hbase : r ∈ simplexSlice H
  <;> by_cases ha : a < r 0
  <;> by_cases hb : b < r 1
  <;> by_cases hc : c < H-r 0-r 1
  <;> simp [Fin.sum_univ_succ, simplexMaskSign, Finite.bit, List.range_succ,
    hbase, ha, hb, hc]
  all_goals norm_num

/-- The integrated inclusion–exclusion identity.
Integrability is explicit; it is not an analytic assumption about zeta moments. -/
theorem boundedSimplexSlice_integral (a b c H : ℝ)
    (f : (Fin 2 → ℝ) → ℝ)
    (hf : ∀ mask : Fin 8, Integrable
      ((simplexUpperMask a b c H mask).indicator f)) :
    (∫ r, (boundedSimplexSlice a b c H).indicator f r) =
      ∑ mask : Fin 8, simplexMaskSign mask *
        ∫ r, (simplexUpperMask a b c H mask).indicator f r := by
  simp_rw [boundedSimplexSlice_indicator]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro mask _
    exact (hf mask).const_mul (simplexMaskSign mask)

/-- For continuous polynomial integrands, no extra integrability premise remains. -/
theorem boundedSimplexSlice_integral_of_continuous (a b c H : ℝ)
    (f : (Fin 2 → ℝ) → ℝ) (hf : Continuous f) :
    (∫ r, (boundedSimplexSlice a b c H).indicator f r) =
      ∑ mask : Fin 8, simplexMaskSign mask *
        ∫ r, (simplexUpperMask a b c H mask).indicator f r := by
  exact boundedSimplexSlice_integral a b c H f
    (fun mask => simplexUpperMask_indicator_integrable a b c H mask f hf)

/-- The amount subtracted from the total length by a selected upper face. -/
def simplexMaskShift (a b c : ℝ) (mask : Fin 8) : ℝ :=
  (if Finite.bit mask.val 0 then a else 0) +
  (if Finite.bit mask.val 1 then b else 0) +
  (if Finite.bit mask.val 2 then c else 0)

/-- Translation in the two coordinates carrying the slice measure `dr₁ dr₂`. -/
def simplexMaskTranslate (a b : ℝ) (mask : Fin 8) (r : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![r 0 + (if Finite.bit mask.val 0 then a else 0),
    r 1 + (if Finite.bit mask.val 1 then b else 0)]

/-- After translation, selected lower faces are open and the other faces closed. -/
def simplexFaceMask (H : ℝ) (mask : Fin 8) : Set (Fin 2 → ℝ) :=
  {r | (if Finite.bit mask.val 0 then 0 < r 0 else 0 ≤ r 0) ∧
    (if Finite.bit mask.val 1 then 0 < r 1 else 0 ≤ r 1) ∧
    (if Finite.bit mask.val 2 then 0 < H-r 0-r 1 else 0 ≤ H-r 0-r 1)}

/-- The slack coordinate transforms by exactly the sum of the selected caps. -/
theorem simplexMaskTranslate_slack (a b c H : ℝ) (mask : Fin 8)
    (r : Fin 2 → ℝ) :
    H-(simplexMaskTranslate a b mask r) 0-(simplexMaskTranslate a b mask r) 1 -
      (if Finite.bit mask.val 2 then c else 0) =
    (H-simplexMaskShift a b c mask)-r 0-r 1 := by
  simp only [simplexMaskTranslate, simplexMaskShift,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- Exact translation of every mask, retaining its strict boundary convention. -/
theorem simplexUpperMask_translate {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : ℝ)
    (mask : Fin 8) (r : Fin 2 → ℝ) :
    simplexMaskTranslate a b mask r ∈ simplexUpperMask a b c H mask ↔
      r ∈ simplexFaceMask (H-simplexMaskShift a b c mask) mask := by
  simp only [simplexUpperMask, simplexFaceMask, simplexSlice, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h0, h1, h2⟩, h3, h4, h5⟩
    fin_cases mask
    all_goals
      norm_num [Finite.bit, simplexMaskShift, simplexMaskTranslate] at *
      repeat' constructor
      all_goals linarith
  · rintro ⟨h0, h1, h2⟩
    fin_cases mask
    all_goals
      norm_num [Finite.bit, simplexMaskShift, simplexMaskTranslate] at *
      repeat' constructor
      all_goals linarith

/-- Translation preserves exactly the two-dimensional slice measure. -/
theorem simplexUpperMask_integral_translate {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : ℝ)
    (mask : Fin 8) (f : (Fin 2 → ℝ) → ℝ) :
    (∫ r, (simplexUpperMask a b c H mask).indicator f r) =
      ∫ r, (simplexFaceMask (H-simplexMaskShift a b c mask) mask).indicator
        (fun r => f (simplexMaskTranslate a b mask r)) r := by
  classical
  let shift : Fin 2 → ℝ :=
    ![(if Finite.bit mask.val 0 then a else 0),
      (if Finite.bit mask.val 1 then b else 0)]
  have ht (r : Fin 2 → ℝ) : r+shift = simplexMaskTranslate a b mask r := by
    funext i
    fin_cases i <;> simp [shift, simplexMaskTranslate]
  calc
    (∫ r, (simplexUpperMask a b c H mask).indicator f r) =
        ∫ r, (simplexUpperMask a b c H mask).indicator f (r+shift) :=
      (integral_add_right_eq_self _ shift).symm
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro r
      change (simplexUpperMask a b c H mask).indicator f (r+shift) = _
      rw [ht]
      change (if simplexMaskTranslate a b mask r ∈ simplexUpperMask a b c H mask
        then f (simplexMaskTranslate a b mask r) else 0) =
        (if r ∈ simplexFaceMask (H-simplexMaskShift a b c mask) mask
        then f (simplexMaskTranslate a b mask r) else 0)
      rw [simplexUpperMask_translate ha hb hc H mask r]

/-- The linear functional defining the third boundary face. -/
noncomputable def simplexCoordinateSum : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

theorem simplexCoordinateSum_apply (r : Fin 2 → ℝ) :
    simplexCoordinateSum r = r 0+r 1 := rfl

/-- The sloping face, as well as both coordinate faces, has zero slice measure. -/
theorem simplex_slack_face_null (H : ℝ) :
    volume {r : Fin 2 → ℝ | H-r 0-r 1 = 0} = 0 := by
  have hproper : simplexCoordinateSum.ker ≠ ⊤ := by
    intro he
    have hm : (![1, 0] : Fin 2 → ℝ) ∈ simplexCoordinateSum.ker := by
      rw [he]
      exact Submodule.mem_top
    norm_num [LinearMap.mem_ker, simplexCoordinateSum_apply] at hm
  have hnull : volume (simplexCoordinateSum.ker : Set (Fin 2 → ℝ)) = 0 :=
    Measure.addHaar_submodule volume simplexCoordinateSum.ker hproper
  have hs : {r : Fin 2 → ℝ | H-r 0-r 1 = 0} =
      (fun r : Fin 2 → ℝ => r+![-H, 0]) ⁻¹'
        (simplexCoordinateSum.ker : Set (Fin 2 → ℝ)) := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe,
      LinearMap.mem_ker, simplexCoordinateSum_apply, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    constructor <;> intro h <;> linarith
  rw [hs, measure_preimage_add_right, hnull]

/-- Opening any subset of the three lower faces does not change its Lebesgue integral. -/
theorem simplexFaceMask_ae_eq (H : ℝ) (mask : Fin 8) :
    simplexFaceMask H mask =ᵐ[volume] simplexSlice H := by
  have h0 : ∀ᵐ r : Fin 2 → ℝ, r 0 ≠ 0 :=
    Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) 0 0
  have h1 : ∀ᵐ r : Fin 2 → ℝ, r 1 ≠ 0 :=
    Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) 1 0
  have h2 : ∀ᵐ r : Fin 2 → ℝ, H-r 0-r 1 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using simplex_slack_face_null H
  have hle (x : ℝ) (hx : x ≠ 0) : 0 < x ↔ 0 ≤ x := by
    constructor
    · exact le_of_lt
    · intro h
      exact lt_of_le_of_ne h (Ne.symm hx)
  filter_upwards [h0, h1, h2] with r hr0 hr1 hr2
  simp only [simplexFaceMask, simplexSlice, Set.mem_ofPred_eq,
    hle _ hr0, hle _ hr1, hle _ hr2, ite_self]

theorem simplexFaceMask_indicator_ae_eq (H : ℝ) (mask : Fin 8)
    (f : (Fin 2 → ℝ) → ℝ) :
    (simplexFaceMask H mask).indicator f =ᵐ[volume] (simplexSlice H).indicator f := by
  classical
  filter_upwards [simplexFaceMask_ae_eq H mask] with r hr
  change (if r ∈ simplexFaceMask H mask then f r else 0) =
    (if r ∈ simplexSlice H then f r else 0)
  rw [hr]

/-- Each mask integral is a translated ordinary closed-simplex integral. -/
theorem simplexUpperMask_integral_simplex {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : ℝ)
    (mask : Fin 8) (f : (Fin 2 → ℝ) → ℝ) :
    (∫ r, (simplexUpperMask a b c H mask).indicator f r) =
      ∫ r, (simplexSlice (H-simplexMaskShift a b c mask)).indicator
        (fun r => f (simplexMaskTranslate a b mask r)) r := by
  rw [simplexUpperMask_integral_translate ha hb hc]
  exact integral_congr_ae (simplexFaceMask_indicator_ae_eq _ _ _)

/-- In the zero-length boundary case the closed slice is a single point. -/
theorem simplexSlice_zero : simplexSlice 0 = {0} := by
  ext r
  constructor
  · rintro ⟨h0, h1, h2⟩
    apply Set.mem_singleton_iff.mpr
    funext i
    fin_cases i <;> dsimp
    all_goals linarith
  · intro hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    simp [simplexSlice]

/-- Negative total length gives an empty slice, with no positivity convention. -/
theorem simplexSlice_empty_of_neg {H : ℝ} (hH : H < 0) : simplexSlice H = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro r hr
  rcases hr with ⟨h0, h1, h2⟩
  linarith

theorem boundedSimplexSlice_empty_of_neg (a b c : ℝ) {H : ℝ} (hH : H < 0) :
    boundedSimplexSlice a b c H = ∅ := by
  ext r
  simp [boundedSimplexSlice, simplexSlice_empty_of_neg hH]

theorem simplexUpperMask_empty_of_neg (a b c : ℝ) {H : ℝ} (hH : H < 0)
    (mask : Fin 8) : simplexUpperMask a b c H mask = ∅ := by
  ext r
  simp [simplexUpperMask, simplexSlice_empty_of_neg hH]

/-- Both the empty case and the singleton boundary case integrate to zero. -/
theorem simplexSlice_integral_zero_of_nonpos {H : ℝ} (hH : H ≤ 0)
    (f : (Fin 2 → ℝ) → ℝ) :
    (∫ r, (simplexSlice H).indicator f r) = 0 := by
  have hn : volume (simplexSlice H) = 0 := by
    rcases lt_or_eq_of_le hH with h | h
    · rw [simplexSlice_empty_of_neg h, measure_empty]
    · rw [h, simplexSlice_zero, measure_singleton]
  apply integral_eq_zero_of_ae
  filter_upwards [compl_mem_ae_iff.mpr hn] with r hr
  exact Set.indicator_of_notMem hr f

/-- Geometric eight-mask formula, in the exact evaluator order. -/
theorem boundedSimplexSlice_integral_simplex {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : ℝ)
    (f : (Fin 2 → ℝ) → ℝ) (hf : Continuous f) :
    (∫ r, (boundedSimplexSlice a b c H).indicator f r) =
      ∑ mask : Fin 8, simplexMaskSign mask *
        ∫ r, (simplexSlice (H-simplexMaskShift a b c mask)).indicator
          (fun r => f (simplexMaskTranslate a b mask r)) r := by
  rw [boundedSimplexSlice_integral_of_continuous a b c H f hf]
  simp_rw [simplexUpperMask_integral_simplex ha hb hc]

/-- Nonpositive translated lengths give exactly the zero branch used by `dminus`. -/
theorem boundedSimplexSlice_integral_simplex_cutoff {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : ℝ)
    (f : (Fin 2 → ℝ) → ℝ) (hf : Continuous f) :
    (∫ r, (boundedSimplexSlice a b c H).indicator f r) =
      ∑ mask : Fin 8, simplexMaskSign mask *
        (if H-simplexMaskShift a b c mask ≤ 0 then 0 else
          ∫ r, (simplexSlice (H-simplexMaskShift a b c mask)).indicator
            (fun r => f (simplexMaskTranslate a b mask r)) r) := by
  rw [boundedSimplexSlice_integral_simplex ha hb hc H f hf]
  apply Finset.sum_congr rfl
  intro mask _
  by_cases hh : H-simplexMaskShift a b c mask ≤ 0
  · rw [ite_eq_left hh, simplexSlice_integral_zero_of_nonpos hh]
  · rw [ite_eq_right hh]

theorem simplexSlice_indicator_integrable (H : ℝ)
    (f : (Fin 2 → ℝ) → ℝ) (hf : Continuous f) :
    Integrable ((simplexSlice H).indicator f) := by
  exact (hf.continuousOn.integrableOn_compact (simplexSlice_compact H)).integrable_indicator
    (simplexSlice_closed H).measurableSet

/-- Fubini with precisely the `dr₁ dr₂` convention in equation (5.7). -/
theorem simplexSlice_integral_fubini (H : ℝ)
    (f : (Fin 2 → ℝ) → ℝ) (hf : Continuous f) :
    (∫ r, (simplexSlice H).indicator f r) =
      ∫ x, ∫ y, (simplexSlice H).indicator f ![x,y] := by
  rw [integral_pi_eq_iterated 2 _ (simplexSlice_indicator_integrable H f hf)]
  simp only [finiteIteratedIntegral]
  rfl

theorem simplexSlice_nested_indicator (H x y : ℝ)
    (f : (Fin 2 → ℝ) → ℝ) :
    (simplexSlice H).indicator f ![x,y] =
      (Set.Icc 0 H).indicator (fun x =>
        (Set.Icc 0 (H-x)).indicator (fun y => f ![x,y]) y) x := by
  classical
  have hm : (![x,y] : Fin 2 → ℝ) ∈ simplexSlice H ↔
      x ∈ Set.Icc 0 H ∧ y ∈ Set.Icc 0 (H-x) := by
    change (0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ H-x-y) ↔ _
    simp only [Set.mem_Icc]
    constructor
    · rintro ⟨hx, hy, hxy⟩
      constructor <;> constructor <;> linarith
    · rintro ⟨⟨hx, hxH⟩, ⟨hy, hyH⟩⟩
      constructor
      · exact hx
      · constructor
        · exact hy
        · linarith
  rw [Set.indicator_apply, hm]
  simp only [Set.indicator_apply]
  by_cases hx : x ∈ Set.Icc 0 H
  <;> by_cases hy : y ∈ Set.Icc 0 (H-x)
  <;> simp only [hx, hy, and_true, and_false, ite_true, ite_false]

theorem simplex_interval_indicator_integral (a b : ℝ) (f : ℝ → ℝ) (hab : a ≤ b) :
    (∫ x, (Set.Icc a b).indicator f x) = ∫ x in a..b, f x := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

/-- The slice Lebesgue integral equals the iterated triangle integral. -/
theorem simplexSlice_integral_iterated {H : ℝ} (hH : 0 ≤ H)
    (f : (Fin 2 → ℝ) → ℝ) (hf : Continuous f) :
    (∫ r, (simplexSlice H).indicator f r) =
      ∫ x in (0 : ℝ)..H, ∫ y in (0 : ℝ)..H-x, f ![x,y] := by
  rw [simplexSlice_integral_fubini H f hf]
  simp_rw [simplexSlice_nested_indicator, integral_indicator₂]
  rw [simplex_interval_indicator_integral 0 H _ hH]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [Set.uIcc_of_le hH] at hx
  exact simplex_interval_indicator_integral 0 (H-x) _ (sub_nonneg.mpr hx.2)

/-- Equation (5.7), now for the actual two-dimensional Lebesgue slice measure. -/
theorem simplexSlice_monomial_integral {H : ℝ} (hH : 0 ≤ H) (i j k : ℕ) :
    (∫ r, (simplexSlice H).indicator
      (fun r => r 0^i*r 1^j*(H-r 0-r 1)^k) r) =
      (Nat.factorial i : ℝ)*Nat.factorial j*Nat.factorial k /
        Nat.factorial (i+j+k+2) * H^(i+j+k+2) := by
  rw [simplexSlice_integral_iterated hH _ (by fun_prop)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact simplex_monomial_two H i j k

/-- The monomial evaluator, including its exact nonpositive-length cutoff. -/
theorem simplexSlice_monomial_integral_cutoff (H : ℝ) (i j k : ℕ) :
    (∫ r, (simplexSlice H).indicator
      (fun r => r 0^i*r 1^j*(H-r 0-r 1)^k) r) =
      if H ≤ 0 then 0 else
        (Nat.factorial i : ℝ)*Nat.factorial j*Nat.factorial k /
          Nat.factorial (i+j+k+2) * H^(i+j+k+2) := by
  by_cases hH : H ≤ 0
  · rw [ite_eq_left hH, simplexSlice_integral_zero_of_nonpos hH]
  · rw [ite_eq_right hH]
    exact simplexSlice_monomial_integral (le_of_lt (lt_of_not_ge hH)) i j k

end Sechstmoment
