import Mathlib.MeasureTheory.Measure.Regular
import Sechstmoment.Denominator.Measures.DiagonalLaplaceTransform

/-! Finiteness of the actual positive exponential tilts and local finiteness
of the literal arithmetic diagonal measure. -/

namespace Sechstmoment
open MeasureTheory Set
open scoped BigOperators Topology ENNReal
noncomputable section
set_option maxHeartbeats 0

theorem d01AtomicWeight_nonpos {L : ℝ} (hL : L ≤ 0) (x : DiagonalSixIndices) :
    d01AtomicWeight L x ≤ 0 := by
  unfold d01AtomicWeight
  apply div_nonpos_of_nonpos_of_nonneg
  · exact (show Odd (9 : ℕ) by decide).pow_nonpos (inv_nonpos.mpr hL)
  · exact Nat.cast_nonneg _

theorem d01DiagonalMeasure_eq_zero_of_nonpos {L : ℝ} (hL : L ≤ 0) :
    d01DiagonalMeasure L = 0 := by
  unfold d01DiagonalMeasure
  have hw (x : DiagonalSixIndices) : ENNReal.ofReal (d01AtomicWeight L x) = 0 :=
    ENNReal.ofReal_eq_zero.mpr (d01AtomicWeight_nonpos hL x)
  simp only [hw, zero_smul, Measure.sum_zero]

theorem d01_locallyFinite_of_positive_continuous_integrable
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hc : Continuous f) (hp : ∀ x, 0 < f x)
    (hi : Integrable f μ) : IsLocallyFiniteMeasure μ := by
  constructor
  intro x
  refine ⟨{y | f x / 2 < f y}, ?_, ?_⟩
  · exact (isOpen_lt continuous_const hc).mem_nhds (by
      have h := hp x
      dsimp
      linarith)
  · apply lt_of_le_of_lt (measure_mono ?_) (hi.measure_norm_gt_lt_top (by
      exact div_pos (hp x) (by norm_num) : 0 < f x / 2))
    intro y hy
    change f x / 2 < ‖f y‖
    exact hy.trans_le (le_abs_self (f y))

theorem d01DiagonalMeasure_finite_laplace_density {L : ℝ} (hL : 0 < L)
    (ab : D01LogSpace) (ha : ∀ i, 0 < ab.1 i) (hb : ∀ j, 0 < ab.2 j) :
    IsFiniteMeasure ((d01DiagonalMeasure L).withDensity
      (fun y => ENNReal.ofReal (d01LaplaceWeight ab y))) :=
  isFiniteMeasure_withDensity_ofReal (d01LaplaceWeight_integrable hL ab ha hb).2

theorem d01DiagonalMeasure_locallyFinite {L : ℝ} (hL : 0 < L) :
    IsLocallyFiniteMeasure (d01DiagonalMeasure L) :=
  d01_locallyFinite_of_positive_continuous_integrable (d01DiagonalMeasure L)
    (d01LaplaceWeight ((fun _ => 1), (fun _ => 1)))
    (d01LaplaceWeight_continuous _) (d01LaplaceWeight_pos _)
    (d01LaplaceWeight_integrable hL _ (by intro i; norm_num) (by intro j; norm_num))

theorem d01DiagonalMeasure_finiteOnCompacts {L : ℝ} (hL : 0 < L) :
    IsFiniteMeasureOnCompacts (d01DiagonalMeasure L) := by
  let := d01DiagonalMeasure_locallyFinite hL
  infer_instance

theorem d01DiagonalMeasure_regular {L : ℝ} (hL : 0 < L) :
    (d01DiagonalMeasure L).Regular := by
  let := d01DiagonalMeasure_locallyFinite hL
  infer_instance

theorem d01DiagonalMeasure_compact_test_integrable {L : ℝ} (hL : 0 < L)
    {E : Type*} [NormedAddCommGroup E] (f : D01LogSpace → E)
    (hf : Continuous f) (hK : HasCompactSupport f) :
    Integrable f (d01DiagonalMeasure L) := by
  let := d01DiagonalMeasure_finiteOnCompacts hL
  exact hf.integrable_of_hasCompactSupport hK

end
end Sechstmoment
