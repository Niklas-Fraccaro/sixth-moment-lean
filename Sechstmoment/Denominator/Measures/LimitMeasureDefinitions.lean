import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Regular
import Sechstmoment.Denominator.Measures.DiagonalMeasureDefinitions

/-! The geometric D01 limit is the push-forward of nine-dimensional positive
Lebesgue measure under the three row and three column sums. -/
namespace Sechstmoment
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 0

def d01NonnegativeOrthant : Set D01EdgeSpace := {x | ∀ ij, 0 ≤ x ij}

def d01RowColumnSums (x : D01EdgeSpace) : D01LogSpace :=
  (fun i => ∑ j, x (i,j), fun j => ∑ i, x (i,j))

def d01EdgeMeasure : Measure D01EdgeSpace := volume.restrict d01NonnegativeOrthant

def d01LimitMeasure : Measure D01LogSpace :=
  ENNReal.ofReal arithmeticFactor • Measure.map d01RowColumnSums d01EdgeMeasure

theorem d01NonnegativeOrthant_measurable : MeasurableSet d01NonnegativeOrthant := by
  have he : d01NonnegativeOrthant = ⋂ ij : Fin 3 × Fin 3, {x : D01EdgeSpace | 0 ≤ x ij} := by
    ext x
    simp [d01NonnegativeOrthant]
  rw [he]
  exact (isClosed_iInter fun ij => isClosed_le continuous_const (continuous_apply ij)).measurableSet

theorem d01RowColumnSums_continuous : Continuous d01RowColumnSums := by
  unfold d01RowColumnSums
  fun_prop

theorem d01RowColumnSums_nonnegative {x : D01EdgeSpace} (hx : x ∈ d01NonnegativeOrthant) :
    (∀ i, 0 ≤ (d01RowColumnSums x).1 i) ∧ (∀ j, 0 ≤ (d01RowColumnSums x).2 j) := by
  change (∀ i, 0 ≤ ∑ j, x (i,j)) ∧ (∀ j, 0 ≤ ∑ i, x (i,j))
  constructor <;> intro i <;> apply Finset.sum_nonneg <;> intro j _ <;> exact hx _

theorem d01RowColumnSums_total (x : D01EdgeSpace) :
    ∑ i, (d01RowColumnSums x).1 i = ∑ j, (d01RowColumnSums x).2 j := by
  change (∑ i, ∑ j, x (i,j)) = ∑ j, ∑ i, x (i,j)
  exact Finset.sum_comm

theorem d01EdgeMeasure_pi : d01EdgeMeasure =
    Measure.pi (fun _ : Fin 3 × Fin 3 => volume.restrict (Ici (0:ℝ))) := by
  unfold d01EdgeMeasure d01NonnegativeOrthant
  change (Measure.pi (fun _ : Fin 3 × Fin 3 => (volume : Measure ℝ))).restrict
    {x | ∀ ij, 0 ≤ x ij} = _
  rw [show {x : D01EdgeSpace | ∀ ij, 0 ≤ x ij} =
    Set.univ.pi (fun _ : Fin 3 × Fin 3 => Ici (0:ℝ)) by
      ext x
      change (∀ ij, 0 ≤ x ij) ↔ ∀ ij ∈ (Set.univ : Set (Fin 3 × Fin 3)), 0 ≤ x ij
      simp only [Set.mem_univ, forall_true_left]]
  exact Measure.restrict_pi_pi _ _

theorem d01LimitMeasure_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : D01LogSpace → E} (hf : StronglyMeasurable f) :
    (∫ y, f y ∂d01LimitMeasure) = arithmeticFactor •
      ∫ x, f (d01RowColumnSums x) ∂d01EdgeMeasure := by
  rw [d01LimitMeasure, integral_smul_measure,
    integral_map_of_stronglyMeasurable d01RowColumnSums_continuous.measurable hf,
    ENNReal.toReal_ofReal arithmeticFactor_wellDefined.2.le]

theorem d01LimitMeasure_ae_orthant : ∀ᵐ y ∂d01LimitMeasure, y ∈ d01PositiveOrthant := by
  unfold d01LimitMeasure
  apply Measure.ae_smul_measure
  apply (ae_map_iff d01RowColumnSums_continuous.measurable.aemeasurable
    d01PositiveOrthant_isClosed.measurableSet).mpr
  filter_upwards [ae_restrict_mem d01NonnegativeOrthant_measurable] with x hx
  exact d01RowColumnSums_nonnegative hx

theorem d01LimitMeasure_ae_equal_totals :
    ∀ᵐ y ∂d01LimitMeasure, (∑ i, y.1 i) = ∑ j, y.2 j := by
  unfold d01LimitMeasure
  apply Measure.ae_smul_measure
  apply (ae_map_iff d01RowColumnSums_continuous.measurable.aemeasurable
    (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet).mpr
  exact ae_of_all _ d01RowColumnSums_total

end
end Sechstmoment
