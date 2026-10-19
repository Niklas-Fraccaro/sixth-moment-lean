import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Sechstmoment.Certificate.Kernels.Balanced.CoordinateMeasure

namespace Sechstmoment
open MeasureTheory

def denominatorRegion (a b c d : ℝ) : Set (Fin 4 → ℝ) :=
  {v | 0 ≤ v 0 ∧ 0 ≤ v 1 ∧ 0 ≤ v 2 ∧ 0 ≤ v 3 ∧
    v 0+v 1 ≤ a ∧ v 2+v 3 ≤ b ∧ v 0+v 2 ≤ c ∧ v 1+v 3 ≤ d}

def denominatorCoordinateRegion (a b c d : ℝ) : Set (Fin 4 → ℝ) :=
  {w | 0 ≤ w 0 ∧ w 0 ≤ min (a+b) (c+d) ∧
    max 0 (w 0-b) ≤ w 1 ∧ w 1 ≤ min a (w 0) ∧
    max 0 (w 0-d) ≤ w 2 ∧ w 2 ≤ min c (w 0) ∧
    max 0 (w 1+w 2-w 0) ≤ w 3 ∧ w 3 ≤ min (w 1) (w 2)}

theorem denominatorRegion_closed (a b c d : ℝ) : IsClosed (denominatorRegion a b c d) := by
  unfold denominatorRegion
  simp only [Set.ofPred_and]
  repeat' apply IsClosed.inter
  all_goals apply isClosed_le <;> fun_prop

theorem denominatorCoordinateRegion_closed (a b c d : ℝ) :
    IsClosed (denominatorCoordinateRegion a b c d) := by
  unfold denominatorCoordinateRegion
  simp only [Set.ofPred_and]
  repeat' apply IsClosed.inter
  all_goals apply isClosed_le <;> fun_prop

theorem denominatorRegion_coordinate_preimage (a b c d : ℝ) :
    denominatorRegion a b c d =
      denominatorCoordinateChange ⁻¹' denominatorCoordinateRegion a b c d := by
  ext v
  dsimp [denominatorRegion, denominatorCoordinateRegion]
  rw [denominatorCoordinateChange_apply]
  dsimp
  have hi := denominator_coordinates_iff a b c d
    (v 0+v 1+v 2+v 3) (v 0+v 1) (v 0+v 2) (v 0)
  ring_nf at hi ⊢
  exact hi

theorem denominator_region_integral_coordinate_change (f : (Fin 4 → ℝ) → ℝ)
    (a b c d : ℝ) :
    (∫ v in denominatorRegion a b c d, f (denominatorCoordinateChange v)) =
      ∫ w in denominatorCoordinateRegion a b c d, f w := by
  rw [← integral_indicator (denominatorRegion_closed a b c d).measurableSet,
    ← integral_indicator (denominatorCoordinateRegion_closed a b c d).measurableSet]
  have he (v : Fin 4 → ℝ) :
      (denominatorRegion a b c d).indicator (fun v => f (denominatorCoordinateChange v)) v =
      (denominatorCoordinateRegion a b c d).indicator f (denominatorCoordinateChange v) := by
    rw [denominatorRegion_coordinate_preimage]
    rfl
  calc
    (∫ v, (denominatorRegion a b c d).indicator (fun v => f (denominatorCoordinateChange v)) v) =
      ∫ v, (denominatorCoordinateRegion a b c d).indicator f (denominatorCoordinateChange v) :=
        integral_congr_ae (Filter.Eventually.of_forall he)
    _ = _ := denominator_coordinate_integral _

end Sechstmoment
