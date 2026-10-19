import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Sechstmoment.Certificate.Kernels.Balanced.Coordinates

namespace Sechstmoment
open MeasureTheory

noncomputable def denominatorCoordinateMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,1,1,1; 1,1,0,0; 1,0,1,0; 1,0,0,0]

noncomputable def denominatorCoordinateChange : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
  Matrix.toLin' denominatorCoordinateMatrix

theorem denominatorCoordinateMatrix_det : denominatorCoordinateMatrix.det = -1 := by
  norm_num [denominatorCoordinateMatrix, Matrix.det_succ_row_zero,
    Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]

theorem denominatorCoordinateChange_apply (v : Fin 4 → ℝ) :
    denominatorCoordinateChange v =
      ![v 0+v 1+v 2+v 3, v 0+v 1, v 0+v 2, v 0] := by
  funext i
  fin_cases i <;> simp [denominatorCoordinateChange, denominatorCoordinateMatrix,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]

theorem denominatorCoordinateChange_measurePreserving :
    MeasurePreserving denominatorCoordinateChange volume volume := by
  refine ⟨denominatorCoordinateChange.continuous_of_finiteDimensional.measurable, ?_⟩
  have hd : denominatorCoordinateMatrix.det ≠ 0 := by rw [denominatorCoordinateMatrix_det]; norm_num
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hd
  simpa [denominatorCoordinateChange, denominatorCoordinateMatrix_det] using h

noncomputable def denominatorCoordinateHomeomorph : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toFun := denominatorCoordinateChange
  invFun := fun w => ![w 3,w 1-w 3,w 2-w 3,w 0-w 1-w 2+w 3]
  left_inv := by
    intro v
    simp only [denominatorCoordinateChange_apply]
    funext i
    fin_cases i
    · simp
    · simp
    · simp
    · simp
      ring
  right_inv := by
    intro w
    rw [denominatorCoordinateChange_apply]
    funext i
    fin_cases i
    · simp
      ring
    · simp
    · simp
    · simp
  continuous_toFun := denominatorCoordinateChange.continuous_of_finiteDimensional
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

theorem denominator_coordinate_integral (f : (Fin 4 → ℝ) → ℝ) :
    (∫ v, f (denominatorCoordinateChange v)) = ∫ w, f w :=
  denominatorCoordinateChange_measurePreserving.integral_comp
    denominatorCoordinateHomeomorph.measurableEmbedding f

end Sechstmoment
