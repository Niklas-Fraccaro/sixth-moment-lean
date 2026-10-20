import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import SixthMoment.Denominator.Unbalanced.Geometry

namespace SixthMoment
open MeasureTheory Set
open scoped BigOperators
noncomputable section

abbrev D04SliceCoordinateSpace := Fin 4 ⊕ Fin 5 → ℝ

def d04SliceEdgeIndex : Fin 4 ⊕ Fin 5 → Fin 3 × Fin 3 :=
  Sum.elim ![(0,1),(1,1),(2,1),(2,2)] ![(0,2),(1,2),(0,0),(1,0),(2,0)]
def d04SliceEdgeEquiv : (Fin 4 ⊕ Fin 5) ≃ (Fin 3 × Fin 3) :=
  Equiv.ofBijective d04SliceEdgeIndex (by decide)
def d04SliceReindex : D01EdgeSpace ≃ᵐ D04SliceCoordinateSpace :=
  MeasurableEquiv.arrowCongr' d04SliceEdgeEquiv.symm (MeasurableEquiv.refl ℝ)

@[simp] theorem d04SliceReindex_apply (x : D01EdgeSpace) (k : Fin 4 ⊕ Fin 5) :
    d04SliceReindex x k = x (d04SliceEdgeIndex k) := rfl

theorem d04SliceReindex_measurePreserving : MeasurePreserving d04SliceReindex volume volume :=
  volume_preserving_arrowCongr' d04SliceEdgeEquiv.symm (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id _)

def d04SliceEndpointMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,0,0,0; 0,1,0,0; 0,0,1,1; 0,0,0,1]
def d04SliceIncidence : Matrix (Fin 4) (Fin 5) ℝ :=
  !![1,0,1,0,0; 0,1,0,1,0; 0,0,0,0,1; 1,1,0,0,0]
def d04SliceShearMatrix : Matrix (Fin 4 ⊕ Fin 5) (Fin 4 ⊕ Fin 5) ℝ :=
  Matrix.fromBlocks d04SliceEndpointMatrix d04SliceIncidence 0 1

theorem d04SliceEndpointMatrix_det : d04SliceEndpointMatrix.det = 1 := by
  have hu : d04SliceEndpointMatrix.IsUpperTriangular := by
    intro i j hji
    fin_cases i <;> fin_cases j <;> simp_all [d04SliceEndpointMatrix]
  rw [Matrix.det_of_isUpperTriangular hu]
  norm_num [d04SliceEndpointMatrix,Fin.prod_univ_succ]

theorem d04SliceShearMatrix_det : d04SliceShearMatrix.det = 1 := by
  simp [d04SliceShearMatrix,d04SliceEndpointMatrix_det]

def d04SliceShear : D04SliceCoordinateSpace →ₗ[ℝ] D04SliceCoordinateSpace :=
  Matrix.toLin' d04SliceShearMatrix

theorem d04SliceShear_measurePreserving : MeasurePreserving d04SliceShear volume volume := by
  refine ⟨d04SliceShear.continuous_of_finiteDimensional.measurable, ?_⟩
  have hd : d04SliceShearMatrix.det ≠ 0 := by rw [d04SliceShearMatrix_det]; norm_num
  simpa [d04SliceShear,d04SliceShearMatrix_det] using
    Real.map_matrix_volume_pi_eq_smul_volume_pi hd

def d04SliceCoordinateChange (x : D01EdgeSpace) : D04SliceCoordinateSpace :=
  d04SliceShear (d04SliceReindex x)

theorem d04SliceCoordinateChange_apply (x : D01EdgeSpace) :
    d04SliceCoordinateChange x = Sum.elim (d04UnbalancedProfileCoordinates x)
      ![x (0,2),x (1,2),x (0,0),x (1,0),x (2,0)] := by
  funext k
  cases k with
  | inl i =>
      fin_cases i <;>
        simp [d04SliceCoordinateChange,d04SliceShear,Matrix.toLin'_apply,Matrix.mulVec,
          dotProduct,d04SliceShearMatrix,d04SliceEndpointMatrix,d04SliceIncidence,
          Fintype.sum_sum_type,Fin.sum_univ_succ,d04SliceEdgeIndex,
          d04UnbalancedProfileCoordinates,d01RowColumnSums] <;> ring
  | inr i =>
      fin_cases i <;>
        simp [d04SliceCoordinateChange,d04SliceShear,Matrix.toLin'_apply,Matrix.mulVec,
          dotProduct,d04SliceShearMatrix,d04SliceEndpointMatrix,d04SliceIncidence,
          Fintype.sum_sum_type,Fin.sum_univ_succ,d04SliceEdgeIndex,
          d04UnbalancedProfileCoordinates,d01RowColumnSums,Matrix.one_apply]

theorem d04SliceCoordinateChange_measurePreserving :
    MeasurePreserving d04SliceCoordinateChange volume volume :=
  d04SliceShear_measurePreserving.comp d04SliceReindex_measurePreserving

def d04SliceReconstruct (q : D04SliceCoordinateSpace) : D01EdgeSpace :=
  d04UnbalancedEdges (q (.inl 0)) (q (.inl 1)) (q (.inl 2)) (q (.inl 3))
    ![q (.inr 0),q (.inr 1)] ![q (.inr 2),q (.inr 3),q (.inr 4)]

theorem d04SliceReconstruct_change (x : D01EdgeSpace) :
    d04SliceReconstruct (d04SliceCoordinateChange x) = x := by
  rw [d04SliceCoordinateChange_apply]
  exact d04UnbalancedEdges_reconstruct x

theorem d04SliceChange_reconstruct (q : D04SliceCoordinateSpace) :
    d04SliceCoordinateChange (d04SliceReconstruct q) = q := by
  rw [d04SliceCoordinateChange_apply]
  unfold d04SliceReconstruct
  rw [d04UnbalancedProfileCoordinates_edges]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp
  | inr i => fin_cases i <;> simp [d04UnbalancedEdges]

def d04SliceCoordinateHomeomorph : D01EdgeSpace ≃ₜ D04SliceCoordinateSpace where
  toFun := d04SliceCoordinateChange
  invFun := d04SliceReconstruct
  left_inv := d04SliceReconstruct_change
  right_inv := d04SliceChange_reconstruct
  continuous_toFun := by
    apply continuous_pi
    intro k
    simp_rw [d04SliceCoordinateChange_apply]
    cases k with
    | inl i => fin_cases i <;> simp [d04UnbalancedProfileCoordinates,d01RowColumnSums] <;> fun_prop
    | inr i => fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    apply continuous_pi
    rintro ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [d04SliceReconstruct,d04UnbalancedEdges] <;> fun_prop

theorem d04SliceCoordinate_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : D04SliceCoordinateSpace → E) :
    (∫ x : D01EdgeSpace, f (d04SliceCoordinateChange x)) = ∫ q, f q :=
  d04SliceCoordinateChange_measurePreserving.integral_comp
    d04SliceCoordinateHomeomorph.measurableEmbedding f

theorem d04SliceReconstruct_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : D01EdgeSpace → E) :
    (∫ x : D01EdgeSpace, f x) = ∫ q, f (d04SliceReconstruct q) := by
  simpa only [d04SliceReconstruct_change] using
    d04SliceCoordinate_integral (fun q => f (d04SliceReconstruct q))

end
end SixthMoment
