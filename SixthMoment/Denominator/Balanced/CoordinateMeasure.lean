import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import SixthMoment.Denominator.Balanced.Geometry


namespace SixthMoment
open MeasureTheory Set
open scoped BigOperators
noncomputable section

abbrev D02SliceCoordinateSpace := Fin 5 ⊕ Fin 4 → ℝ

def d02SliceEdgeIndex : Fin 5 ⊕ Fin 4 → Fin 3 × Fin 3 :=
  Sum.elim ![(0,0),(1,0),(2,0),(0,1),(0,2)] ![(1,1),(1,2),(2,1),(2,2)]

def d02SliceEdgeEquiv : (Fin 5 ⊕ Fin 4) ≃ (Fin 3 × Fin 3) :=
  Equiv.ofBijective d02SliceEdgeIndex (by decide)

def d02SliceReindex : D01EdgeSpace ≃ᵐ D02SliceCoordinateSpace :=
  MeasurableEquiv.arrowCongr' d02SliceEdgeEquiv.symm (MeasurableEquiv.refl ℝ)

@[simp] theorem d02SliceReindex_apply (x : D01EdgeSpace) (k : Fin 5 ⊕ Fin 4) :
    d02SliceReindex x k = x (d02SliceEdgeIndex k) := rfl

theorem d02SliceReindex_measurePreserving : MeasurePreserving d02SliceReindex volume volume :=
  volume_preserving_arrowCongr' d02SliceEdgeEquiv.symm (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id _)

def d02SliceIncidence : Matrix (Fin 5) (Fin 4) ℝ :=
  !![0,0,0,0; 1,1,0,0; 0,0,1,1; 1,0,1,0; 0,1,0,1]

def d02SliceShearMatrix : Matrix (Fin 5 ⊕ Fin 4) (Fin 5 ⊕ Fin 4) ℝ :=
  Matrix.fromBlocks 1 d02SliceIncidence 0 1

theorem d02SliceShearMatrix_det : d02SliceShearMatrix.det = 1 := by
  simp [d02SliceShearMatrix]

def d02SliceShear : D02SliceCoordinateSpace →ₗ[ℝ] D02SliceCoordinateSpace :=
  Matrix.toLin' d02SliceShearMatrix

theorem d02SliceShear_measurePreserving : MeasurePreserving d02SliceShear volume volume := by
  refine ⟨d02SliceShear.continuous_of_finiteDimensional.measurable, ?_⟩
  have hd : d02SliceShearMatrix.det ≠ 0 := by rw [d02SliceShearMatrix_det]; norm_num
  simpa [d02SliceShear,d02SliceShearMatrix_det] using
    Real.map_matrix_volume_pi_eq_smul_volume_pi hd

def d02SliceCoordinateChange (x : D01EdgeSpace) : D02SliceCoordinateSpace :=
  d02SliceShear (d02SliceReindex x)

theorem d02SliceCoordinateChange_apply (x : D01EdgeSpace) :
    d02SliceCoordinateChange x =
      Sum.elim ![x (0,0),(d01RowColumnSums x).1 1,(d01RowColumnSums x).1 2,
        (d01RowColumnSums x).2 1,(d01RowColumnSums x).2 2] (d02InteriorEdges x) := by
  funext k
  cases k with
  | inl i =>
      fin_cases i <;>
        simp [d02SliceCoordinateChange,d02SliceShear,Matrix.toLin'_apply,Matrix.mulVec,
          dotProduct,d02SliceShearMatrix,d02SliceIncidence,Fintype.sum_sum_type,
          Fin.sum_univ_succ,d02SliceEdgeIndex,d01RowColumnSums,d02InteriorEdges] <;>
          norm_num [Matrix.one_apply]
  | inr i =>
      fin_cases i <;>
        simp [d02SliceCoordinateChange,d02SliceShear,Matrix.toLin'_apply,Matrix.mulVec,
          dotProduct,d02SliceShearMatrix,d02SliceIncidence,Fintype.sum_sum_type,
          Fin.sum_univ_succ,d02SliceEdgeIndex,d01RowColumnSums,d02InteriorEdges] <;>
          norm_num [Matrix.one_apply]

theorem d02SliceCoordinateChange_measurePreserving :
    MeasurePreserving d02SliceCoordinateChange volume volume :=
  d02SliceShear_measurePreserving.comp d02SliceReindex_measurePreserving

def d02SliceReconstruct (q : D02SliceCoordinateSpace) : D01EdgeSpace :=
  d02BalancedEdges (q (.inl 1)) (q (.inl 2)) (q (.inl 3)) (q (.inl 4))
    (fun i => q (.inr i)) (q (.inl 0))

theorem d02SliceReconstruct_change (x : D01EdgeSpace) :
    d02SliceReconstruct (d02SliceCoordinateChange x) = x := by
  rw [d02SliceCoordinateChange_apply]
  exact d02BalancedEdges_reconstruct x

theorem d02SliceChange_reconstruct (q : D02SliceCoordinateSpace) :
    d02SliceCoordinateChange (d02SliceReconstruct q) = q := by
  rw [d02SliceCoordinateChange_apply]
  unfold d02SliceReconstruct
  rw [d02BalancedEdges_rowColumnSums,d02BalancedEdges_interior,d02BalancedEdges_origin]
  funext k
  cases k with
  | inl i => fin_cases i <;> simp
  | inr i => simp

def d02SliceCoordinateHomeomorph : D01EdgeSpace ≃ₜ D02SliceCoordinateSpace where
  toFun := d02SliceCoordinateChange
  invFun := d02SliceReconstruct
  left_inv := d02SliceReconstruct_change
  right_inv := d02SliceChange_reconstruct
  continuous_toFun := by
    apply continuous_pi
    intro k
    simp_rw [d02SliceCoordinateChange_apply]
    cases k with
    | inl i => fin_cases i <;> simp [d01RowColumnSums] <;> fun_prop
    | inr i => fin_cases i <;> simp [d02InteriorEdges] <;> fun_prop
  continuous_invFun := by
    apply continuous_pi
    rintro ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [d02SliceReconstruct,d02BalancedEdges] <;> fun_prop

theorem d02SliceCoordinate_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : D02SliceCoordinateSpace → E) :
    (∫ x : D01EdgeSpace, f (d02SliceCoordinateChange x)) = ∫ q, f q :=
  d02SliceCoordinateChange_measurePreserving.integral_comp
    d02SliceCoordinateHomeomorph.measurableEmbedding f

theorem d02SliceReconstruct_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : D01EdgeSpace → E) :
    (∫ x : D01EdgeSpace, f x) = ∫ q, f (d02SliceReconstruct q) := by
  simpa only [d02SliceReconstruct_change] using
    d02SliceCoordinate_integral (fun q => f (d02SliceReconstruct q))

end
end SixthMoment
