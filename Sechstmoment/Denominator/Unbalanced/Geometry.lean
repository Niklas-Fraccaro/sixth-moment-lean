import Mathlib.Tactic
import Sechstmoment.Certificate.Kernels.Unbalanced.Kernel
import Sechstmoment.Denominator.Measures.LimitMeasureDefinitions

/-! Literal nine-edge coordinates for the unbalanced three-to-one slice.
The third-column edges form the original two-coordinate simplex slice; the
first-column edges independently split the three residual row masses. -/
namespace Sechstmoment
open Set
open scoped BigOperators
noncomputable section

/-- The four original profile vertices: all three rows and the last column. -/
def d04UnbalancedProfileCoordinates (x : D01EdgeSpace) : Fin 4 → ℝ :=
  ![(d01RowColumnSums x).1 0,(d01RowColumnSums x).1 1,
    (d01RowColumnSums x).1 2,(d01RowColumnSums x).2 2]

def d04UnbalancedSliceEdges (x : D01EdgeSpace) : Fin 2 → ℝ := ![x (0,2),x (1,2)]
def d04UnbalancedSplitEdges (x : D01EdgeSpace) : Fin 3 → ℝ := ![x (0,0),x (1,0),x (2,0)]

def d04UnbalancedResiduals (a b c d : ℝ) (u : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![a-u 0,b-u 1,c-(d-u 0-u 1)]

def d04UnbalancedEdges (a b c d : ℝ) (u : Fin 2 → ℝ) (y : Fin 3 → ℝ) : D01EdgeSpace :=
  fun ij =>
    (![![y 0,a-u 0-y 0,u 0],
       ![y 1,b-u 1-y 1,u 1],
       ![y 2,c-(d-u 0-u 1)-y 2,d-u 0-u 1]] : Fin 3 → Fin 3 → ℝ) ij.1 ij.2

theorem d04UnbalancedEdges_rowColumnSums (a b c d : ℝ) (u : Fin 2 → ℝ) (y : Fin 3 → ℝ) :
    d01RowColumnSums (d04UnbalancedEdges a b c d u y) =
      (![a,b,c],![y 0+y 1+y 2,a+b+c-d-(y 0+y 1+y 2),d]) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [d01RowColumnSums,d04UnbalancedEdges,Fin.sum_univ_succ] <;> ring

theorem d04UnbalancedProfileCoordinates_edges (a b c d : ℝ) (u : Fin 2 → ℝ)
    (y : Fin 3 → ℝ) :
    d04UnbalancedProfileCoordinates (d04UnbalancedEdges a b c d u y) = ![a,b,c,d] := by
  unfold d04UnbalancedProfileCoordinates
  rw [d04UnbalancedEdges_rowColumnSums]
  rfl

@[simp] theorem d04UnbalancedEdges_slice (a b c d : ℝ) (u : Fin 2 → ℝ) (y : Fin 3 → ℝ) :
    d04UnbalancedSliceEdges (d04UnbalancedEdges a b c d u y) = u := by
  funext i
  fin_cases i <;> simp [d04UnbalancedSliceEdges,d04UnbalancedEdges]

@[simp] theorem d04UnbalancedEdges_split (a b c d : ℝ) (u : Fin 2 → ℝ) (y : Fin 3 → ℝ) :
    d04UnbalancedSplitEdges (d04UnbalancedEdges a b c d u y) = y := by
  funext i
  fin_cases i <;> simp [d04UnbalancedSplitEdges,d04UnbalancedEdges]

theorem d04UnbalancedEdges_reconstruct (x : D01EdgeSpace) :
    d04UnbalancedEdges ((d01RowColumnSums x).1 0) ((d01RowColumnSums x).1 1)
      ((d01RowColumnSums x).1 2) ((d01RowColumnSums x).2 2)
      (d04UnbalancedSliceEdges x) (d04UnbalancedSplitEdges x) = x := by
  funext ij
  rcases ij with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [d04UnbalancedEdges,d04UnbalancedSliceEdges,d04UnbalancedSplitEdges,
      d01RowColumnSums,Fin.sum_univ_succ] <;> ring

theorem d04UnbalancedEdges_nonnegative_iff (a b c d : ℝ) (u : Fin 2 → ℝ)
    (y : Fin 3 → ℝ) :
    d04UnbalancedEdges a b c d u y ∈ d01NonnegativeOrthant ↔
      u∈boundedSimplexSlice a b c d ∧
        y∈Icc (fun _ => 0) (d04UnbalancedResiduals a b c d u) := by
  constructor
  · intro h
    have h00 := h (0,0); have h01 := h (0,1); have h02 := h (0,2)
    have h10 := h (1,0); have h11 := h (1,1); have h12 := h (1,2)
    have h20 := h (2,0); have h21 := h (2,1); have h22 := h (2,2)
    simp [d04UnbalancedEdges] at h00 h01 h02 h10 h11 h12 h20 h21 h22
    constructor
    · simp only [boundedSimplexSlice,simplexSlice,mem_ofPred_eq]
      exact ⟨⟨h02,h12,by linarith⟩,by linarith,by linarith,by linarith⟩
    · constructor <;> intro i <;> fin_cases i <;>
        simp [d04UnbalancedResiduals] <;> linarith
  · rintro ⟨hu,hy⟩
    rcases hu with ⟨⟨hu0,hu1,hu2⟩,hcap0,hcap1,hcap2⟩
    have hy0 := hy.1 0; have hy1 := hy.1 1; have hy2 := hy.1 2
    have hY0 := hy.2 0; have hY1 := hy.2 1; have hY2 := hy.2 2
    simp [d04UnbalancedResiduals] at hY0 hY1 hY2
    rintro ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [d04UnbalancedEdges] <;> linarith

theorem d04UnbalancedResiduals_nonnegative {a b c d : ℝ} {u : Fin 2 → ℝ}
    (hu : u∈boundedSimplexSlice a b c d) : ∀ i, 0≤d04UnbalancedResiduals a b c d u i := by
  intro i
  fin_cases i <;> simp [d04UnbalancedResiduals] <;> linarith [hu.2.1,hu.2.2.1,hu.2.2.2]

/-- Translation centers each independent split interval without changing dx. -/
def d04UnbalancedCenteredSplit (a b c d : ℝ) (_u : Fin 2 → ℝ) (y : Fin 3 → ℝ) : ℝ :=
  y 0+y 1+y 2-(minusKernelH a b c d)/2

theorem d04UnbalancedEdges_centered_arguments (a b c d : ℝ) (u : Fin 2 → ℝ)
    (y : Fin 3 → ℝ) :
    ((d01RowColumnSums (d04UnbalancedEdges a b c d u y)).2 0-1/2,
      1/2-(d01RowColumnSums (d04UnbalancedEdges a b c d u y)).2 1) =
      (d04UnbalancedCenteredSplit a b c d u y-minusKernelT0 a b c d,
       d04UnbalancedCenteredSplit a b c d u y+minusKernelT0 a b c d) := by
  rw [d04UnbalancedEdges_rowColumnSums]
  simp [d04UnbalancedCenteredSplit,minusKernelH,minusKernelT0]
  constructor <;> ring

end
end Sechstmoment
