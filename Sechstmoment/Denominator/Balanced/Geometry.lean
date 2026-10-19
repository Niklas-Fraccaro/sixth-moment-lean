import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Sechstmoment.Certificate.Kernels.Balanced.RegionCoordinates
import Sechstmoment.Denominator.Measures.LimitMeasureDefinitions

/-! Exact nine-edge slice geometry for the balanced second AFE.  The four
profile vertices have prescribed row/column sums.  The remaining free
zeta--zeta edge is cut by the literal sum of the two zeta coordinates.
No approximate functional equation or height asymptotic is assumed here. -/

namespace Sechstmoment
open Set
open scoped BigOperators
noncomputable section

def d02ProfileSum (a b c d : ℝ) : ℝ := a+b+c+d

def d02ProfileDelta (a b c d : ℝ) : ℝ := (a+b-c-d)/2

def d02InteriorSum (R : Fin 4 → ℝ) : ℝ := R 0+R 1+R 2+R 3

def d02BalancedWidth (a b c d : ℝ) (R : Fin 4 → ℝ) : ℝ :=
  1-d02ProfileSum a b c d+2*d02InteriorSum R

/-- All nine original nonnegative edge coordinates, rather than a free
limiting kernel.  The side edges are determined by the four profile sums. -/
def d02BalancedEdges (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) : D01EdgeSpace :=
  fun ij =>
    (![![u, c-R 0-R 2, d-R 1-R 3],
       ![a-R 0-R 1, R 0, R 1],
       ![b-R 2-R 3, R 2, R 3]] : Fin 3 → Fin 3 → ℝ) ij.1 ij.2

def d02ZetaLogSum (y : D01LogSpace) : ℝ := y.1 0+y.2 0

def d02InteriorEdges (x : D01EdgeSpace) : Fin 4 → ℝ :=
  ![x (1,1),x (1,2),x (2,1),x (2,2)]

def d02DirectCoordinate (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) : ℝ :=
  u-d02BalancedWidth a b c d R/2

def d02DualCoordinate (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) : ℝ :=
  d02BalancedWidth a b c d R/2-u

theorem d02BalancedEdges_rowColumnSums (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    d01RowColumnSums (d02BalancedEdges a b c d R u) =
      (![u+c+d-d02InteriorSum R,a,b],
       ![u+a+b-d02InteriorSum R,c,d]) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [d01RowColumnSums,d02BalancedEdges,d02InteriorSum,Fin.sum_univ_succ] <;> ring

@[simp] theorem d02BalancedEdges_interior (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    d02InteriorEdges (d02BalancedEdges a b c d R u) = R := by
  funext i
  fin_cases i <;> simp [d02InteriorEdges,d02BalancedEdges]

@[simp] theorem d02BalancedEdges_origin (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    d02BalancedEdges a b c d R u (0,0) = u := rfl

/-- Every original nine-edge point is recovered from its four profile sums,
four interior edges and free zeta--zeta edge. -/
theorem d02BalancedEdges_reconstruct (x : D01EdgeSpace) :
    d02BalancedEdges ((d01RowColumnSums x).1 1) ((d01RowColumnSums x).1 2)
      ((d01RowColumnSums x).2 1) ((d01RowColumnSums x).2 2)
      (d02InteriorEdges x) (x (0,0)) = x := by
  funext ij
  rcases ij with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [d02BalancedEdges,d02InteriorEdges,d01RowColumnSums,Fin.sum_univ_succ] <;> ring

theorem d02BalancedEdges_nonnegative_iff (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    d02BalancedEdges a b c d R u ∈ d01NonnegativeOrthant ↔
      R ∈ denominatorRegion a b c d ∧ 0≤u := by
  constructor
  · intro h
    have h00 := h (0,0)
    have h01 := h (0,1)
    have h02 := h (0,2)
    have h10 := h (1,0)
    have h11 := h (1,1)
    have h12 := h (1,2)
    have h20 := h (2,0)
    have h21 := h (2,1)
    have h22 := h (2,2)
    simp [d02BalancedEdges] at h00 h01 h02 h10 h11 h12 h20 h21 h22
    exact ⟨⟨h11,h12,h21,h22,by linarith,by linarith,by linarith,by linarith⟩,h00⟩
  · rintro ⟨⟨h0,h1,h2,h3,ha,hb,hc,hd⟩,hu⟩
    intro ij
    rcases ij with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [d02BalancedEdges] <;> linarith

theorem d02BalancedEdges_logSum (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    d02ZetaLogSum (d01RowColumnSums (d02BalancedEdges a b c d R u)) =
      2*u+d02ProfileSum a b c d-2*d02InteriorSum R := by
  rw [d02BalancedEdges_rowColumnSums]
  simp [d02ZetaLogSum,d02ProfileSum]
  ring

/-- The logarithmic cut `q₀≤1` is exactly the free-edge interval cut. -/
theorem d02BalancedEdges_cutoff_iff (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    d02ZetaLogSum (d01RowColumnSums (d02BalancedEdges a b c d R u)) ≤ 1 ↔
      u≤d02BalancedWidth a b c d R/2 := by
  rw [d02BalancedEdges_logSum]
  unfold d02BalancedWidth
  constructor <;> intro h <;> linarith

theorem d02BalancedWidth_pos {a b c d : ℝ} (hS : d02ProfileSum a b c d<1)
    {R : Fin 4 → ℝ} (hR : R∈denominatorRegion a b c d) :
    0<d02BalancedWidth a b c d R := by
  rcases hR with ⟨h0,h1,h2,h3,_⟩
  unfold d02BalancedWidth d02InteriorSum
  linarith

theorem d02BalancedEdges_slice_iff (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    (d02BalancedEdges a b c d R u ∈ d01NonnegativeOrthant ∧
      d02ZetaLogSum (d01RowColumnSums (d02BalancedEdges a b c d R u))≤1) ↔
      R∈denominatorRegion a b c d ∧ u∈Icc 0 (d02BalancedWidth a b c d R/2) := by
  rw [d02BalancedEdges_nonnegative_iff,d02BalancedEdges_cutoff_iff]
  simp only [mem_Icc]
  tauto

/-- Original centered Dirichlet coordinates in the direct AFE half. -/
theorem d02BalancedEdges_centered_arguments (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    (1/2-(d01RowColumnSums (d02BalancedEdges a b c d R u)).1 0,
     1/2-(d01RowColumnSums (d02BalancedEdges a b c d R u)).2 0) =
      (d02ProfileDelta a b c d-d02DirectCoordinate a b c d R u,
       -d02ProfileDelta a b c d-d02DirectCoordinate a b c d R u) := by
  rw [d02BalancedEdges_rowColumnSums]
  simp [d02ProfileDelta,d02DirectCoordinate,d02BalancedWidth,d02ProfileSum,
    d02InteriorSum]
  constructor <;> ring

/-- The dual AFE reverses the two zeta indices as well as the shifts.
Keeping that reversal gives the positive half with the same `delta`. -/
theorem d02BalancedEdges_dual_arguments (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    ((d01RowColumnSums (d02BalancedEdges a b c d R u)).2 0-1/2,
     (d01RowColumnSums (d02BalancedEdges a b c d R u)).1 0-1/2) =
      (d02ProfileDelta a b c d-d02DualCoordinate a b c d R u,
       -d02ProfileDelta a b c d-d02DualCoordinate a b c d R u) := by
  rw [d02BalancedEdges_rowColumnSums]
  simp [d02ProfileDelta,d02DualCoordinate,d02BalancedWidth,d02ProfileSum,
    d02InteriorSum]
  constructor <;> ring

theorem d02DirectCoordinate_mem_iff (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    d02DirectCoordinate a b c d R u ∈ Icc (-d02BalancedWidth a b c d R/2) 0 ↔
      u∈Icc 0 (d02BalancedWidth a b c d R/2) := by
  unfold d02DirectCoordinate
  constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith

theorem d02DualCoordinate_mem_iff (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    d02DualCoordinate a b c d R u ∈ Icc 0 (d02BalancedWidth a b c d R/2) ↔
      u∈Icc 0 (d02BalancedWidth a b c d R/2) := by
  unfold d02DualCoordinate
  constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith

theorem d02DualCoordinate_eq_neg_direct (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    d02DualCoordinate a b c d R u = -d02DirectCoordinate a b c d R u := by
  unfold d02DualCoordinate d02DirectCoordinate
  ring

end
end Sechstmoment
