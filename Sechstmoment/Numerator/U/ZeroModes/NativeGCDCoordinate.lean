import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Sechstmoment.Numerator.U.ZeroModes.Linearization.Fubini

/-! Actual positive-real change of coordinate in the native GCD integral.
The BBLR product variable is X=abmn*x/d; no integer factor is identified
with a continuous coordinate. Every native dyadic mask is retained. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03NativeGCDCoordinateScale (w : Fin 5→ℕ) : ℝ :=
  (Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)/((w 0:ℝ)*w 1*w 2*w 3)

def a03NativeGCDCoordinateQuad (w : Fin 5→ℕ) (X : ℝ) : Fin 4→ℝ :=
  ![(w 2:ℝ),X/((w 0:ℝ)*w 2),(w 3:ℝ),X/((w 1:ℝ)*w 3)]

def a03NativeGCDCoordinateArguments (m n : Bool) (q : QuadraticScales)
    (w : Fin 5→ℕ) (X : ℝ) : Fin 6→ℝ :=
  a03SixZeroSourceArguments m n q w (a03NativeGCDCoordinateScale w*X)

theorem a03NativeGCDCoordinateScale_pos (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) :
    0<a03NativeGCDCoordinateScale w := by
  have hp (j : Fin 5) : 0<w j := by have := hw j; omega
  have hd : 0<Nat.gcd (w 0*w 2) (w 1*w 3) :=
    Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (hp 0) (hp 2))
  have hpr (j : Fin 5) : (0:ℝ)<w j := by exact_mod_cast hp j
  unfold a03NativeGCDCoordinateScale
  exact div_pos (by exact_mod_cast hd) (mul_pos (mul_pos (mul_pos (hpr 0) (hpr 1)) (hpr 2)) (hpr 3))

theorem a03NativeGCDCoordinateQuad_eq (q : QuadraticScales)
    (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) (X : ℝ) :
    a03ZeroModePhysicalQuad q w (a03NativeGCDCoordinateScale w*X)=
      a03NativeGCDCoordinateQuad w X := by
  have hp (j : Fin 5) : (w j:ℝ)≠0 := by exact_mod_cast (show w j≠0 by have := hw j; omega)
  have hd : (Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)≠0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (show 0<w 0 by have := hw 0; omega)
      (show 0<w 2 by have := hw 2; omega))).ne'
  ext j
  fin_cases j <;> simp [a03ZeroModePhysicalQuad,a03NativeGCDCoordinateScale,a03NativeGCDCoordinateQuad]
  all_goals field_simp [hp 0,hp 1,hp 2,hp 3,hd]

theorem a03NativeGCDCoordinateQuad_product (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) (X : ℝ) :
    (∏ j : Fin 4,a03NativeGCDCoordinateQuad w X j)=X^2/((w 0:ℝ)*w 1) := by
  have hp (j : Fin 5) : (w j:ℝ)≠0 := by exact_mod_cast (show w j≠0 by have := hw j; omega)
  simp [a03NativeGCDCoordinateQuad,Fin.prod_univ_four]
  field_simp [hp 0,hp 1,hp 2,hp 3]

theorem a03NativeGCDCoordinateQuad_ratio (w : Fin 5→ℕ) (hw : ∀ j,1≤w j)
    {X : ℝ} (hX : 0<X) :
    a03NativeGCDCoordinateQuad w X 0/a03NativeGCDCoordinateQuad w X 1=(w 0:ℝ)*(w 2:ℝ)^2/X ∧
      a03NativeGCDCoordinateQuad w X 2/a03NativeGCDCoordinateQuad w X 3=(w 1:ℝ)*(w 3:ℝ)^2/X := by
  have hp (j : Fin 5) : (w j:ℝ)≠0 := by exact_mod_cast (show w j≠0 by have := hw j; omega)
  constructor <;> simp [a03NativeGCDCoordinateQuad]
  all_goals field_simp [hp 0,hp 1,hp 2,hp 3,hX.ne']

/-- Genuine Jacobian substitution for each native term, including all
five AFE/gap masks and the full tensor. -/
theorem a03_native_zero_term_eq_GCD_coordinate (F : A03SixTensorSpace→ℂ)
    (m n : Bool) (q : QuadraticScales) (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) :
    (∫ x : ℝ in Ioi 0,a03PhysicalZeroSmoothMask m n q w x*
      F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x)))=
      (a03NativeGCDCoordinateScale w:ℂ)*∫ X : ℝ in Ioi 0,
        (∏ j : Fin 5,(rectangularSmoothBlockWeight (a03NativeGCDCoordinateArguments m n q w X j.succ):ℂ))*
          F (a03SixTensorLogPoint (a03NativeGCDCoordinateArguments m n q w X)) := by
  have he := integral_comp_mul_left_Ioi'
    (fun x : ℝ => a03PhysicalZeroSmoothMask m n q w x*
      F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x))) (0:ℝ)
      (a03NativeGCDCoordinateScale_pos w hw)
  simpa only [mul_zero,Complex.real_smul,a03NativeGCDCoordinateArguments,a03PhysicalZeroSmoothMask] using he.symm

def a03NativeGCDCoordinateZeroMode (F : A03SixTensorSpace→ℂ) (m n : Bool)
    (q : QuadraticScales) (α β : ℕ→ℂ) : ℂ :=
  ∑ w∈quadraticMainIndexSet q,α (w 0)*β (w 1)*(a03NativeGCDCoordinateScale w:ℂ)*
    ∫ X : ℝ in Ioi 0,(∏ j : Fin 5,
      (rectangularSmoothBlockWeight (a03NativeGCDCoordinateArguments m n q w X j.succ):ℂ))*
        F (a03SixTensorLogPoint (a03NativeGCDCoordinateArguments m n q w X))

theorem a03_native_physical_zero_eq_GCD_coordinate (F : A03SixTensorSpace→ℂ)
    (m n : Bool) (q : QuadraticScales) (α β : ℕ→ℂ) :
    a03SixTensorPhysicalZeroMode F m n q α β=a03NativeGCDCoordinateZeroMode F m n q α β := by
  unfold a03SixTensorPhysicalZeroMode a03NativeGCDCoordinateZeroMode
  apply Finset.sum_congr rfl
  intro w hw
  have hp : ∀ j,1≤w j := fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
  rw [show (fun x : ℝ => (∏ j : Fin 5,(rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q w x j.succ):ℂ))*
    F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x)))=
      (fun x : ℝ => a03PhysicalZeroSmoothMask m n q w x*F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x))) from rfl,
    a03_native_zero_term_eq_GCD_coordinate F m n q w hp]
  ring

end
end Sechstmoment
