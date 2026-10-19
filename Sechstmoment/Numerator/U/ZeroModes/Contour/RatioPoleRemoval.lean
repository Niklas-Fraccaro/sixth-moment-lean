import Sechstmoment.Numerator.U.ZeroModes.Contour.RatioWeight
import Sechstmoment.Zeta.Regularized

/-! Actual removal of the two same-side difference poles in BBLR §4.
The extension retains the other quadratic factor of the genuine ratio
Gaussian. No contour displacement or reconstructed main term is assumed. -/

namespace Sechstmoment.Source
open Complex
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioOtherRoot (j : Fin 2) : Fin 2 := if j=0 then 1 else 0

def a03ZeroModeRatioDifferenceArgument (α : MomentShifts) (j : Fin 2) (z : ℂ) : ℂ :=
  1+2*(z-a03ZeroModeRatioRoot α j)

def a03ZeroModeRatioRemovedDifference (α : MomentShifts) (j : Fin 2) (z : ℂ) : ℂ :=
  exp (z^2)*(1-z^2/(a03ZeroModeRatioRoot α (a03ZeroModeRatioOtherRoot j))^2)*
    (-(z+a03ZeroModeRatioRoot α j)/(2*(a03ZeroModeRatioRoot α j)^2))*
      Sechstmoment.polarRegularizedZeta (a03ZeroModeRatioDifferenceArgument α j z)

theorem a03ZeroModeRatioDifferenceArgument_zero (α : MomentShifts) (z : ℂ) :
    a03ZeroModeRatioDifferenceArgument α 0 z=1+α 0-α 1+2*z := by
  simp [a03ZeroModeRatioDifferenceArgument,a03ZeroModeRatioRoot]
  ring

theorem a03ZeroModeRatioDifferenceArgument_one (α : MomentShifts) (z : ℂ) :
    a03ZeroModeRatioDifferenceArgument α 1 z=1+α 2-α 3+2*z := by
  simp [a03ZeroModeRatioDifferenceArgument,a03ZeroModeRatioRoot]
  ring

theorem a03ZeroModeRatioRemovedDifference_differentiable (α : MomentShifts) (j : Fin 2) :
    Differentiable ℂ (a03ZeroModeRatioRemovedDifference α j) := by
  unfold a03ZeroModeRatioRemovedDifference a03ZeroModeRatioDifferenceArgument
  exact (by fun_prop : Differentiable ℂ (fun z : ℂ =>
    exp (z^2)*(1-z^2/(a03ZeroModeRatioRoot α (a03ZeroModeRatioOtherRoot j))^2)*
      (-(z+a03ZeroModeRatioRoot α j)/(2*(a03ZeroModeRatioRoot α j)^2)))).mul
    (Sechstmoment.polarRegularizedZeta_differentiable.comp (by fun_prop))

theorem a03ZeroModeRatioWeight_split (α : MomentShifts) (j : Fin 2) (z : ℂ) :
    a03ZeroModeRatioWeight α z=exp (z^2)*
      (1-z^2/(a03ZeroModeRatioRoot α (a03ZeroModeRatioOtherRoot j))^2)*
        (1-z^2/(a03ZeroModeRatioRoot α j)^2) := by
  fin_cases j <;> simp [a03ZeroModeRatioWeight,a03ZeroModeRatioOtherRoot,
    mul_comm,mul_left_comm,mul_assoc]

/-- Exact equality away from the selected difference pole. The expression
on the left is entire also at that pole. -/
theorem a03ZeroModeRatioRemovedDifference_eq (α : MomentShifts) (j : Fin 2)
    (hρ : a03ZeroModeRatioRoot α j≠0) {z : ℂ} (hz : z≠a03ZeroModeRatioRoot α j) :
    a03ZeroModeRatioRemovedDifference α j z=
      a03ZeroModeRatioWeight α z*riemannZeta (a03ZeroModeRatioDifferenceArgument α j z) := by
  have ha : a03ZeroModeRatioDifferenceArgument α j z≠1 := by
    unfold a03ZeroModeRatioDifferenceArgument
    intro he
    have h : z=a03ZeroModeRatioRoot α j := by linear_combination he/2
    exact hz h
  rw [a03ZeroModeRatioWeight_split]
  unfold a03ZeroModeRatioRemovedDifference
  rw [Sechstmoment.polarRegularizedZeta_of_ne_one ha]
  unfold a03ZeroModeRatioDifferenceArgument
  field_simp
  ring

/-- At the genuine ratio pole `z=0`, the numerator has exactly the
same-side zeta value. -/
theorem a03ZeroModeRatioRemovedDifference_zero (α : MomentShifts) (j : Fin 2)
    (hρ : a03ZeroModeRatioRoot α j≠0) :
    a03ZeroModeRatioRemovedDifference α j 0=
      riemannZeta (a03ZeroModeRatioDifferenceArgument α j 0) := by
  rw [a03ZeroModeRatioRemovedDifference_eq α j hρ (Ne.symm hρ),
    a03ZeroModeRatioWeight_zero,one_mul]

/-- The actual holomorphic value at a removed difference pole includes
the factor `1/2` from its affine zeta argument. -/
theorem a03ZeroModeRatioRemovedDifference_at_root (α : MomentShifts) (j : Fin 2)
    (hρ : a03ZeroModeRatioRoot α j≠0) :
    a03ZeroModeRatioRemovedDifference α j (a03ZeroModeRatioRoot α j)=
      -exp ((a03ZeroModeRatioRoot α j)^2)*
        (1-(a03ZeroModeRatioRoot α j)^2/
          (a03ZeroModeRatioRoot α (a03ZeroModeRatioOtherRoot j))^2)/
            a03ZeroModeRatioRoot α j := by
  simp only [a03ZeroModeRatioRemovedDifference,a03ZeroModeRatioDifferenceArgument,
    sub_self,mul_zero,add_zero,Sechstmoment.polarRegularizedZeta_one,mul_one]
  field_simp
  ring

def a03ZeroModeRatioRemovedPair (α : MomentShifts) (u v : ℂ) : ℂ :=
  a03ZeroModeRatioRemovedDifference α 0 u*a03ZeroModeRatioRemovedDifference α 1 v

theorem a03ZeroModeRatioRemovedPair_differentiable_left (α : MomentShifts) (v : ℂ) :
    Differentiable ℂ (fun u => a03ZeroModeRatioRemovedPair α u v) :=
  (a03ZeroModeRatioRemovedDifference_differentiable α 0).mul_const _

theorem a03ZeroModeRatioRemovedPair_differentiable_right (α : MomentShifts) (u : ℂ) :
    Differentiable ℂ (a03ZeroModeRatioRemovedPair α u) :=
  (a03ZeroModeRatioRemovedDifference_differentiable α 1).const_mul _

theorem a03ZeroModeRatioRemovedPair_eq (α : MomentShifts)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) {u v : ℂ}
    (hu : u≠a03ZeroModeRatioRoot α 0) (hv : v≠a03ZeroModeRatioRoot α 1) :
    a03ZeroModeRatioRemovedPair α u v/(u*v)=
      (a03ZeroModeRatioWeight α u/u)*(a03ZeroModeRatioWeight α v/v)*
        riemannZeta (1+α 0-α 1+2*u)*riemannZeta (1+α 2-α 3+2*v) := by
  unfold a03ZeroModeRatioRemovedPair
  rw [a03ZeroModeRatioRemovedDifference_eq α 0 (hρ 0) hu,
    a03ZeroModeRatioRemovedDifference_eq α 1 (hρ 1) hv,
    a03ZeroModeRatioDifferenceArgument_zero,a03ZeroModeRatioDifferenceArgument_one]
  ring

theorem a03ZeroModeRatioRemovedPair_zero (α : MomentShifts)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) :
    a03ZeroModeRatioRemovedPair α 0 0=
      riemannZeta (1+α 0-α 1)*riemannZeta (1+α 2-α 3) := by
  unfold a03ZeroModeRatioRemovedPair
  rw [a03ZeroModeRatioRemovedDifference_zero α 0 (hρ 0),
    a03ZeroModeRatioRemovedDifference_zero α 1 (hρ 1),
    a03ZeroModeRatioDifferenceArgument_zero,a03ZeroModeRatioDifferenceArgument_one]
  simp

end
end Sechstmoment.Source
