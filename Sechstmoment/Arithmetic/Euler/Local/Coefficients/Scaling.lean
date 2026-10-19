import Sechstmoment.Arithmetic.Euler.Local.Geometric.StepProductScaling

/-! Homogeneity of the twofold coefficients. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem coeff2_scaled (a b r : R) (n : ℕ) : coeff2 (r*a) (r*b) n=r^n*coeff2 a b n := by
  unfold coeff2
  rw [show coeff1 (r*b) = (fun k => r^k*coeff1 b k) from funext (fun k => coeff1_scaled b r k)]
  exact step_scaled a r (coeff1 b) n

end Sechstmoment.Source.NoDPLocal

/-! Homogeneity of the threefold coefficients. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem coeff3_scaled (a b c r : R) (n : ℕ) : coeff3 (r*a) (r*b) (r*c) n=r^n*coeff3 a b c n := by
  unfold coeff3
  rw [show coeff2 (r*b) (r*c) = (fun k => r^k*coeff2 b c k) from funext (fun k => coeff2_scaled b c r k)]
  exact step_scaled a r (coeff2 b c) n

end Sechstmoment.Source.NoDPLocal

/-! Homogeneity of the fourfold shifted coefficients. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem coeff4_scaled (a b c d r : R) (n : ℕ) :
    coeff4 (r*a) (r*b) (r*c) (r*d) n=r^n*coeff4 a b c d n := by
  unfold coeff4
  rw [show coeff3 (r*b) (r*c) (r*d) = (fun k => r^k*coeff3 b c d k) from funext (fun k => coeff3_scaled b c d r k)]
  exact step_scaled a r (coeff3 b c d) n

end Sechstmoment.Source.NoDPLocal

/-! Homogeneity of the four denominator coefficients. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem e1_scaled (a b c d r : R) : e1 (r*a) (r*b) (r*c) (r*d)=r*e1 a b c d := by unfold e1; ring
theorem e2_scaled (a b c d r : R) : e2 (r*a) (r*b) (r*c) (r*d)=r^2*e2 a b c d := by unfold e2; ring
theorem e3_scaled (a b c d r : R) : e3 (r*a) (r*b) (r*c) (r*d)=r^3*e3 a b c d := by unfold e3; ring
theorem e4_scaled (a b c d r : R) : e4 (r*a) (r*b) (r*c) (r*d)=r^4*e4 a b c d := by unfold e4; ring

end Sechstmoment.Source.NoDPLocal

/-! Homogeneity of each coefficient of the local numerator. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem q0_scaled (a b c d r : R) (h : ℕ) :
    q0 (r*a) (r*b) (r*c) (r*d) h=r^h*q0 a b c d h := by simp [q0,coeff4_scaled]
theorem q1_scaled (a b c d r : R) (h : ℕ) :
    q1 (r*a) (r*b) (r*c) (r*d) h=r^(h+1)*q1 a b c d h := by
  simp only [q1,coeff4_scaled,e1_scaled,pow_succ]; ring
theorem q2_scaled (a b c d r : R) (h : ℕ) :
    q2 (r*a) (r*b) (r*c) (r*d) h=r^(h+2)*q2 a b c d h := by
  simp only [q2,coeff4_scaled,e1_scaled,e2_scaled,pow_succ]; ring
theorem q3_scaled (a b c d r : R) (h : ℕ) :
    q3 (r*a) (r*b) (r*c) (r*d) h=r^(h+3)*q3 a b c d h := by
  simp only [q3,coeff4_scaled,e1_scaled,e2_scaled,e3_scaled,pow_succ]; ring

end Sechstmoment.Source.NoDPLocal

/-! The entire Euler correction scales homogeneously. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem numerator_scaled (a b c d r t : R) (h : ℕ) :
    numerator (r*a) (r*b) (r*c) (r*d) h t=r^h*numerator a b c d h (r*t) := by
  simp only [numerator,q0_scaled,q1_scaled,q2_scaled,q3_scaled,pow_add]; ring

end Sechstmoment.Source.NoDPLocal

/-! Scaling the four local roots is equivalent to scaling the series variable. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem denom_scaled (a b c d r t : R) :
    denom (r*a) (r*b) (r*c) (r*d) t=denom a b c d (r*t) := by unfold denom; ring

end Sechstmoment.Source.NoDPLocal
