import Sechstmoment.Arithmetic.Euler.Local.Geometric.StepMap

/-! Transport of the first two local coefficient sequences. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S]
theorem coeff1_map (F : R →+* S) (a : R) (n : ℕ) : F (coeff1 a n)=coeff1 (F a) n := by simp [coeff1]
theorem coeff2_map (F : R →+* S) (a b : R) (n : ℕ) : F (coeff2 a b n)=coeff2 (F a) (F b) n := by
  unfold coeff2
  rw [step_map]
  simp_rw [coeff1_map]

end Sechstmoment.Source.NoDPLocal

/-! Transport of threefold local coefficients. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S]
theorem coeff3_map (F : R →+* S) (a b c : R) (n : ℕ) : F (coeff3 a b c n)=coeff3 (F a) (F b) (F c) n := by
  unfold coeff3
  rw [step_map]
  simp_rw [coeff2_map]

end Sechstmoment.Source.NoDPLocal

/-! Transport of fourfold local coefficients. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S]
theorem coeff4_map (F : R →+* S) (a b c d : R) (n : ℕ) :
    F (coeff4 a b c d n)=coeff4 (F a) (F b) (F c) (F d) n := by
  unfold coeff4
  rw [step_map]
  simp_rw [coeff3_map]

end Sechstmoment.Source.NoDPLocal
