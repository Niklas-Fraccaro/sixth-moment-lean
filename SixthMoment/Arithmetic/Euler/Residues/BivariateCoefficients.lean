import SixthMoment.Arithmetic.Euler.Residues.BackwardEuler

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
namespace SixthMoment.Source.NoDPResidues
open NoDPLocal
variable {R : Type*} [CommRing R]
def extractLeft (a b c : R) (F : ℕ → ℕ → R) (m n : ℕ) : R :=
  threeBack a b c (fun k => F k n) m
def extractRight (a b c : R) (F : ℕ → ℕ → R) (m n : ℕ) : R :=
  threeBack a b c (F m) n
def regularizedCoeff (a b c : R) (F : ℕ → ℕ → R) : ℕ → ℕ → R :=
  extractLeft a b c (extractRight a b c F)
noncomputable def residueRest (ai a b c x : ℂ) : ℕ → ℕ → ℂ :=
  regularizedCoeff (x*a) (x*b) (x*c) (fun h k => weightedResidue ai a b c x (h+k))

theorem extract_commute (a b c : R) (F : ℕ → ℕ → R) (m n : ℕ) :
    extractLeft a b c (extractRight a b c F) m n =
      extractRight a b c (extractLeft a b c F) m n := by
  rcases m with (_ | _ | _ | m) <;> rcases n with (_ | _ | _ | n) <;>
    simp only [extractLeft, extractRight, threeBack, back] <;> ring

@[simp] theorem regularizedCoeff_zero_zero (a b c : R) (F : ℕ → ℕ → R) :
    regularizedCoeff a b c F 0 0 = F 0 0 := rfl

theorem regularizedCoeff_one_zero (a b c : R) (F : ℕ → ℕ → R) :
    regularizedCoeff a b c F 1 0 = F 1 0-(a+b+c)*F 0 0 := by
  simp [regularizedCoeff, extractLeft, extractRight, threeBack_one]

theorem regularizedCoeff_zero_one (a b c : R) (F : ℕ → ℕ → R) :
    regularizedCoeff a b c F 0 1 = F 0 1-(a+b+c)*F 0 0 := by
  simp [regularizedCoeff, extractLeft, extractRight, threeBack_one]

theorem regularizedCoeff_one_one (a b c : R) (F : ℕ → ℕ → R) :
    regularizedCoeff a b c F 1 1 = F 1 1-(a+b+c)*(F 1 0+F 0 1)+(a+b+c)^2*F 0 0 := by
  simp only [regularizedCoeff, extractLeft, extractRight, threeBack_one]
  ring

theorem regularizedCoeff_diagonal_symm (a b c : R) (W : ℕ → R) (m n : ℕ) :
    regularizedCoeff a b c (fun h k => W (h+k)) m n =
      regularizedCoeff a b c (fun h k => W (h+k)) n m := by
  rcases m with (_ | _ | _ | m) <;> rcases n with (_ | _ | _ | n) <;>
    simp only [regularizedCoeff, extractLeft, extractRight, threeBack, back, Nat.add_comm] <;> ring

theorem regularizedCoeff_diagonal_axis_left (a b c : R) (W : ℕ → R) (m : ℕ) :
    regularizedCoeff a b c (fun h k => W (h+k)) m 0 = threeBack a b c W m := by
  simp [regularizedCoeff, extractLeft, extractRight]

theorem regularizedCoeff_diagonal_axis_right (a b c : R) (W : ℕ → R) (n : ℕ) :
    regularizedCoeff a b c (fun h k => W (h+k)) 0 n = threeBack a b c W n := by
  simp [regularizedCoeff, extractLeft, extractRight]

@[simp] theorem residueRest_constant (ai a b c x : ℂ) : residueRest ai a b c x 0 0 = 1 := by
  simp [residueRest]

theorem residueRest_linear (ai a b c x : ℂ) (hai : ai ≠ 0) :
    residueRest ai a b c x 1 0 = -x^2/ai*(a*b+a*c+b*c)+x^3/ai^2*(a*b*c) ∧
    residueRest ai a b c x 0 1 = -x^2/ai*(a*b+a*c+b*c)+x^3/ai^2*(a*b*c) := by
  unfold residueRest
  rw [regularizedCoeff_one_zero, regularizedCoeff_zero_one]
  simp only [Nat.one_add, Nat.add_zero, Nat.zero_add, weightedResidue_base,
    weightedResidue_first ai a b c x hai]
  constructor <;> ring

end SixthMoment.Source.NoDPResidues
