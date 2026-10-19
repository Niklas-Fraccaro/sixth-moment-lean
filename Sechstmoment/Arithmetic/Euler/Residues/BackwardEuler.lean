import Sechstmoment.Arithmetic.Euler.Residues.ArithmeticCorrections

/-! Causal Euler difference operators acting on actual Taylor coefficients. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPResidues
open NoDPLocal
variable {R : Type*} [CommRing R]
def back (a : R) (f : ℕ → R) : ℕ → R
  | 0 => f 0
  | n+1 => f (n+1)-a*f n
def threeBack (a b c : R) (f : ℕ → R) := back a (back b (back c f))

@[simp] theorem back_zero (a : R) (f : ℕ → R) : back a f 0 = f 0 := rfl
@[simp] theorem back_succ (a : R) (f : ℕ → R) (n : ℕ) : back a f (n+1) = f (n+1)-a*f n := rfl

theorem back_add (a : R) (f g : ℕ → R) (n : ℕ) :
    back a (fun k => f k+g k) n = back a f n+back a g n := by
  cases n with
  | zero => rfl
  | succ n => simp only [back_succ]; ring

theorem back_smul (a z : R) (f : ℕ → R) (n : ℕ) :
    back a (fun k => z*f k) n = z*back a f n := by
  cases n with
  | zero => rfl
  | succ n => simp only [back_succ]; ring

theorem back_commute (a b : R) (f : ℕ → R) (n : ℕ) :
    back a (back b f) n = back b (back a f) n := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => simp only [back_succ, back_zero]; ring
    | succ n => simp only [back_succ]; ring

theorem back_step (a : R) (f : ℕ → R) (n : ℕ) : back a (step a f) n = f n := by
  cases n with
  | zero => rfl
  | succ n => simp only [back_succ, step_succ]; ring

theorem step_back (a : R) (f : ℕ → R) (n : ℕ) : step a (back a f) n = f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [step_succ, back_succ, ih]; ring

@[simp] theorem threeBack_zero (a b c : R) (f : ℕ → R) : threeBack a b c f 0 = f 0 := rfl

theorem threeBack_one (a b c : R) (f : ℕ → R) :
    threeBack a b c f 1 = f 1-(a+b+c)*f 0 := by
  simp only [threeBack, back_succ, back_zero]
  ring

theorem threeBack_two (a b c : R) (f : ℕ → R) :
    threeBack a b c f 2 = f 2-(a+b+c)*f 1+(a*b+a*c+b*c)*f 0 := by
  simp only [threeBack, back_succ, back_zero]
  ring

theorem threeBack_high (a b c : R) (f : ℕ → R) (n : ℕ) :
    threeBack a b c f (n+3) = f (n+3)-(a+b+c)*f (n+2)+
      (a*b+a*c+b*c)*f (n+1)-a*b*c*f n := by
  simp only [threeBack, back_succ]
  ring

theorem threeBack_coeff3 (a b c : R) (n : ℕ) :
    threeBack a b c (coeff3 a b c) n = if n = 0 then 1 else 0 := by
  unfold threeBack
  rw [back_commute a b]
  rw [show back a (back c (coeff3 a b c)) = back c (back a (coeff3 a b c)) from
    funext (back_commute a c (coeff3 a b c))]
  rw [show back a (coeff3 a b c) = coeff2 b c from funext (back_step a (coeff2 b c))]
  rw [back_commute b c]
  rw [show back b (coeff2 b c) = coeff1 c from funext (back_step b (coeff1 c))]
  cases n with
  | zero => simp [coeff1]
  | succ n => simp [back_succ, coeff1, pow_succ, mul_comm]

end Sechstmoment.Source.NoDPResidues
