import Sechstmoment.Arithmetic.Euler.Local.Recurrence.ThreeAnnihilator

/-! A first order recursion is uniquely determined by its input and initial value. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem step_unique (a : R) (f g : ℕ → R) (h0 : g 0=f 0)
    (hs : ∀ n, g (n+1)=f (n+1)+a*g n) : g=step a f := by
  funext n
  induction n with
  | zero => exact h0
  | succ n ih => rw [hs,step_succ,ih]
theorem delta_eq_zero_unique (a : R) (f : ℕ → R) (hf : ∀ n, delta a f n=0) (n : ℕ) :
    f n=f 0*a^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := hf n
    unfold delta at hn
    have he : f (n+1)=a*f n := sub_eq_zero.mp hn
    rw [he,ih,pow_succ]; ring

end Sechstmoment.Source.NoDPLocal
