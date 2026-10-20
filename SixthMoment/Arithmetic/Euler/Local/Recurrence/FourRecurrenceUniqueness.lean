import SixthMoment.Arithmetic.Euler.Local.Recurrence.FirstOrderUniqueness


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

variable {R : Type*} [CommRing R]
theorem fourth_order_unique (a b c d : R) (f g : ℕ → R)
    (hinit : ∀ n<4, f n=g n)
    (hf : ∀ n, f (n+4)=e1 a b c d*f (n+3)-e2 a b c d*f (n+2)+e3 a b c d*f (n+1)-e4 a b c d*f n)
    (hg : ∀ n, g (n+4)=e1 a b c d*g (n+3)-e2 a b c d*g (n+2)+e3 a b c d*g (n+1)-e4 a b c d*g n) : f=g := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<4
    · exact hinit n hn
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
      rw [Nat.add_comm 4 k,hf,hg]
      rw [ih (k+3) (by omega),ih (k+2) (by omega),ih (k+1) (by omega),ih k (by omega)]

end SixthMoment.Source.NoDPLocal
