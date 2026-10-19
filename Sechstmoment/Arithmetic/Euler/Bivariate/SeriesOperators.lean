import Sechstmoment.Arithmetic.Euler.Bivariate.RestAlgebra

/-! Multiplication of actual, summable double series by the six Euler factors. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPLocalClosure
open NoDPLocal NoDPResidues
open scoped BigOperators

def delayLeft (F : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, _ => 0
  | m+1, n => F m n

def delayRight (F : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ
  | _, 0 => 0
  | m, n+1 => F m n

theorem delayLeft_hasSum (F : ℕ → ℕ → ℂ) (U V S : ℂ)
    (hs : HasSum (fun p : ℕ × ℕ => F p.1 p.2*U^p.1*V^p.2) S) :
    HasSum (fun p : ℕ × ℕ => delayLeft F p.1 p.2*U^p.1*V^p.2) (U*S) := by
  let e : ℕ × ℕ → ℕ × ℕ := fun p => (p.1+1,p.2)
  have hi : Function.Injective e := by
    intro p q h
    change (p.1+1,p.2) = (q.1+1,q.2) at h
    exact Prod.ext (Nat.add_right_cancel (Prod.mk.inj h).1) (Prod.mk.inj h).2
  have hz : ∀ p ∉ Set.range e, delayLeft F p.1 p.2*U^p.1*V^p.2 = 0 := by
    rintro ⟨m,n⟩ hp
    cases m with
    | zero => simp [delayLeft]
    | succ m => exact False.elim (hp ⟨(m,n),rfl⟩)
  apply (hi.hasSum_iff hz).mp
  convert hs.mul_left U using 1
  funext p
  simp only [Function.comp_def, e, delayLeft, pow_succ]
  ring

theorem delayRight_hasSum (F : ℕ → ℕ → ℂ) (U V S : ℂ)
    (hs : HasSum (fun p : ℕ × ℕ => F p.1 p.2*U^p.1*V^p.2) S) :
    HasSum (fun p : ℕ × ℕ => delayRight F p.1 p.2*U^p.1*V^p.2) (V*S) := by
  let e : ℕ × ℕ → ℕ × ℕ := fun p => (p.1,p.2+1)
  have hi : Function.Injective e := by
    intro p q h
    change (p.1,p.2+1) = (q.1,q.2+1) at h
    exact Prod.ext (Prod.mk.inj h).1 (Nat.add_right_cancel (Prod.mk.inj h).2)
  have hz : ∀ p ∉ Set.range e, delayRight F p.1 p.2*U^p.1*V^p.2 = 0 := by
    rintro ⟨m,n⟩ hp
    cases n with
    | zero => simp [delayRight]
    | succ n => exact False.elim (hp ⟨(m,n),rfl⟩)
  apply (hi.hasSum_iff hz).mp
  convert hs.mul_left V using 1
  funext p
  simp only [Function.comp_def, e, delayRight, pow_succ]
  ring

theorem backLeft_hasSum (F : ℕ → ℕ → ℂ) (a U V S : ℂ)
    (hs : HasSum (fun p : ℕ × ℕ => F p.1 p.2*U^p.1*V^p.2) S) :
    HasSum (fun p : ℕ × ℕ => back a (fun k => F k p.2) p.1*U^p.1*V^p.2) ((1-a*U)*S) := by
  have H := hs.sub ((delayLeft_hasSum F U V S hs).mul_left a)
  convert H using 1
  · funext p
    obtain ⟨m,n⟩ := p
    cases m <;> simp only [back, delayLeft] <;> ring
  · ring

theorem backRight_hasSum (F : ℕ → ℕ → ℂ) (a U V S : ℂ)
    (hs : HasSum (fun p : ℕ × ℕ => F p.1 p.2*U^p.1*V^p.2) S) :
    HasSum (fun p : ℕ × ℕ => back a (F p.1) p.2*U^p.1*V^p.2) ((1-a*V)*S) := by
  have H := hs.sub ((delayRight_hasSum F U V S hs).mul_left a)
  convert H using 1
  · funext p
    obtain ⟨m,n⟩ := p
    cases n <;> simp only [back, delayRight] <;> ring
  · ring

theorem extractLeft_hasSum (F : ℕ → ℕ → ℂ) (a b c U V S : ℂ)
    (hs : HasSum (fun p : ℕ × ℕ => F p.1 p.2*U^p.1*V^p.2) S) :
    HasSum (fun p : ℕ × ℕ => extractLeft a b c F p.1 p.2*U^p.1*V^p.2) (den3 a b c U*S) := by
  have H1 := backLeft_hasSum F c U V S hs
  have H2 := backLeft_hasSum (fun m n => back c (fun k => F k n) m) b U V _ H1
  have H3 := backLeft_hasSum (fun m n => back b (back c (fun k => F k n)) m) a U V _ H2
  convert H3 using 1
  · rfl
  · unfold den3
    ring

theorem extractRight_hasSum (F : ℕ → ℕ → ℂ) (a b c U V S : ℂ)
    (hs : HasSum (fun p : ℕ × ℕ => F p.1 p.2*U^p.1*V^p.2) S) :
    HasSum (fun p : ℕ × ℕ => extractRight a b c F p.1 p.2*U^p.1*V^p.2) (den3 a b c V*S) := by
  have H1 := backRight_hasSum F c U V S hs
  have H2 := backRight_hasSum (fun m n => back c (F m) n) b U V _ H1
  have H3 := backRight_hasSum (fun m n => back b (back c (F m)) n) a U V _ H2
  convert H3 using 1
  · rfl
  · unfold den3
    ring

theorem regularized_hasSum (F : ℕ → ℕ → ℂ) (a b c U V S : ℂ)
    (hs : HasSum (fun p : ℕ × ℕ => F p.1 p.2*U^p.1*V^p.2) S) :
    HasSum (fun p : ℕ × ℕ => regularizedCoeff a b c F p.1 p.2*U^p.1*V^p.2)
      (den3 a b c U*den3 a b c V*S) := by
  have H1 := extractRight_hasSum F a b c U V S hs
  have H2 := extractLeft_hasSum (extractRight a b c F) a b c U V _ H1
  convert H2 using 1
  · rfl
  · ring

theorem restPolynomial_factorization_of_summable (ai a b c x U V : ℂ) (hai : ai ≠ 0)
    (hs : Summable (diagonalTerm (weightedResidue ai a b c x) U V)) :
    restPolynomial ai a b c x U V =
      den3 (x*a) (x*b) (x*c) U*den3 (x*a) (x*b) (x*c) V*
        doubleSeries (weightedResidue ai a b c x) U V := by
  rw [← rest_series_eq_polynomial ai a b c x U V hai]
  exact (regularized_hasSum (fun m n => weightedResidue ai a b c x (m+n))
    (x*a) (x*b) (x*c) U V _ hs.hasSum).tsum_eq

end Sechstmoment.Source.NoDPLocalClosure
