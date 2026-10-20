import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import SixthMoment.Arithmetic.Euler.Residues.ResidueBounds

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
namespace SixthMoment.Source.NoDPResidues
open NoDPLocal

@[fun_prop] theorem coeff2_differentiable {a b : ℂ → ℂ}
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b) (n : ℕ) :
    Differentiable ℂ (fun z => coeff2 (a z) (b z) n) := by
  induction n with
  | zero =>
    change Differentiable ℂ (fun _ : ℂ => (1:ℂ))
    exact differentiable_const 1
  | succ n ih =>
    change Differentiable ℂ (fun z => b z^(n+1)+a z*coeff2 (a z) (b z) n)
    exact (hb.pow (n+1)).add (ha.mul ih)

@[fun_prop] theorem coeff3_differentiable {a b c : ℂ → ℂ}
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b) (hc : Differentiable ℂ c) (n : ℕ) :
    Differentiable ℂ (fun z => coeff3 (a z) (b z) (c z) n) := by
  induction n with
  | zero =>
    change Differentiable ℂ (fun _ : ℂ => (1:ℂ))
    exact differentiable_const 1
  | succ n ih =>
    change Differentiable ℂ (fun z => coeff2 (b z) (c z) (n+1)+a z*coeff3 (a z) (b z) (c z) n)
    exact (coeff2_differentiable hb hc (n+1)).add (ha.mul ih)

@[fun_prop] theorem coeff4_differentiable {a b c d : ℂ → ℂ}
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b)
    (hc : Differentiable ℂ c) (hd : Differentiable ℂ d) (n : ℕ) :
    Differentiable ℂ (fun z => coeff4 (a z) (b z) (c z) (d z) n) := by
  induction n with
  | zero =>
    change Differentiable ℂ (fun _ : ℂ => (1:ℂ))
    exact differentiable_const 1
  | succ n ih =>
    change Differentiable ℂ (fun z => coeff3 (b z) (c z) (d z) (n+1)+a z*coeff4 (a z) (b z) (c z) (d z) n)
    exact (coeff3_differentiable hb hc hd (n+1)).add (ha.mul ih)

@[fun_prop] theorem numerator_differentiable {a b c d t : ℂ → ℂ}
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b) (hc : Differentiable ℂ c)
    (hd : Differentiable ℂ d) (ht : Differentiable ℂ t) (h : ℕ) :
    Differentiable ℂ (fun z => numerator (a z) (b z) (c z) (d z) h (t z)) := by
  unfold numerator q0 q1 q2 q3 e1 e2 e3
  fun_prop

@[fun_prop] theorem triNumerator_differentiable {a b c t : ℂ → ℂ}
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b) (hc : Differentiable ℂ c)
    (ht : Differentiable ℂ t) (h : ℕ) :
    Differentiable ℂ (fun z => triNumerator (a z) (b z) (c z) h (t z)) := by
  unfold triNumerator triQ1 triQ2
  fun_prop

@[fun_prop] theorem residuePoly_differentiable {a b c : ℂ → ℂ}
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b) (hc : Differentiable ℂ c) (h : ℕ) :
    Differentiable ℂ (fun z => residuePoly (a z) (b z) (c z) h) := by
  exact triNumerator_differentiable ha hb hc (differentiable_const 1) h

noncomputable def eulerParameter (p : ℕ) (u s : ℂ) : ℂ := u*(p:ℂ)^(-s)
noncomputable def primeCorrection (p : ℕ) (shifts : Fin 4 → ℂ) (u : ℂ) (h : ℕ) (s : ℂ) : ℂ :=
  numerator (primeRoot p (shifts 0)) (primeRoot p (shifts 1))
    (primeRoot p (shifts 2)) (primeRoot p (shifts 3)) h (eulerParameter p u s)

theorem eulerParameter_entire (p : ℕ) (hp : p ≠ 0) (u : ℂ) :
    Differentiable ℂ (eulerParameter p u) := by
  have hp' : (p:ℂ) ≠ 0 := by exact_mod_cast hp
  exact (differentiable_id.neg.const_cpow (Or.inl hp')).const_mul u

theorem primeCorrection_entire (p : ℕ) (hp : p ≠ 0) (shifts : Fin 4 → ℂ) (u : ℂ) (h : ℕ) :
    Differentiable ℂ (primeCorrection p shifts u h) := by
  exact numerator_differentiable (differentiable_const _) (differentiable_const _)
    (differentiable_const _) (differentiable_const _) (eulerParameter_entire p hp u) h

theorem eulerParameter_hasDerivAt (p : ℕ) (hp : p ≠ 0) (u s : ℂ) :
    HasDerivAt (eulerParameter p u) (-Complex.log (p:ℂ)*eulerParameter p u s) s := by
  have hp' : (p:ℂ) ≠ 0 := by exact_mod_cast hp
  have H := ((hasDerivAt_id s).neg.const_cpow (Or.inl hp')).const_mul u
  change HasDerivAt (eulerParameter p u) (u*((p:ℂ)^(-s)*Complex.log (p:ℂ)*(-1))) s at H
  convert! H using 1
  unfold eulerParameter
  ring

theorem primeCorrection_continuous (p : ℕ) (hp : p ≠ 0) (shifts : Fin 4 → ℂ) (u : ℂ) (h : ℕ) :
    Continuous (primeCorrection p shifts u h) :=
  (primeCorrection_entire p hp shifts u h).continuous

end SixthMoment.Source.NoDPResidues
