import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Sechstmoment.Analysis.Beta.Concentration
import Std


namespace Sechstmoment

open Complex Polynomial
open scoped ComplexConjugate

noncomputable section

def vEndpointProfile (η a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) η).indicator (betaScaledProfile η n (betaProfileIndex η a n)) x

theorem vEndpointProfile_zero_above (η a : ℝ) (n : ℕ) {x : ℝ} (hx : η < x) :
    vEndpointProfile η a n x = 0 := by
  apply Set.indicator_of_notMem
  exact fun h => (not_le_of_gt hx) h.2

def uEndpointProfile (ψ : ℝ → ℝ) (hstar a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  let h : ℝ := hstar / n
  h⁻¹ * ψ ((a - x) / h)

theorem uEndpointProfile_zero_above (ψ : ℝ → ℝ)
    (hψ : ∀ x : ℝ, x ≤ 0 → ψ x = 0) {hstar : ℝ} (hh : 0 < hstar)
    (a : ℝ) {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : a < x) :
    uEndpointProfile ψ hstar a n x = 0 := by
  change (hstar / n)⁻¹ * ψ ((a - x) / (hstar / n)) = 0
  have hhn : 0 < hstar / n := div_pos hh (by exact_mod_cast hn)
  rw [hψ _ (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.le) hhn.le), mul_zero]

end

end Sechstmoment
