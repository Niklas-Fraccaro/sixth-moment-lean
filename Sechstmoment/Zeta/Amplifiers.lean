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
import Std

/-!
# The manuscript's actual U/V tests

These definitions use the Riemann zeta function and its complex derivatives.
They instantiate the exact phase projection of §1.1, and also assemble the 250
rows of Appendix A with their unscaled integer coefficients. They introduce no
asymptotic moment formula. The profile sum is indexed by `n+1` to exclude zero;
for the supported profiles and `T > 1` it is proved to be a finite Dirichlet sum.
-/

namespace Sechstmoment

open Complex Polynomial
open scoped ComplexConjugate

noncomputable section

/-- `A_f(s) = ∑_{n≥1} f(log n/log T) n⁻ˢ`. The sum is finite for the
supported profiles used below when `T > 1`. -/
def profileDirichletSum (T : ℝ) (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (f (Real.log (n + 1 : ℝ) / Real.log T) : ℂ) / (n + 1 : ℂ) ^ s

/-- Compact support above `a` makes the displayed Dirichlet series a literal
finite sum of length `⌊Tᵃ⌋`. -/
theorem profileDirichletSum_eq_finite {T : ℝ} (hT : 1 < T) (a : ℝ)
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, a < x → f x = 0) (s : ℂ) :
    profileDirichletSum T f s =
      ∑ n ∈ Finset.range ⌊T ^ a⌋₊,
        (f (Real.log (n + 1 : ℝ) / Real.log T) : ℂ) / (n + 1 : ℂ) ^ s := by
  unfold profileDirichletSum
  apply tsum_eq_sum
  intro n hn
  have hn' : ⌊T ^ a⌋₊ < n + 1 := by
    have : ⌊T ^ a⌋₊ ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    omega
  have hpow : T ^ a < (n + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_of_floor_lt hn'
  have hlog : a * Real.log T < Real.log (n + 1 : ℝ) :=
    Real.lt_log_of_rpow_lt (lt_trans zero_lt_one hT) hpow
  have harg : a < Real.log (n + 1 : ℝ) / Real.log T :=
    (lt_div_iff₀ (Real.log_pos hT)).mpr hlog
  rw [hf _ harg]
  simp

theorem profileDirichletSum_conj (T : ℝ) (f : ℝ → ℝ) (s : ℂ) :
    profileDirichletSum T f (conj s) = conj (profileDirichletSum T f s) := by
  unfold profileDirichletSum
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  rw [map_div₀, conj_ofReal]
  have harg : (n + 1 : ℂ).arg ≠ Real.pi := by
    have hcast : (n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.natCast_arg]
    exact Real.pi_pos.ne
  have hcpow : (n + 1 : ℂ) ^ conj s = conj ((n + 1 : ℂ) ^ s) := by
    simpa only [map_add, conj_natCast, map_one] using Complex.cpow_conj (n + 1 : ℂ) s harg
  rw [hcpow]

end

end Sechstmoment
