import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import SixthMoment.Arithmetic.Exact.Polynomials
import Std

namespace SixthMoment
open scoped BigOperators

noncomputable def homogeneousFour (r : Nat) (q₀ q₁ q₂ q₃ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (r+1), ∑ j ∈ Finset.range (r-i+1),
    ∑ k ∈ Finset.range (r-i-j+1), q₀^i*q₁^j*q₂^k*q₃^(r-i-j-k)
noncomputable def simplexMonomialAverage (r : Nat) (q₀ q₁ q₂ q₃ : ℝ) : ℝ :=
  (6 * (Finite.factorial r : ℝ) / (Finite.factorial (r+3) : ℝ)) *
    homogeneousFour r q₀ q₁ q₂ q₃
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false

end SixthMoment
