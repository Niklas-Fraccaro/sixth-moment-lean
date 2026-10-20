import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
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


namespace Sechstmoment
open Complex Filter Set
open scoped Topology

noncomputable section

theorem gammaReal_differentiableAt_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  unfold Gammaℝ
  apply DifferentiableAt.mul
  · exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · apply (Complex.differentiableAt_Gamma (s/2) ?_).comp s
      (differentiableAt_id.div_const (2 : ℂ))
    intro n hn
    have hpos : 0 < (s/2).re := by simp only [div_ofNat_re]; positivity
    have hre := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at hre
    have hnpos : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

theorem gammaReal_shift_ratio (s u : ℂ) :
    Gammaℝ (s+u)/Gammaℝ s = (Real.pi : ℂ)^(-u/2) *
      (Gamma ((s+u)/2)/Gamma (s/2)) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : (Real.pi : ℂ)^(-(s+u)/2) =
      (Real.pi : ℂ)^(-s/2) * (Real.pi : ℂ)^(-u/2) := by
    rw [← Complex.cpow_add _ _ hp]
    congr 1
    ring
  simp only [Gammaℝ_def, he]
  rw [mul_assoc, mul_div_mul_left _ _ (by simp [hp])]
  rw [mul_div_assoc]

end
end Sechstmoment
