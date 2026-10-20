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
import Sechstmoment.Zeta.FunctionalEquation
import Sechstmoment.Zeta.Gamma.Ratios
import Std


namespace Sechstmoment
open Complex Filter Set
open scoped Topology

noncomputable section

def zetaChi (s : ℂ) : ℂ := Gammaℝ (1-s) / Gammaℝ s

@[simp] theorem zetaChi_criticalLinePoint (t : ℝ) :
    zetaChi (criticalLinePoint t) = criticalChi t := rfl

theorem criticalChi_ne_zero (t : ℝ) : criticalChi t ≠ 0 := by
  intro h
  have hn := criticalChi_norm t
  simp only [h, norm_zero] at hn
  norm_num at hn

private theorem ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := by
  intro h
  simp only [h, zero_re] at hs
  exact (lt_irrefl 0) hs

theorem riemannZeta_strip_functional_equation {s : ℂ}
    (hlo : 0 < s.re) (hhi : s.re < 1) :
    riemannZeta s = zetaChi s * riemannZeta (1-s) := by
  have hs := ne_zero_of_re_pos hlo
  have hs' : 1-s ≠ 0 := ne_zero_of_re_pos (by simp only [sub_re, one_re]; linarith)
  have hg := Gammaℝ_ne_zero_of_re_pos hlo
  have hg' : Gammaℝ (1-s) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp only [sub_re, one_re]; linarith)
  rw [riemannZeta_def_of_ne_zero hs, zetaChi,
    riemannZeta_def_of_ne_zero hs', completedRiemannZeta_one_sub]
  field_simp

theorem zetaChi_ne_zero_strip {s : ℂ} (hlo : 0 < s.re) (hhi : s.re < 1) :
    zetaChi s ≠ 0 := by
  exact div_ne_zero
    (Gammaℝ_ne_zero_of_re_pos (by simp only [sub_re, one_re]; linarith))
    (Gammaℝ_ne_zero_of_re_pos hlo)

theorem zetaChi_one_sub_mul {s : ℂ} (hlo : 0 < s.re) (hhi : s.re < 1) :
    zetaChi (1-s) * zetaChi s = 1 := by
  have hg := Gammaℝ_ne_zero_of_re_pos hlo
  have hg' : Gammaℝ (1-s) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp only [sub_re, one_re]; linarith)
  simp only [zetaChi, sub_sub_cancel]
  field_simp

theorem zetaChi_analyticOnNhd_strip :
    AnalyticOnNhd ℂ zetaChi {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    apply DifferentiableAt.differentiableWithinAt
    unfold zetaChi
    apply DifferentiableAt.div
    · exact (gammaReal_differentiableAt_of_re_pos (by
        simp only [sub_re, one_re]; linarith [hs.2])).comp s (by fun_prop)
    · exact gammaReal_differentiableAt_of_re_pos hs.1
    · exact Gammaℝ_ne_zero_of_re_pos hs.1
  · exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)

theorem zetaChi_shift_ratio (s u : ℂ) :
    zetaChi (s+u)/zetaChi s = (Real.pi : ℂ)^u *
      (Gamma ((1-s-u)/2)/Gamma ((1-s)/2)) *
      (Gamma (s/2)/Gamma ((s+u)/2)) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : 1-(s+u) = (1-s)+(-u) := by ring
  have he : -(-u)/2 = u/2 := by ring
  have hn' : (1-s)+(-u) = 1-s-u := by ring
  simp only [zetaChi]
  rw [div_div_div_comm, hn, gammaReal_shift_ratio, gammaReal_shift_ratio, he, hn']
  have hpow : (Real.pi : ℂ)^(u/2)/(Real.pi : ℂ)^(-u/2) =
      (Real.pi : ℂ)^u := by
    rw [show -u/2 = -(u/2) by ring, Complex.cpow_neg, div_eq_mul_inv, inv_inv,
      ← Complex.cpow_add _ _ hp]
    congr 1
    ring
  rw [← hpow]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

end
end Sechstmoment
