import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import SixthMoment.Zeta.Amplifiers
import SixthMoment.Zeta.Centering.Exact
import SixthMoment.Zeta.Moments.Shifts
import Std


namespace SixthMoment
open Complex MeasureTheory Set
open scoped ComplexConjugate BigOperators
open Polynomial

noncomputable section

def shiftedFourthProduct (t : ℝ) (α : MomentShifts) : ℂ :=
  riemannZeta (criticalLinePoint t + α 0) *
    riemannZeta (criticalLinePoint t + α 1) *
    riemannZeta (1-criticalLinePoint t + α 2) *
    riemannZeta (1-criticalLinePoint t + α 3)

def allPositiveFourthProduct (t : ℝ) (α : MomentShifts) : ℂ :=
  riemannZeta (criticalLinePoint t + α 0) *
    riemannZeta (criticalLinePoint t + α 1) *
    riemannZeta (criticalLinePoint t - α 2) *
    riemannZeta (criticalLinePoint t - α 3)

def twistedFourthIntegrand (T t : ℝ) (α : MomentShifts)
    (f g Φ : ℝ → ℝ) : ℂ :=
  (Φ (t/T) : ℂ) * shiftedFourthProduct t α *
    profileDirichletSum T f (criticalLinePoint t) *
    profileDirichletSum T g (1-criticalLinePoint t)

def chiTwistedFourthIntegrand (T t : ℝ) (α : MomentShifts)
    (f g Φ : ℝ → ℝ) : ℂ :=
  (Φ (t/T) : ℂ) * shiftedFourthProduct t α * criticalChi t *
    profileDirichletSum T f (1-criticalLinePoint t) *
    profileDirichletSum T g (1-criticalLinePoint t)

def twistedFourthMoment (T : ℝ) (α : MomentShifts)
    (f g Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, twistedFourthIntegrand T t α f g Φ

def chiTwistedFourthMoment (T : ℝ) (α : MomentShifts)
    (f g Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, chiTwistedFourthIntegrand T t α f g Φ

def dpArchimedeanCorrection (t : ℝ) (α : MomentShifts) : ℂ :=
  zetaChi (1-criticalLinePoint t + α 2) / zetaChi (1-criticalLinePoint t) *
    (zetaChi (1-criticalLinePoint t + α 3) / zetaChi (1-criticalLinePoint t))

theorem profileDirichletSum_one_sub (T t : ℝ) (f : ℝ → ℝ) :
    profileDirichletSum T f (1-criticalLinePoint t) =
      conj (profileDirichletSum T f (criticalLinePoint t)) := by
  rw [criticalLinePoint_one_sub]
  exact profileDirichletSum_conj T f (criticalLinePoint t)

theorem twistedFourthIntegrand_conjugate_form (T t : ℝ) (α : MomentShifts)
    (f g Φ : ℝ → ℝ) :
    twistedFourthIntegrand T t α f g Φ =
      (Φ (t/T) : ℂ) * shiftedFourthProduct t α *
        profileDirichletSum T f (criticalLinePoint t) *
        conj (profileDirichletSum T g (criticalLinePoint t)) := by
  simp only [twistedFourthIntegrand, profileDirichletSum_one_sub]

theorem chiTwistedFourthIntegrand_conjugate_form (T t : ℝ) (α : MomentShifts)
    (f g Φ : ℝ → ℝ) :
    chiTwistedFourthIntegrand T t α f g Φ =
      (Φ (t/T) : ℂ) * shiftedFourthProduct t α * criticalChi t *
        conj (profileDirichletSum T f (criticalLinePoint t) *
          profileDirichletSum T g (criticalLinePoint t)) := by
  simp only [chiTwistedFourthIntegrand, profileDirichletSum_one_sub, map_mul]
  ring

theorem shiftedFourthProduct_functional_equations (t : ℝ) (α : MomentShifts)
    (h₂ : 0 < (1-criticalLinePoint t + α 2).re ∧
      (1-criticalLinePoint t + α 2).re < 1)
    (h₃ : 0 < (1-criticalLinePoint t + α 3).re ∧
      (1-criticalLinePoint t + α 3).re < 1) :
    shiftedFourthProduct t α =
      zetaChi (1-criticalLinePoint t + α 2) *
        zetaChi (1-criticalLinePoint t + α 3) * allPositiveFourthProduct t α := by
  unfold shiftedFourthProduct allPositiveFourthProduct
  rw [riemannZeta_strip_functional_equation h₂.1 h₂.2,
    riemannZeta_strip_functional_equation h₃.1 h₃.2]
  simp only [show ∀ z : ℂ, 1-(1-criticalLinePoint t+z) = criticalLinePoint t-z
    from fun z => by ring]
  ring

theorem chiTwistedFourthIntegrand_functional_equation (T t : ℝ)
    (α : MomentShifts) (f g Φ : ℝ → ℝ)
    (h₂ : 0 < (1-criticalLinePoint t + α 2).re ∧
      (1-criticalLinePoint t + α 2).re < 1)
    (h₃ : 0 < (1-criticalLinePoint t + α 3).re ∧
      (1-criticalLinePoint t + α 3).re < 1) :
    chiTwistedFourthIntegrand T t α f g Φ =
      (Φ (t/T) : ℂ) * zetaChi (1-criticalLinePoint t) *
        dpArchimedeanCorrection t α * allPositiveFourthProduct t α *
        profileDirichletSum T f (1-criticalLinePoint t) *
        profileDirichletSum T g (1-criticalLinePoint t) := by
  have hstrip : 0 < (criticalLinePoint t).re ∧ (criticalLinePoint t).re < 1 := by
    simp only [criticalLinePoint_re]
    norm_num
  have hrecip := zetaChi_one_sub_mul hstrip.1 hstrip.2
  have hnonzero : zetaChi (1-criticalLinePoint t) ≠ 0 :=
    zetaChi_ne_zero_strip (by norm_num [sub_re, criticalLinePoint_re])
      (by norm_num [sub_re, criticalLinePoint_re])
  unfold chiTwistedFourthIntegrand dpArchimedeanCorrection
  rw [shiftedFourthProduct_functional_equations t α h₂ h₃]
  rw [← zetaChi_criticalLinePoint]
  field_simp
  linear_combination
    (Φ (t/T) : ℂ) * zetaChi (1-criticalLinePoint t+α 2) *
      zetaChi (1-criticalLinePoint t+α 3) * allPositiveFourthProduct t α *
      profileDirichletSum T f (1-criticalLinePoint t) *
      profileDirichletSum T g (1-criticalLinePoint t) * hrecip

end
end SixthMoment
