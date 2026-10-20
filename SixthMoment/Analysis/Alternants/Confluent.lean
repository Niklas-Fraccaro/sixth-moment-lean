import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import SixthMoment.Analysis.Alternants.Four
import Std


namespace SixthMoment
open scoped BigOperators

set_option maxHeartbeats 0

noncomputable def confluentExpMatrix (q : Fin 4 → ℂ) (z : ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![(fun _ => 1), (fun j => q j), (fun j => (q j)^2),
    (fun j => Complex.exp (z*q j))]

noncomputable def vandermondeCofactor (q : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![-((q 2-q 1)*(q 3-q 1)*(q 3-q 2)),
    (q 2-q 0)*(q 3-q 0)*(q 3-q 2),
    -((q 1-q 0)*(q 3-q 0)*(q 3-q 1)),
    (q 1-q 0)*(q 2-q 0)*(q 2-q 1)]

theorem confluentExpMatrix_det (q : Fin 4 → ℂ) (z : ℂ) :
    (confluentExpMatrix q z).det =
      ∑ j : Fin 4, Complex.exp (z*q j) * vandermondeCofactor q j := by
  rw [determinant_four_six_minors]
  norm_num [matrixMinorTwo, confluentExpMatrix, vandermondeCofactor,
    Fin.sum_univ_succ]
  ring

theorem fourVandermonde_div_nodeProduct (q : Fin 4 → ℂ)
    (hq : Function.Injective q) (j : Fin 4) :
    fourVandermonde q /
      (∏ k ∈ (Finset.univ : Finset (Fin 4)).erase j, (q j-q k)) =
      vandermondeCofactor q j := by
  have h01 : q 0 ≠ q 1 := hq.ne (by decide)
  have h02 : q 0 ≠ q 2 := hq.ne (by decide)
  have h03 : q 0 ≠ q 3 := hq.ne (by decide)
  have h12 : q 1 ≠ q 2 := hq.ne (by decide)
  have h13 : q 1 ≠ q 3 := hq.ne (by decide)
  have h23 : q 2 ≠ q 3 := hq.ne (by decide)
  have hu0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have hu1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have hu2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have hu3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  fin_cases j <;>
    norm_num [hu0, hu1, hu2, hu3, Finset.prod_insert,
      fourVandermonde, vandermondeCofactor] <;>
    field_simp [sub_ne_zero.mpr h01, sub_ne_zero.mpr h02, sub_ne_zero.mpr h03,
      sub_ne_zero.mpr h12, sub_ne_zero.mpr h13, sub_ne_zero.mpr h23,
      sub_ne_zero.mpr h01.symm, sub_ne_zero.mpr h02.symm, sub_ne_zero.mpr h03.symm,
      sub_ne_zero.mpr h12.symm, sub_ne_zero.mpr h13.symm, sub_ne_zero.mpr h23.symm] <;>
    ring

theorem confluentExpMatrix_det_divided_difference (q : Fin 4 → ℂ) (z : ℂ)
    (hq : Function.Injective q) :
    (confluentExpMatrix q z).det = fourVandermonde q *
      (∑ j : Fin 4, Complex.exp (z*q j) /
        (∏ k ∈ (Finset.univ : Finset (Fin 4)).erase j, (q j-q k))) := by
  rw [confluentExpMatrix_det, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show fourVandermonde q * (Complex.exp (z*q j) /
      (∏ k ∈ (Finset.univ : Finset (Fin 4)).erase j, (q j-q k))) =
      Complex.exp (z*q j) * (fourVandermonde q /
        (∏ k ∈ (Finset.univ : Finset (Fin 4)).erase j, (q j-q k))) by ring]
  rw [fourVandermonde_div_nodeProduct q hq j]

noncomputable def confluentExpGenerator (q : Fin 4 → ℂ) (z : ℂ) : ℂ :=
  (confluentExpMatrix q z).det / (2*z^3)

theorem confluentExpGenerator_eq_simplex (q : Fin 4 → ℂ) (z : ℂ)
    (hq : Function.Injective q) (hz : z ≠ 0) :
    confluentExpGenerator q z =
      fourVandermonde q / 12 * simplexExpGenerator q z := by
  rw [confluentExpGenerator, confluentExpMatrix_det_divided_difference q z hq,
    simplexExpGenerator_distinct q z hq hz]
  ring

end SixthMoment
