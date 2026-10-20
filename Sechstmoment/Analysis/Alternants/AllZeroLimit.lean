import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.Topology.Instances.Matrix
import Sechstmoment.Analysis.Alternants.ShiftLimit
import Std


namespace Sechstmoment
open Filter MeasureTheory
open scoped Topology BigOperators

set_option maxHeartbeats 0

noncomputable def expSecondNodeDifference (q : ℂ) (x : Fin 4 → ℂ) : ℂ :=
  q^2*simplexTriangleExpIntegral (x 0) (x 1) (x 2) q 0 1

noncomputable def expThirdNodeDifference (q : ℂ) (x : Fin 4 → ℂ) : ℂ :=
  (q^3/6)*simplexExpGenerator x q

theorem expSecondNodeDifference_continuous (q : ℂ) :
    Continuous (expSecondNodeDifference q) := by
  unfold expSecondNodeDifference simplexTriangleExpIntegral
  fun_prop

theorem expThirdNodeDifference_continuous (q : ℂ) :
    Continuous (expThirdNodeDifference q) := by
  exact continuous_const.mul
    (simplexExpGenerator_continuous_comp continuous_id continuous_const)

theorem expSecondNodeDifference_distinct (q : ℂ) (x : Fin 4 → ℂ)
    (hx : Function.Injective x) :
    expSecondNodeDifference q x =
      Complex.exp (q*x 0)/((x 0-x 1)*(x 0-x 2))+
      Complex.exp (q*x 1)/((x 1-x 0)*(x 1-x 2))+
      Complex.exp (q*x 2)/((x 2-x 0)*(x 2-x 1)) := by
  have h01 := hx.ne (show (0:Fin 4) ≠ 1 by decide)
  have h02 := hx.ne (show (0:Fin 4) ≠ 2 by decide)
  have h12 := hx.ne (show (1:Fin 4) ≠ 2 by decide)
  unfold expSecondNodeDifference
  by_cases hq : q = 0
  · simp only [hq, zero_pow (by decide : (2:ℕ) ≠ 0), zero_mul, Complex.exp_zero]
    field_simp [sub_ne_zero.mpr h01, sub_ne_zero.mpr h02, sub_ne_zero.mpr h12,
      sub_ne_zero.mpr h01.symm, sub_ne_zero.mpr h02.symm, sub_ne_zero.mpr h12.symm]
    ring
  · rw [simplexTriangleExpIntegral_closed _ _ _ _ _ _ hq h01 h02 h12]
    norm_num
    field_simp [hq, sub_ne_zero.mpr h01, sub_ne_zero.mpr h02, sub_ne_zero.mpr h12,
      sub_ne_zero.mpr h01.symm, sub_ne_zero.mpr h02.symm, sub_ne_zero.mpr h12.symm]
    ring

theorem expThirdNodeDifference_distinct (q : ℂ) (x : Fin 4 → ℂ)
    (hx : Function.Injective x) :
    expThirdNodeDifference q x =
      ∑ j : Fin 4, Complex.exp (q*x j)/
        (∏ k ∈ (Finset.univ : Finset (Fin 4)).erase j, (x j-x k)) := by
  unfold expThirdNodeDifference
  by_cases hq : q = 0
  · have h01 := hx.ne (show (0:Fin 4) ≠ 1 by decide)
    have h02 := hx.ne (show (0:Fin 4) ≠ 2 by decide)
    have h03 := hx.ne (show (0:Fin 4) ≠ 3 by decide)
    have h12 := hx.ne (show (1:Fin 4) ≠ 2 by decide)
    have h13 := hx.ne (show (1:Fin 4) ≠ 3 by decide)
    have h23 := hx.ne (show (2:Fin 4) ≠ 3 by decide)
    have hu0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
    have hu1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
    have hu2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
    have hu3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
    norm_num [hq, Fin.sum_univ_succ, hu0, hu1, hu2, hu3, Finset.prod_insert]
    field_simp [sub_ne_zero.mpr h01, sub_ne_zero.mpr h02, sub_ne_zero.mpr h03,
      sub_ne_zero.mpr h12, sub_ne_zero.mpr h13, sub_ne_zero.mpr h23,
      sub_ne_zero.mpr h01.symm, sub_ne_zero.mpr h02.symm, sub_ne_zero.mpr h03.symm,
      sub_ne_zero.mpr h12.symm, sub_ne_zero.mpr h13.symm, sub_ne_zero.mpr h23.symm]
    ring
  · rw [simplexExpGenerator_distinct x q hx hq]
    simp_rw [mul_comm q]
    field_simp

noncomputable def expNewtonMatrix (x q : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![(fun j => Complex.exp (q j*x 0)),
    (fun j => Complex.exp (q j*x 0)*expFirstSlope (q j) (x 1-x 0)),
    (fun j => expSecondNodeDifference (q j) x),
    (fun j => expThirdNodeDifference (q j) x)]

noncomputable def expNewtonTransition (x : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![1,0,0,0],
    ![1,x 1-x 0,0,0],
    ![1,x 2-x 0,(x 2-x 0)*(x 2-x 1),0],
    ![1,x 3-x 0,(x 3-x 0)*(x 3-x 1),(x 3-x 0)*(x 3-x 1)*(x 3-x 2)]]

theorem expFirstNodeDifference_distinct (q : ℂ) (x : Fin 4 → ℂ)
    (h01 : x 0 ≠ x 1) :
    Complex.exp (q*x 0)*expFirstSlope q (x 1-x 0) =
      (Complex.exp (q*x 1)-Complex.exp (q*x 0))/(x 1-x 0) := by
  rw [expFirstSlope_of_ne _ _ (sub_ne_zero.mpr h01.symm)]
  have he : Complex.exp (q*x 0)*Complex.exp ((x 1-x 0)*q) = Complex.exp (q*x 1) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [← mul_div_assoc, mul_sub, mul_one, he]

theorem expAlternantMatrix_newton (x q : Fin 4 → ℂ) (hx : Function.Injective x) :
    expAlternantMatrix x q = expNewtonTransition x * expNewtonMatrix x q := by
  have h01 := hx.ne (show (0:Fin 4) ≠ 1 by decide)
  have h02 := hx.ne (show (0:Fin 4) ≠ 2 by decide)
  have h03 := hx.ne (show (0:Fin 4) ≠ 3 by decide)
  have h12 := hx.ne (show (1:Fin 4) ≠ 2 by decide)
  have h13 := hx.ne (show (1:Fin 4) ≠ 3 by decide)
  have h23 := hx.ne (show (2:Fin 4) ≠ 3 by decide)
  have hu0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have hu1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have hu2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have hu3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i
  · simp [expAlternantMatrix, expNewtonTransition, expNewtonMatrix,
      Fin.sum_univ_succ, mul_comm]
  all_goals norm_num [expAlternantMatrix, expNewtonTransition, expNewtonMatrix,
    Fin.sum_univ_succ]
  all_goals simp only [expFirstNodeDifference_distinct (q j) x h01,
    expSecondNodeDifference_distinct (q j) x hx,
    expThirdNodeDifference_distinct (q j) x hx]
  all_goals norm_num [Fin.sum_univ_succ, hu0, hu1, hu2, hu3, Finset.prod_insert, mul_comm]
  all_goals field_simp [sub_ne_zero.mpr h01, sub_ne_zero.mpr h02, sub_ne_zero.mpr h03,
    sub_ne_zero.mpr h12, sub_ne_zero.mpr h13, sub_ne_zero.mpr h23,
    sub_ne_zero.mpr h01.symm, sub_ne_zero.mpr h02.symm, sub_ne_zero.mpr h03.symm,
    sub_ne_zero.mpr h12.symm, sub_ne_zero.mpr h13.symm, sub_ne_zero.mpr h23.symm]
  all_goals ring

theorem expNewtonTransition_det (x : Fin 4 → ℂ) :
    (expNewtonTransition x).det = fourVandermonde x := by
  rw [determinant_four_six_minors]
  norm_num [matrixMinorTwo, expNewtonTransition, fourVandermonde]
  ring

theorem exponentialAlternant_newton (x q : Fin 4 → ℂ) (hx : Function.Injective x) :
    exponentialAlternant x q = Complex.exp (x 0+x 1)*(expNewtonMatrix x q).det := by
  unfold exponentialAlternant
  rw [expAlternantMatrix_newton x q hx, Matrix.det_mul, expNewtonTransition_det]
  have hV : fourVandermonde x ≠ 0 := by
    unfold fourVandermonde
    repeat apply mul_ne_zero
    all_goals apply sub_ne_zero.mpr; exact hx.ne (by decide)
  field_simp

theorem expNewtonMatrix_continuous (q : Fin 4 → ℂ) :
    Continuous (fun x => expNewtonMatrix x q) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i
  all_goals simp only [expNewtonMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.reduceFinMk]
  · fun_prop
  · exact (by fun_prop : Continuous (fun x : Fin 4 → ℂ => Complex.exp (q j*x 0))).mul
      ((expFirstSlope_continuous (q j)).comp (by fun_prop))
  · exact expSecondNodeDifference_continuous (q j)
  · exact expThirdNodeDifference_continuous (q j)

theorem simplexTriangleExpIntegral_nodes_zero (q : ℂ) :
    simplexTriangleExpIntegral 0 0 0 q 0 1 = (1/2:ℂ) := by
  unfold simplexTriangleExpIntegral
  simp only [zero_mul, add_zero, mul_zero, Complex.exp_zero]
  simp_rw [intervalIntegral.integral_const, Complex.real_smul, mul_one, sub_zero]
  rw [intervalIntegral.integral_ofReal]
  have hr : (∫ x in (0:ℝ)..1, (1-x:ℝ)) = 1/2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun x : ℝ => x)
      (show IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1 from
        continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _)]
    norm_num
  rw [hr]
  norm_num

theorem simplexExpGenerator_nodes_zero (q : ℂ) :
    simplexExpGenerator (0 : Fin 4 → ℂ) q = 1 := by
  unfold simplexExpGenerator complexSimplexDot
  simp only [Pi.zero_apply, zero_mul, zero_add, mul_zero, Complex.exp_zero]
  exact complexSimplexExpectation_one

theorem expNewtonMatrix_zero (q : Fin 4 → ℂ) :
    expNewtonMatrix 0 q =
      ![(fun _ => 1), (fun j => q j), (fun j => (q j)^2/2), (fun j => (q j)^3/6)] := by
  ext i j
  fin_cases i
  all_goals norm_num [expNewtonMatrix, expSecondNodeDifference, expThirdNodeDifference,
    expFirstSlope_zero, simplexTriangleExpIntegral_nodes_zero, simplexExpGenerator_nodes_zero]
  ring

theorem expNewtonMatrix_zero_det (q : Fin 4 → ℂ) :
    (expNewtonMatrix 0 q).det = fourVandermonde q/12 := by
  rw [determinant_four_six_minors, expNewtonMatrix_zero]
  norm_num [matrixMinorTwo, fourVandermonde]
  ring

theorem exponentialAlternant_all_zero_limit (q : Fin 4 → ℂ) :
    Tendsto (fun x : Fin 4 → ℂ => exponentialAlternant x q)
      (𝓝[{x : Fin 4 → ℂ | Function.Injective x}] (0:Fin 4 → ℂ))
      (𝓝 (fourVandermonde q/12)) := by
  have he : Continuous (fun x : Fin 4 → ℂ => Complex.exp (x 0+x 1)) := by fun_prop
  have hc := he.mul ((expNewtonMatrix_continuous q).matrix_det)
  have ht := (hc.tendsto (0:Fin 4 → ℂ)).mono_left
    (nhdsWithin_le_nhds (s := {x : Fin 4 → ℂ | Function.Injective x}))
  simp only [Pi.mul_apply, Pi.zero_apply, zero_add, Complex.exp_zero, one_mul,
    expNewtonMatrix_zero_det] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (exponentialAlternant_newton x q hx).symm

theorem exponentialAlternant_joint_shift_limit_all (q : Fin 4 → ℂ) (z : ℂ)
    (hq : Function.Injective q) :
    Tendsto (fun x : Fin 4 → ℂ => exponentialAlternant x q)
      (𝓝[{x : Fin 4 → ℂ | Function.Injective x}] (![0,0,z,0]))
      (𝓝 (fourVandermonde q/12*simplexExpGenerator q z)) := by
  by_cases hz : z = 0
  · have hx : (![0,0,(0:ℂ),0] : Fin 4 → ℂ) = 0 := by
      funext i
      fin_cases i <;> simp
    simpa only [hz, hx, simplexExpGenerator_zero, mul_one] using
      exponentialAlternant_all_zero_limit q
  · exact exponentialAlternant_joint_shift_limit_eq_simplex q z hq hz

theorem fourVandermonde_zero_of_not_injective (q : Fin 4 → ℂ)
    (hq : ¬Function.Injective q) : fourVandermonde q = 0 := by
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hq
  have hd : (expNewtonMatrix 0 q).det = 0 := by
    apply Matrix.det_zero_of_column_eq hne
    intro k
    fin_cases k <;> simp [expNewtonMatrix, hij]
  rw [expNewtonMatrix_zero_det] at hd
  exact (div_eq_zero_iff.mp hd).resolve_right (by norm_num)

theorem exponentialAlternant_zero_of_not_injective (x q : Fin 4 → ℂ)
    (hq : ¬Function.Injective q) : exponentialAlternant x q = 0 := by
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hq
  have hd : (expAlternantMatrix x q).det = 0 := by
    apply Matrix.det_zero_of_column_eq hne
    intro k
    simp [expAlternantMatrix, hij]
  simp [exponentialAlternant, hd]

theorem exponentialAlternant_joint_shift_limit_unrestricted (q : Fin 4 → ℂ) (z : ℂ) :
    Tendsto (fun x : Fin 4 → ℂ => exponentialAlternant x q)
      (𝓝[{x : Fin 4 → ℂ | Function.Injective x}] (![0,0,z,0]))
      (𝓝 (fourVandermonde q/12*simplexExpGenerator q z)) := by
  classical
  by_cases hq : Function.Injective q
  · exact exponentialAlternant_joint_shift_limit_all q z hq
  · have hv := fourVandermonde_zero_of_not_injective q hq
    have he : (fun x : Fin 4 → ℂ => exponentialAlternant x q) = (fun _ => 0) := by
      funext x
      exact exponentialAlternant_zero_of_not_injective x q hq
    rw [he, hv]
    simp only [zero_div, zero_mul]
    exact tendsto_const_nhds

end Sechstmoment
