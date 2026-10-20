import Mathlib.Algebra.Polynomial.Eval.Degree
import SixthMoment.Denominator.Gram.Algebra
import SixthMoment.Zeta.Centering.ShiftDerivatives

namespace SixthMoment
open Complex MeasureTheory Set Polynomial Filter Metric
open scoped Topology BigOperators ComplexConjugate
noncomputable section
set_option maxHeartbeats 0

theorem d06_reflectedTestPolynomial_coeff (q : ℝ[X]) (m : ℕ) :
    (reflectedTestPolynomial q).coeff m = q.coeff m * (-1)^m := by
  unfold reflectedTestPolynomial
  simpa only [C_neg,C_1,neg_one_mul] using
    (Polynomial.comp_C_mul_X_coeff (p := q) (r := (-1 : ℝ)) (n := m))

theorem d06_reflectedTestPolynomial_natDegree_le (q : ℝ[X]) :
    (reflectedTestPolynomial q).natDegree ≤ q.natDegree := by
  simpa only [reflectedTestPolynomial,natDegree_neg,natDegree_X,mul_one] using
    (Polynomial.natDegree_comp_le (p := q) (q := -X))

private theorem d06_minus_neg_analyticAt_zero (T t : ℝ) :
    AnalyticAt ℂ (fun z => zetaCMinus T t (-z)) 0 := by
  have hs : 1-criticalLinePoint t ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [sub_re,one_re,criticalLinePoint_re] at hr
    norm_num at hr
  have hz := analyticOn_riemannZeta (1-criticalLinePoint t) (by simpa using hs)
  have hz' : AnalyticAt ℂ riemannZeta
      (1-criticalLinePoint t + -(0 : ℂ)/(Real.log T : ℂ)) := by simpa using hz
  have ha : AnalyticAt ℂ (fun z : ℂ =>
      1-criticalLinePoint t + -z/(Real.log T : ℂ)) 0 := by fun_prop
  have he : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-z/2)) 0 := by fun_prop
  exact he.mul (hz'.comp (f := fun z : ℂ =>
    1-criticalLinePoint t + -z/(Real.log T : ℂ)) ha)

theorem d06ReflectionDerivative_eq_error {T : ℝ} (hT : 1<T) (t : ℝ) (m : ℕ) :
    (criticalChi t)⁻¹ * centeredZetaDerivative T m (criticalLinePoint t) -
      (-1 : ℂ)^m * centeredZetaDerivative T m (1-criticalLinePoint t) =
    ∑ j ∈ Finset.range (m+1), (m.choose j : ℂ) *
      iteratedDeriv j (centeringError T t) 0 * (-1 : ℂ)^(m-j) *
        centeredZetaDerivative T (m-j) (1-criticalLinePoint t) := by
  have hlocal : (fun z => (criticalChi t)⁻¹*zetaCPlus T t z-zetaCMinus T t (-z))
      =ᶠ[𝓝 0] (fun z => centeringError T t z*zetaCMinus T t (-z)) := by
    have hc : Continuous (fun z : ℂ => (centeringShift T t z).re) := by
      unfold centeringShift
      fun_prop
    have ho : IsOpen {z : ℂ | 0 < (centeringShift T t z).re ∧
        (centeringShift T t z).re < 1} :=
      (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
    have hzero : (0 : ℂ) ∈ {z : ℂ | 0 < (centeringShift T t z).re ∧
        (centeringShift T t z).re < 1} := by norm_num [centeringShift]
    filter_upwards [ho.mem_nhds hzero] with z hz
    exact centering_generator_error T t z hz
  have hplus : ContDiffAt ℂ m (zetaCPlus T t) 0 := by
    have hs := analyticOn_riemannZeta (criticalLinePoint t)
      (by simpa using criticalLinePoint_ne_one t)
    have hz : AnalyticAt ℂ (fun z : ℂ =>
        riemannZeta (criticalLinePoint t+z/(Real.log T : ℂ))) 0 := by
      have hs' : AnalyticAt ℂ riemannZeta (criticalLinePoint t+0/(Real.log T : ℂ)) := by
        simpa using hs
      exact hs'.comp (f := fun z : ℂ => criticalLinePoint t+z/(Real.log T : ℂ)) (by fun_prop)
    exact ((by fun_prop : AnalyticAt ℂ (fun z : ℂ => Complex.exp (z/2)) 0).mul hz).contDiffAt
  have hminus : ContDiffAt ℂ m (fun z => zetaCMinus T t (-z)) 0 :=
    (d06_minus_neg_analyticAt_zero T t).contDiffAt
  have herr : ContDiffAt ℂ m (centeringError T t) 0 :=
    (centeringError_analyticAt (by norm_num [centeringShift])).contDiffAt
  have hd := hlocal.iteratedDeriv_eq m
  rw [iteratedDeriv_fun_sub (contDiffAt_const.mul hplus) hminus,
    iteratedDeriv_const_mul_field,iteratedDeriv_comp_neg,
    iteratedDeriv_fun_mul herr hminus] at hd
  simp only [neg_zero,iteratedDeriv_comp_neg,smul_eq_mul,mul_assoc] at hd
  have hp (n : ℕ) : iteratedDeriv n (zetaCPlus T t) 0 =
      centeredZetaDerivative T n (criticalLinePoint t) :=
    iteratedDeriv_shiftedZetaGenerator_of_one_lt T (criticalLinePoint t) n hT
      (criticalLinePoint_ne_one t)
  have hlow : 1-criticalLinePoint t ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    norm_num [criticalLinePoint] at hre
  have hm (n : ℕ) : iteratedDeriv n (zetaCMinus T t) 0 =
      centeredZetaDerivative T n (1-criticalLinePoint t) :=
    iteratedDeriv_shiftedZetaGenerator_of_one_lt T (1-criticalLinePoint t) n hT hlow
  simp_rw [hp,hm] at hd
  simpa only [mul_assoc] using hd

theorem d06PolynomialReflectionError_eq_sum {T : ℝ} (hT : 1<T) (t : ℝ)
    (q : ℝ[X]) (hq : q.natDegree≤4) :
    d06PolynomialReflectionError T t q =
      ∑ m ∈ Finset.range 5, (q.coeff m : ℂ) *
        (∑ j ∈ Finset.range (m+1), (m.choose j : ℂ) *
          iteratedDeriv j (centeringError T t) 0 * (-1 : ℂ)^(m-j) *
            centeredZetaDerivative T (m-j) (1-criticalLinePoint t)) := by
  simp_rw [← d06ReflectionDerivative_eq_error hT t]
  unfold d06PolynomialReflectionError zetaCp zetaPolynomialDerivative
  rw [q.sum_over_range' (fun _ => by simp) 5 (by omega),
    (reflectedTestPolynomial q).sum_over_range' (fun _ => by simp) 5
      (lt_of_le_of_lt (d06_reflectedTestPolynomial_natDegree_le q) (by omega))]
  simp only [Finset.mul_sum,d06_reflectedTestPolynomial_coeff,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

def d06ReflectionConstant (q : ℝ[X]) : ℝ :=
  ∑ m ∈ Finset.range 5, ‖(q.coeff m : ℂ)‖ *
    (∑ j ∈ Finset.range (m+1), (m.choose j : ℝ)*(j.factorial : ℝ)*
      |centeringUniformConstant 1|)

def d06LowerDerivativeNormSum (T t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 5, ‖centeredZetaDerivative T k (1-criticalLinePoint t)‖

theorem d06ReflectionConstant_nonneg (q : ℝ[X]) : 0≤d06ReflectionConstant q := by
  unfold d06ReflectionConstant
  positivity

theorem d06PolynomialReflectionError_eventually_norm_bound
    (q : ℝ[X]) (hq : q.natDegree≤4) :
    ∀ᶠ T : ℝ in atTop,∀ t∈Icc T (2*T),
      ‖d06PolynomialReflectionError T t q‖ ≤
        (d06ReflectionConstant q/Real.log T)*d06LowerDerivativeNormSum T t := by
  have hall : ∀ᶠ T : ℝ in atTop,∀ j : Fin 5,∀ x∈Icc (1:ℝ) 2,
      ‖iteratedDeriv j.val (centeringError T (T*x)) 0‖ ≤
        (j.val.factorial:ℝ)*(centeringUniformConstant 1/Real.log T) := by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [centeringError_uniform_shift_derivative_bound j.val 0] with T hT
    intro x hx
    simpa using hT x hx 0 (by simp)
  filter_upwards [hall,eventually_gt_atTop (1:ℝ)] with T herrors hT
  intro t ht
  have hT0 : 0<T := zero_lt_one.trans hT
  have hL : 0<Real.log T := Real.log_pos hT
  have hx : t/T∈Icc (1:ℝ) 2 := by
    constructor
    · exact (le_div_iff₀ hT0).mpr (by simpa using ht.1)
    · exact (div_le_iff₀ hT0).mpr ht.2
  have hE (j : ℕ) (hj : j≤4) :
      ‖iteratedDeriv j (centeringError T t) 0‖ ≤
        (j.factorial:ℝ)*(|centeringUniformConstant 1|/Real.log T) := by
    have he := herrors ⟨j,by omega⟩ (t/T) hx
    rw [mul_div_cancel₀ _ hT0.ne'] at he
    exact he.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (le_abs_self _) hL.le) (by positivity))
  have hS : 0≤d06LowerDerivativeNormSum T t := by
    unfold d06LowerDerivativeNormSum
    positivity
  have hsingle (k : ℕ) (hk : k≤4) :
      ‖centeredZetaDerivative T k (1-criticalLinePoint t)‖≤d06LowerDerivativeNormSum T t := by
    unfold d06LowerDerivativeNormSum
    exact Finset.single_le_sum
      (f := fun i => ‖centeredZetaDerivative T i (1-criticalLinePoint t)‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  rw [d06PolynomialReflectionError_eq_sum hT t q hq]
  calc
    _ ≤ ∑ m ∈ Finset.range 5, ‖(q.coeff m : ℂ)‖ *
        (∑ j ∈ Finset.range (m+1), (m.choose j : ℝ)*
          ‖iteratedDeriv j (centeringError T t) 0‖*
            ‖centeredZetaDerivative T (m-j) (1-criticalLinePoint t)‖) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      gcongr
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      simp
    _ ≤ ∑ m ∈ Finset.range 5, ‖(q.coeff m : ℂ)‖ *
        (∑ j ∈ Finset.range (m+1), (m.choose j : ℝ)*
          ((j.factorial:ℝ)*(|centeringUniformConstant 1|/Real.log T))*
            d06LowerDerivativeNormSum T t) := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro j hj
      have hm' : m≤4 := by have := Finset.mem_range.mp hm; omega
      have hj' : j≤m := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
      gcongr
      · exact hE j (hj'.trans hm')
      · exact hsingle (m-j) (Nat.sub_le m j |>.trans hm')
    _ = (d06ReflectionConstant q/Real.log T)*d06LowerDerivativeNormSum T t := by
      unfold d06ReflectionConstant
      simp_rw [div_eq_mul_inv]
      calc
        _ = ∑ m ∈ Finset.range 5, (‖(q.coeff m : ℂ)‖ *
            (∑ j ∈ Finset.range (m+1), (m.choose j : ℝ)*(j.factorial : ℝ)*
              |centeringUniformConstant 1|)) *
                ((Real.log T)⁻¹*d06LowerDerivativeNormSum T t) := by
          apply Finset.sum_congr rfl
          intro m _
          rw [mul_assoc]
          congr 1
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [← Finset.sum_mul]; ring

end
end SixthMoment
