import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import Sechstmoment.Analysis.Simplex.Moments


namespace Sechstmoment
open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 0

noncomputable def complexSimplexExpectation (f : ℝ → ℝ → ℝ → ℂ) : ℂ :=
  6 * ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1-x,
    ∫ w in (0 : ℝ)..1-x-y, f x y w

noncomputable def complexSimplexDot (q : Fin 4 → ℂ) (x y w : ℝ) : ℂ :=
  q 0 * x + q 1 * y + q 2 * w + q 3 * (1-x-y-w : ℝ)

noncomputable def simplexExpGenerator (q : Fin 4 → ℂ) (z : ℂ) : ℂ :=
  complexSimplexExpectation (fun x y w => Complex.exp (z * complexSimplexDot q x y w))

theorem integral_cexp_affine (l u : ℝ) (A B : ℂ) (hA : A ≠ 0) :
    (∫ t in l..u, Complex.exp (A*t+B)) =
      (Complex.exp (A*u+B)-Complex.exp (A*l+B))/A := by
  simp_rw [Complex.exp_add]
  rw [intervalIntegral.integral_mul_const, integral_exp_mul_complex hA]
  ring

theorem integral_cexp_simplex_line (a b z c : ℂ) (H : ℝ)
    (hz : z ≠ 0) (hab : a ≠ b) :
    (∫ x in (0 : ℝ)..H, Complex.exp (z*(a*x+b*(H-x : ℝ)+c))) =
      (Complex.exp (z*(a*H+c))-Complex.exp (z*(b*H+c)))/(z*(a-b)) := by
  have he (x : ℝ) : z*(a*x+b*(H-x : ℝ)+c) =
      (z*(a-b))*x+z*(b*H+c) := by push_cast; ring
  simp_rw [he]
  rw [integral_cexp_affine _ _ _ _ (mul_ne_zero hz (sub_ne_zero.mpr hab))]
  have hu : (z*(a-b))*(H:ℂ)+z*(b*H+c) = z*(a*H+c) := by ring
  rw [hu]
  simp

noncomputable def simplexTriangleExpIntegral (a b c z v : ℂ) (H : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..H, ∫ y in (0 : ℝ)..H-x,
    Complex.exp (z*(a*x+b*y+c*(H-x-y : ℝ)+v))

theorem simplexTriangleExpIntegral_closed (a b c z v : ℂ) (H : ℝ)
    (hz : z ≠ 0) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    simplexTriangleExpIntegral a b c z v H =
      (((Complex.exp (z*(a*H+v))-Complex.exp (z*(b*H+v)))/(z*(a-b))) -
       ((Complex.exp (z*(a*H+v))-Complex.exp (z*(c*H+v)))/(z*(a-c)))) /
        (z*(b-c)) := by
  have hi (x : ℝ) :
      (∫ y in (0 : ℝ)..H-x, Complex.exp (z*(a*x+b*y+c*(H-x-y : ℝ)+v))) =
        (Complex.exp (z*(b*(H-x : ℝ)+(a*x+v)))-
          Complex.exp (z*(c*(H-x : ℝ)+(a*x+v))))/(z*(b-c)) := by
    have he (y : ℝ) : z*(a*x+b*y+c*(H-x-y : ℝ)+v) =
        z*(b*y+c*((H-x)-y : ℝ)+(a*x+v)) := by push_cast; ring
    simp_rw [he]
    exact integral_cexp_simplex_line b c z (a*x+v) (H-x) hz hbc
  unfold simplexTriangleExpIntegral
  simp_rw [hi]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub]
  · have he (d : ℂ) (x : ℝ) : z*(d*(H-x : ℝ)+(a*x+v)) =
        z*(a*x+d*(H-x : ℝ)+v) := by ring
    simp_rw [he]
    rw [integral_cexp_simplex_line a b z v H hz hab,
      integral_cexp_simplex_line a c z v H hz hac]
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop

theorem simplexExpGenerator_iterated (q : Fin 4 → ℂ) (z : ℂ)
    (hz : z ≠ 0) (h23 : q 2 ≠ q 3) :
    simplexExpGenerator q z = 6 *
      (simplexTriangleExpIntegral (q 0) (q 1) (q 2) z 0 1 -
        simplexTriangleExpIntegral (q 0) (q 1) (q 3) z 0 1) / (z*(q 2-q 3)) := by
  have hi (x y : ℝ) :
      (∫ w in (0 : ℝ)..1-x-y, Complex.exp (z*complexSimplexDot q x y w)) =
      (Complex.exp (z*(q 2*(1-x-y : ℝ)+(q 0*x+q 1*y)))-
        Complex.exp (z*(q 3*(1-x-y : ℝ)+(q 0*x+q 1*y))))/(z*(q 2-q 3)) := by
    have he (w : ℝ) : z*complexSimplexDot q x y w =
        z*(q 2*w+q 3*((1-x-y)-w : ℝ)+(q 0*x+q 1*y)) := by
      unfold complexSimplexDot
      push_cast
      ring
    simp_rw [he]
    exact integral_cexp_simplex_line _ _ _ _ _ hz h23
  have hy (x : ℝ) :
      (∫ y in (0 : ℝ)..1-x,
        (Complex.exp (z*(q 2*(1-x-y : ℝ)+(q 0*x+q 1*y)))-
          Complex.exp (z*(q 3*(1-x-y : ℝ)+(q 0*x+q 1*y))))/(z*(q 2-q 3))) =
      ((∫ y in (0 : ℝ)..1-x, Complex.exp (z*(q 2*(1-x-y : ℝ)+(q 0*x+q 1*y))))-
        (∫ y in (0 : ℝ)..1-x, Complex.exp (z*(q 3*(1-x-y : ℝ)+(q 0*x+q 1*y))))) /
          (z*(q 2-q 3)) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub]
    all_goals apply Continuous.intervalIntegrable; fun_prop
  have hc (d : ℂ) : Continuous (fun x : ℝ =>
      ∫ y in (0 : ℝ)..1-x, Complex.exp (z*(d*(1-x-y : ℝ)+(q 0*x+q 1*y)))) := by
    fun_prop
  unfold simplexExpGenerator complexSimplexExpectation
  simp_rw [hi, hy]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    ((hc (q 2)).intervalIntegrable _ _) ((hc (q 3)).intervalIntegrable _ _)]
  have he (d : ℂ) (x y : ℝ) : z*(d*(1-x-y : ℝ)+(q 0*x+q 1*y)) =
      z*(q 0*x+q 1*y+d*(1-x-y : ℝ)+0) := by ring
  simp_rw [he]
  change 6 * ((simplexTriangleExpIntegral _ _ _ _ _ _ -
    simplexTriangleExpIntegral _ _ _ _ _ _) / _) = _
  ring

theorem simplexExpGenerator_distinct (q : Fin 4 → ℂ) (z : ℂ)
    (hq : Function.Injective q) (hz : z ≠ 0) :
    simplexExpGenerator q z = (6/z^3) *
      ∑ j : Fin 4, Complex.exp (z*q j) /
        (∏ k ∈ (Finset.univ : Finset (Fin 4)).erase j, (q j-q k)) := by
  have h01 : q 0 ≠ q 1 := hq.ne (by decide)
  have h02 : q 0 ≠ q 2 := hq.ne (by decide)
  have h03 : q 0 ≠ q 3 := hq.ne (by decide)
  have h12 : q 1 ≠ q 2 := hq.ne (by decide)
  have h13 : q 1 ≠ q 3 := hq.ne (by decide)
  have h23 : q 2 ≠ q 3 := hq.ne (by decide)
  rw [simplexExpGenerator_iterated q z hz h23,
    simplexTriangleExpIntegral_closed _ _ _ _ _ _ hz h01 h02 h12,
    simplexTriangleExpIntegral_closed _ _ _ _ _ _ hz h01 h03 h13]
  have hu0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have hu1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have hu2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have hu3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  norm_num [Fin.sum_univ_succ, hu0, hu1, hu2, hu3, Finset.prod_insert]
  field_simp [hz, sub_ne_zero.mpr h01, sub_ne_zero.mpr h02, sub_ne_zero.mpr h03,
    sub_ne_zero.mpr h12, sub_ne_zero.mpr h13, sub_ne_zero.mpr h23,
    sub_ne_zero.mpr h01.symm, sub_ne_zero.mpr h02.symm, sub_ne_zero.mpr h03.symm,
    sub_ne_zero.mpr h12.symm, sub_ne_zero.mpr h13.symm, sub_ne_zero.mpr h23.symm]
  ring

theorem complexSimplexExpectation_one :
    complexSimplexExpectation (fun _ _ _ => 1) = 1 := by
  unfold complexSimplexExpectation
  change (6 : ℂ) * (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1-x,
    ∫ w in (0 : ℝ)..1-x-y, ((1 : ℝ) : ℂ)) = 1
  simp_rw [intervalIntegral.integral_ofReal]
  exact_mod_cast simplexExpectation_one

theorem simplexExpGenerator_zero (q : Fin 4 → ℂ) : simplexExpGenerator q 0 = 1 := by
  simp only [simplexExpGenerator, zero_mul, Complex.exp_zero]
  exact complexSimplexExpectation_one

theorem simplexExpGenerator_continuous (q : Fin 4 → ℂ) :
    Continuous (simplexExpGenerator q) := by
  unfold simplexExpGenerator complexSimplexExpectation complexSimplexDot
  fun_prop

theorem simplexExpGenerator_continuous_joint :
    Continuous (fun p : (Fin 4 → ℂ) × ℂ => simplexExpGenerator p.1 p.2) := by
  unfold simplexExpGenerator complexSimplexExpectation complexSimplexDot
  fun_prop

theorem simplexExpGenerator_continuous_comp {α : Type*} [TopologicalSpace α]
    {q : α → (Fin 4 → ℂ)} {z : α → ℂ} (hq : Continuous q) (hz : Continuous z) :
    Continuous (fun p => simplexExpGenerator (q p) (z p)) :=
  simplexExpGenerator_continuous_joint.comp (hq.prodMk hz)

theorem simplexExpGenerator_shift (q : Fin 4 → ℂ) (c z : ℂ) :
    simplexExpGenerator (fun j => q j+c) z =
      Complex.exp (z*c) * simplexExpGenerator q z := by
  have he (x y w : ℝ) :
      z*complexSimplexDot (fun j => q j+c) x y w =
        z*c+z*complexSimplexDot q x y w := by
    unfold complexSimplexDot
    push_cast
    ring
  unfold simplexExpGenerator complexSimplexExpectation
  simp_rw [he, Complex.exp_add, intervalIntegral.integral_const_mul]
  ring

theorem simplexExpGenerator_neg (q : Fin 4 → ℂ) (z : ℂ) :
    simplexExpGenerator (fun j => -q j) z = simplexExpGenerator q (-z) := by
  have he (x y w : ℝ) : z*complexSimplexDot (fun j => -q j) x y w =
      (-z)*complexSimplexDot q x y w := by unfold complexSimplexDot; ring
  unfold simplexExpGenerator complexSimplexExpectation
  simp_rw [he]

theorem simplexExpGenerator_differentiableAt_distinct (q : Fin 4 → ℂ)
    (hq : Function.Injective q) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (simplexExpGenerator q) z := by
  have hfd : DifferentiableAt ℂ (fun w : ℂ => (6/w^3) *
      ∑ j : Fin 4, Complex.exp (w*q j) /
        (∏ k ∈ (Finset.univ : Finset (Fin 4)).erase j, (q j-q k))) z := by
    apply DifferentiableAt.mul
    · exact (differentiableAt_const (6 : ℂ)).div
        (differentiableAt_id.pow 3) (pow_ne_zero 3 hz)
    · apply DifferentiableAt.fun_sum
      intro j _
      exact ((Complex.differentiableAt_exp).comp z
        (differentiableAt_id.mul_const (q j))).div_const _
  apply hfd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact simplexExpGenerator_distinct q w hq hw

theorem simplexExpGenerator_analyticAt_zero (q : Fin 4 → ℂ)
    (hq : Function.Injective q) : AnalyticAt ℂ (simplexExpGenerator q) 0 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact simplexExpGenerator_differentiableAt_distinct q hq (by simpa using hz)
  · exact (simplexExpGenerator_continuous q).continuousAt

theorem simplexExpGenerator_tendsto_zero (q : Fin 4 → ℂ) :
    Filter.Tendsto (simplexExpGenerator q) (nhds 0) (nhds 1) := by
  simpa only [simplexExpGenerator_zero] using
    (simplexExpGenerator_continuous q).continuousAt.tendsto (x := (0 : ℂ))

end Sechstmoment
