import SixthMoment.Analysis.Simplex.Exponential
import SixthMoment.Numerator.Kernels.Polynomial
import SixthMoment.Numerator.Kernels.ReflectionIntegral
import SixthMoment.Numerator.Polar.Generator.Contour

namespace SixthMoment
open MeasureTheory
open scoped BigOperators

noncomputable def numeratorExpNodes (a b t : ℝ) : Fin 4 → ℂ :=
  ![-1/2, ((a-t:ℝ):ℂ)-1/2, 1/2-((b-t:ℝ):ℂ), 1/2]

noncomputable def numeratorExpGenerator (a b : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..min a b,
    (numeratorP (b-t) (a-t):ℂ) * simplexExpGenerator (numeratorExpNodes a b t) z

noncomputable def reflectionRawNodes (A B : ℂ) : Fin 4 → ℂ := ![0,A,B,1]

theorem simplexExpGenerator_translate (q : Fin 4 → ℂ) (z c : ℂ) :
    simplexExpGenerator (fun j => q j+c) z = Complex.exp (z*c) * simplexExpGenerator q z := by
  have he (x y w : ℝ) : complexSimplexDot (fun j => q j+c) x y w =
      complexSimplexDot q x y w+c := by
    unfold complexSimplexDot
    push_cast
    ring
  unfold simplexExpGenerator complexSimplexExpectation
  simp_rw [he, mul_add, Complex.exp_add]
  simp_rw [intervalIntegral.integral_mul_const]
  ring

theorem reflection_simplex_algebra (A B z : ℂ)
    (hq : Function.Injective (reflectionRawNodes A B)) (hz : z ≠ 0) :
    2*z^3 * (A*B*(B-A)*(1-A)*(1-B)/12) *
      simplexExpGenerator (reflectionRawNodes A B) z =
    -(B-A)*(1-A)*(1-B) + Complex.exp (z*A)*B*(1-B) -
      Complex.exp (z*B)*A*(1-A) + Complex.exp z*A*B*(B-A) := by
  have h01 := hq.ne (show (0:Fin 4) ≠ 1 by decide)
  have h02 := hq.ne (show (0:Fin 4) ≠ 2 by decide)
  have h12 := hq.ne (show (1:Fin 4) ≠ 2 by decide)
  have h13 := hq.ne (show (1:Fin 4) ≠ 3 by decide)
  have h23 := hq.ne (show (2:Fin 4) ≠ 3 by decide)
  norm_num [reflectionRawNodes] at h01 h02 h12 h13 h23
  rw [simplexExpGenerator_distinct _ _ hq hz]
  have hu0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have hu1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have hu2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have hu3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  norm_num [Fin.sum_univ_succ,hu0,hu1,hu2,hu3,Finset.prod_insert,reflectionRawNodes]
  field_simp [hz, (Ne.symm h01),(Ne.symm h02), sub_ne_zero.mpr h12,sub_ne_zero.mpr (Ne.symm h12),
    sub_ne_zero.mpr h13,sub_ne_zero.mpr h23,sub_ne_zero.mpr (Ne.symm h13),sub_ne_zero.mpr (Ne.symm h23)]
  ring

private theorem reflection_nodes_injective (a b t : ℝ) (_ha : 0 < a) (hb : 0 < b)
    (hab : a+b < 1) (ht : t ∈ Set.Icc 0 a) (hta : t ≠ a) (htab : t ≠ (a-b)/2) :
    Function.Injective (reflectionRawNodes ((a-t:ℝ):ℂ) ((b+t:ℝ):ℂ)) := by
  have hA : a-t ≠ 0 := by intro h; apply hta; linarith
  have hB : b+t ≠ 0 := ne_of_gt (by linarith [ht.1] : 0 < b+t)
  have hAB : a-t ≠ b+t := by intro h; apply htab; linarith
  have hA1 : a-t ≠ 1 := ne_of_lt (by linarith [ht.1] : a-t < 1)
  have hB1 : b+t ≠ 1 := ne_of_lt (by linarith [ht.2] : b+t < 1)
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals (first | rfl | norm_num [reflectionRawNodes] at hij)
  all_goals
    have hr := congrArg Complex.re hij
    simp only [Complex.ofReal_re,Complex.sub_re,Complex.add_re,Complex.zero_re,Complex.one_re] at hr
    exfalso
    first
    | exact hA (by linarith)
    | exact hB (by linarith)
    | exact hAB (by linarith)
    | exact hA1 (by linarith)
    | exact hB1 (by linarith)

theorem numeratorExpGenerator_continuous (a b : ℝ) : Continuous (numeratorExpGenerator a b) := by
  unfold numeratorExpGenerator numeratorExpNodes numeratorP simplexExpGenerator
    complexSimplexExpectation complexSimplexDot
  fun_prop

theorem numeratorExpGenerator_reflected_divided (a b : ℝ) (z : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b < 1) (hz : z ≠ 0) :
    2*z^3*Complex.exp (z/2)*numeratorExpGenerator a (1-b) z =
      ∫ t in (0:ℝ)..a, reflectionDividedIntegrand a b t z := by
  have hmin : min a (1-b) = a := min_eq_left (by linarith)
  unfold numeratorExpGenerator
  rw [hmin, ←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne a, volume.ae_ne ((a-b)/2)] with t hta htab
  intro ht
  have ht' : t ∈ Set.Icc 0 a := by
    rw [Set.uIoc_of_le ha.le] at ht
    exact ⟨ht.1.le,ht.2⟩
  have hq := reflection_nodes_injective a b t ha hb hab ht' hta htab
  have hraw := reflection_simplex_algebra ((a-t:ℝ):ℂ) ((b+t:ℝ):ℂ) z hq hz
  have hn : numeratorExpNodes a (1-b) t =
      (fun j => reflectionRawNodes ((a-t:ℝ):ℂ) ((b+t:ℝ):ℂ) j + (-1/2)) := by
    funext j
    fin_cases j <;> simp [numeratorExpNodes,reflectionRawNodes] <;> ring
  rw [hn, simplexExpGenerator_translate]
  have hexp : Complex.exp (z/2)*Complex.exp (z*(-1/2)) = 1 := by
    rw [←Complex.exp_add, show z/2+z*(-1/2) = 0 by ring,Complex.exp_zero]
  have hc : (numeratorP (1-b-t) (a-t):ℂ) =
      ((a-t:ℝ):ℂ)*((b+t:ℝ):ℂ)*(((b+t:ℝ):ℂ)-((a-t:ℝ):ℂ))*
        (1-((a-t:ℝ):ℂ))*(1-((b+t:ℝ):ℂ))/12 := by
    unfold numeratorP
    push_cast
    ring
  rw [hc]
  calc
    _ = 2*z^3 * (((a-t:ℝ):ℂ)*((b+t:ℝ):ℂ)*(((b+t:ℝ):ℂ)-((a-t:ℝ):ℂ))*
        (1-((a-t:ℝ):ℂ))*(1-((b+t:ℝ):ℂ))/12) *
        simplexExpGenerator (reflectionRawNodes ((a-t:ℝ):ℂ) ((b+t:ℝ):ℂ)) z := by
      calc
        _ = 2*z^3 * (((a-t:ℝ):ℂ)*((b+t:ℝ):ℂ)*(((b+t:ℝ):ℂ)-((a-t:ℝ):ℂ))*
          (1-((a-t:ℝ):ℂ))*(1-((b+t:ℝ):ℂ))/12) *
          (Complex.exp (z/2)*Complex.exp (z*(-1/2))) *
          simplexExpGenerator (reflectionRawNodes ((a-t:ℝ):ℂ) ((b+t:ℝ):ℂ)) z := by ring
        _ = _ := by rw [hexp]; ring
    _ = _ := by
      rw [hraw]
      unfold reflectionDividedIntegrand
      push_cast
      ring

theorem numeratorExpGenerator_reflection (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b < 1) :
    numeratorExpGenerator a (1-b) = reflectedPolarGenerator a b := by
  apply Continuous.ext_on (dense_compl_singleton (0:ℂ))
    (numeratorExpGenerator_continuous a (1-b)) (reflectedPolarGenerator_continuous a b)
  intro z hz
  have hz' : z ≠ 0 := hz
  have hdiv := numeratorExpGenerator_reflected_divided a b z ha hb hab hz'
  have hint := reflectionDividedIntegral_formula a b z hz'
  have hp := reflectedPolarGenerator_formula a b z hz'
  have hnonzero : z^7 * Complex.exp (z/2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hz') (Complex.exp_ne_zero _)
  apply mul_left_cancel₀ hnonzero
  linear_combination (z^4/2)*hdiv + hint/2 - hp

theorem numeratorExpGenerator_reflection_contour (a b : ℝ) (z : ℂ) (R : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b < 1) (hR : ‖z‖ < R) :
    numeratorExpGenerator a (1-b) z = Complex.exp (-z/2)*polarContourJ a b (-z) R := by
  rw [numeratorExpGenerator_reflection a b ha hb hab]
  unfold reflectedPolarGenerator
  rw [polarContourJ_eq_polarJ_all a b (-z) R (by simpa using hR)]

theorem numeratorExpGenerator_reflected_analyticAt (a b : ℝ) (z : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b < 1) :
    AnalyticAt ℂ (numeratorExpGenerator a (1-b)) z := by
  rw [numeratorExpGenerator_reflection a b ha hb hab]
  exact reflectedPolarGenerator_analyticAt a b z

theorem numeratorExpGenerator_reflection_iteratedDeriv (a b : ℝ) (n : ℕ) (z : ℂ)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b < 1) :
    iteratedDeriv n (numeratorExpGenerator a (1-b)) z =
      iteratedDeriv n (reflectedPolarGenerator a b) z := by
  rw [numeratorExpGenerator_reflection a b ha hb hab]

end SixthMoment
