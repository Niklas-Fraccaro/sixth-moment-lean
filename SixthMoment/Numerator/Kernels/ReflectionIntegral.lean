import SixthMoment.Numerator.Polar.Generator.Integral

namespace SixthMoment
open MeasureTheory
open scoped BigOperators

noncomputable def reflectionE (x : ℝ) (z : ℂ) : ℂ := Complex.exp ((x:ℂ)*z)-1-(x:ℂ)*z

noncomputable def reflectionNumerator (a b : ℝ) (z : ℂ) : ℂ :=
  z*(1-z/2)*reflectionE a z*reflectionE b z -
  z^3/2*((a:ℂ)^2*reflectionE b z+(b:ℂ)^2*reflectionE a z) +
  (a:ℂ)^2*(b:ℂ)^2*z^4/4*(Complex.exp z-1)

noncomputable def reflectedPolarGenerator (a b : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-z/2) * polarJ a b (-z)

noncomputable def reflectionDividedIntegrand (a b t : ℝ) (z : ℂ) : ℂ :=
  -(((b-a+2*t)*(1-a+t)*(1-b-t):ℝ):ℂ) +
  Complex.exp (z*((a-t:ℝ):ℂ))*(((b+t)*(1-b-t):ℝ):ℂ) -
  Complex.exp (z*((b+t:ℝ):ℂ))*(((a-t)*(1-a+t):ℝ):ℂ) +
  Complex.exp z*(((a-t)*(b+t)*(b-a+2*t):ℝ):ℂ)

private theorem integral_cubic (a A B C D : ℝ) :
    (∫ t in (0:ℝ)..a, A+B*t+C*t^2+D*t^3) = A*a+B*a^2/2+C*a^3/3+D*a^4/4 := by
  have h := integral_finite_polynomial (![A,B,C,D] : Fin 4 → ℝ) 0 a
  norm_num [Fin.sum_univ_succ] at h
  convert h using 1
  · apply intervalIntegral.integral_congr
    intro t _
    ring
  · ring

theorem reflection_polynomial_integral_left (a b : ℝ) :
    (∫ t in (0:ℝ)..a, (b-a+2*t)*(1-a+t)*(1-b-t)) =
      a*b*(1-a-b)+a^2*b^2/2 := by
  have heq : (fun t : ℝ => (b-a+2*t)*(1-a+t)*(1-b-t)) =
      (fun t => (b-a)*(1-a)*(1-b)+(2*(1-a)*(1-b)-(b-a)^2)*t -
        3*(b-a)*t^2-2*t^3) := by funext t; ring
  rw [heq]
  have h := integral_cubic a ((b-a)*(1-a)*(1-b)) (2*(1-a)*(1-b)-(b-a)^2) (-3*(b-a)) (-2)
  convert h using 1
  · apply intervalIntegral.integral_congr
    intro t _
    ring
  · ring

theorem reflection_polynomial_integral_right (a b : ℝ) :
    (∫ t in (0:ℝ)..a, (a-t)*(b+t)*(b-a+2*t)) = a^2*b^2/2 := by
  have heq : (fun t : ℝ => (a-t)*(b+t)*(b-a+2*t)) =
      (fun t => (b-a)*a*b+(2*a*b-(b-a)^2)*t-3*(b-a)*t^2-2*t^3) := by funext t; ring
  rw [heq]
  have h := integral_cubic a ((b-a)*a*b) (2*a*b-(b-a)^2) (-3*(b-a)) (-2)
  convert h using 1
  · apply intervalIntegral.integral_congr
    intro t _
    ring
  · ring

theorem reflectionDividedIntegral_formula (a b : ℝ) (z : ℂ) (hz : z ≠ 0) :
    z^4 * (∫ t in (0:ℝ)..a, reflectionDividedIntegrand a b t z) =
      2 * reflectionNumerator a b z := by
  have i0 : IntervalIntegrable (fun t : ℝ => (((b-a+2*t)*(1-a+t)*(1-b-t):ℝ):ℂ)) volume 0 a :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun t : ℝ => Complex.exp (z*((a-t:ℝ):ℂ))*
      (((b+t)*(1-b-t):ℝ):ℂ)) volume 0 a :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t : ℝ => Complex.exp (z*((b+t:ℝ):ℂ))*
      (((a-t)*(1-a+t):ℝ):ℂ)) volume 0 a :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun t : ℝ => Complex.exp z*
      (((a-t)*(b+t)*(b-a+2*t):ℝ):ℂ)) volume 0 a :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have in0 : IntervalIntegrable (fun t : ℝ => -(((b-a+2*t)*(1-a+t)*(1-b-t):ℝ):ℂ)) volume 0 a := i0.neg
  have in01 : IntervalIntegrable (fun t : ℝ => -(((b-a+2*t)*(1-a+t)*(1-b-t):ℝ):ℂ) +
      Complex.exp (z*((a-t:ℝ):ℂ))*(((b+t)*(1-b-t):ℝ):ℂ)) volume 0 a := in0.add i1
  have in012 : IntervalIntegrable (fun t : ℝ => -(((b-a+2*t)*(1-a+t)*(1-b-t):ℝ):ℂ) +
      Complex.exp (z*((a-t:ℝ):ℂ))*(((b+t)*(1-b-t):ℝ):ℂ) -
      Complex.exp (z*((b+t:ℝ):ℂ))*(((a-t)*(1-a+t):ℝ):ℂ)) volume 0 a := in01.sub i2
  unfold reflectionDividedIntegrand
  rw [intervalIntegral.integral_add in012 i3,
    intervalIntegral.integral_sub in01 i2,
    intervalIntegral.integral_add in0 i1, intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_ofReal,reflection_polynomial_integral_left,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal,
    reflection_polynomial_integral_right]
  have heq1 : (fun t : ℝ => Complex.exp (z*((a-t:ℝ):ℂ))*(((b+t)*(1-b-t):ℝ):ℂ)) =
      (fun t : ℝ => Complex.exp (z*a) * (Complex.exp (-z*t)*
        (-(t:ℂ)^2+(1-2*(b:ℂ))*t+(b:ℂ)*(1-b)))) := by
    funext t
    push_cast
    rw [show z*((a:ℂ)-t) = z*a+(-z)*t by ring, Complex.exp_add]
    ring
  have heq2 : (fun t : ℝ => Complex.exp (z*((b+t:ℝ):ℂ))*(((a-t)*(1-a+t):ℝ):ℂ)) =
      (fun t : ℝ => Complex.exp (z*b) * (Complex.exp (z*t)*
        (-(t:ℂ)^2+(2*(a:ℂ)-1)*t+(a:ℂ)*(1-a)))) := by
    funext t
    push_cast
    rw [show z*((b:ℂ)+t) = z*b+z*t by ring, Complex.exp_add]
    ring
  rw [heq1,heq2,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have h1 := integral_cexp_quadratic 0 a (-z) (-1) (1-2*(b:ℂ)) ((b:ℂ)*(1-b)) (neg_ne_zero.mpr hz)
  have h2 := integral_cexp_quadratic 0 a z (-1) (2*(a:ℂ)-1) ((a:ℂ)*(1-a)) hz
  rw [show (fun t : ℝ => Complex.exp (-z*t)*(-(t:ℂ)^2+(1-2*(b:ℂ))*t+(b:ℂ)*(1-b))) =
      (fun t : ℝ => Complex.exp (-z*t)*((-1)*(t:ℂ)^2+(1-2*(b:ℂ))*t+(b:ℂ)*(1-b))) by funext t; ring,
    show (fun t : ℝ => Complex.exp (z*t)*(-(t:ℂ)^2+(2*(a:ℂ)-1)*t+(a:ℂ)*(1-a))) =
      (fun t : ℝ => Complex.exp (z*t)*((-1)*(t:ℂ)^2+(2*(a:ℂ)-1)*t+(a:ℂ)*(1-a))) by funext t; ring,
    h1,h2]
  unfold reflectionNumerator reflectionE
  push_cast
  simp only [mul_zero,Complex.exp_zero]
  rw [show (a:ℂ)*z = z*a by ring, show (b:ℂ)*z = z*b by ring,
    show -z*(a:ℂ) = -(z*(a:ℂ)) by ring, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero]
  ring

theorem reflectedPolarGenerator_formula (a b : ℝ) (z : ℂ) (hz : z ≠ 0) :
    z^7 * Complex.exp (z/2) * reflectedPolarGenerator a b z = reflectionNumerator a b z := by
  have h := polarJ_residue_formula a b (-z) (neg_ne_zero.mpr hz)
  have ha : polarA a (-z) = reflectionE a z := by
    unfold polarA reflectionE
    rw [show -(a:ℂ)*(-z) = (a:ℂ)*z by ring]
    ring
  have hb : polarA b (-z) = reflectionE b z := by
    unfold polarA reflectionE
    rw [show -(b:ℂ)*(-z) = (b:ℂ)*z by ring]
    ring
  rw [ha,hb] at h
  have hexp : Complex.exp (z/2)*Complex.exp (-z/2) = 1 := by
    rw [←Complex.exp_add,show z/2+(-z)/2 = 0 by ring,Complex.exp_zero]
  unfold reflectedPolarGenerator reflectionNumerator
  rw [show z^7*Complex.exp (z/2)*(Complex.exp (-z/2)*polarJ a b (-z)) =
      z^7*(Complex.exp (z/2)*Complex.exp (-z/2))*polarJ a b (-z) by ring,hexp]
  norm_num at h ⊢
  linear_combination -h

theorem reflectedPolarGenerator_continuous (a b : ℝ) : Continuous (reflectedPolarGenerator a b) := by
  unfold reflectedPolarGenerator
  exact (by fun_prop : Continuous (fun z : ℂ => Complex.exp (-z/2))).mul
    ((polarJ_continuous a b).comp continuous_neg)

theorem reflectedPolarGenerator_differentiable (a b : ℝ) :
    Differentiable ℂ (reflectedPolarGenerator a b) := by
  unfold reflectedPolarGenerator
  exact (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (-z/2))).mul
    ((polarJ_differentiable a b).comp differentiable_neg)

theorem reflectedPolarGenerator_analyticAt (a b : ℝ) (z : ℂ) :
    AnalyticAt ℂ (reflectedPolarGenerator a b) z :=
  (reflectedPolarGenerator_differentiable a b).analyticAt z

end SixthMoment
