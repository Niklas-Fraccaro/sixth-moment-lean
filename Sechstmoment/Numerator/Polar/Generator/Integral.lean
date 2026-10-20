import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import Sechstmoment.Analysis.Integration.PolynomialIntegral

namespace Sechstmoment
open MeasureTheory

noncomputable def polarB (x : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..x, ((x-t : ℝ) : ℂ) * Complex.exp (-z * t)

noncomputable def polarC (x : ℝ) (z : ℂ) : ℂ :=
  -(∫ t in (0 : ℝ)..x, ((x-t : ℝ) : ℂ)^2 / 2 * Complex.exp (-z * t))

noncomputable def polarInverseFactor (x : ℝ) (ω z : ℂ) : ℂ := polarB x z + ω * polarC x z

noncomputable def polarH (m : ℕ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (1-(t:ℂ))^m / (Nat.factorial m : ℂ) * Complex.exp (-z * t)

noncomputable def polarJ (a b : ℝ) (z : ℂ) : ℂ :=
  polarB a z * polarB b z * polarH 2 z +
  (polarB a z * polarC b z + polarC a z * polarB b z) * polarH 1 z +
  polarC a z * polarC b z * polarH 0 z

noncomputable def polarA (x : ℝ) (z : ℂ) : ℂ := Complex.exp (-(x:ℂ)*z) - 1 + (x:ℂ)*z

theorem integral_cexp_quadratic (l u : ℝ) (z A B C : ℂ) (hz : z ≠ 0) :
    (∫ t in l..u, Complex.exp (z*t) * (A*(t:ℂ)^2+B*t+C)) =
    Complex.exp (z*u) * ((A*(u:ℂ)^2+B*u+C)/z - (2*A*u+B)/z^2 + 2*A/z^3) -
    Complex.exp (z*l) * ((A*(l:ℂ)^2+B*l+C)/z - (2*A*l+B)/z^2 + 2*A/z^3) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    have ht := hasDerivAt_id (t : ℂ)
    have he := (Complex.hasDerivAt_exp (z*t)).comp (t : ℂ) (ht.const_mul z)
    have hpoly := (((ht.pow 2).const_mul A).add (ht.const_mul B)).add_const C
    have hlin := (ht.const_mul (2*A)).add_const B
    convert (he.mul ((hpoly.div_const z).sub (hlin.div_const (z^2)) |>.add_const (2*A/z^3))).comp_ofReal using 1
    all_goals (dsimp; try field_simp; try ring)
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp (z*t) * (A*(t:ℂ)^2+B*t+C))).intervalIntegrable _ _

theorem polarB_closed (x : ℝ) (z : ℂ) (hz : z ≠ 0) :
    polarB x z = polarA x z / z^2 := by
  have h := integral_cexp_quadratic 0 x (-z) 0 (-1) x (neg_ne_zero.mpr hz)
  have heq : (fun t : ℝ => ((x-t:ℝ):ℂ) * Complex.exp (-z*t)) =
      (fun t : ℝ => Complex.exp (-z*t) * (0*(t:ℂ)^2+(-1)*t+(x:ℂ))) := by
    funext t; push_cast; ring
  rw [polarB, heq, h]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_mul, zero_add]
  unfold polarA
  rw [show -z*(x:ℂ) = -(x:ℂ)*z by ring]
  field_simp
  ring

theorem polarC_closed (x : ℝ) (z : ℂ) (hz : z ≠ 0) :
    polarC x z = polarA x z / z^3 - (x:ℂ)^2 / (2*z) := by
  have h := integral_cexp_quadratic 0 x (-z) (1/2) (- (x:ℂ)) ((x:ℂ)^2/2)
      (neg_ne_zero.mpr hz)
  have heq : (fun t : ℝ => ((x-t:ℝ):ℂ)^2/2 * Complex.exp (-z*t)) =
      (fun t : ℝ => Complex.exp (-z*t) * ((1/2)*(t:ℂ)^2+(-(x:ℂ))*t+(x:ℂ)^2/2)) := by
    funext t; push_cast; ring
  rw [polarC, heq, h]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_add]
  unfold polarA
  rw [show -z*(x:ℂ) = -(x:ℂ)*z by ring]
  field_simp
  ring

theorem polarInverseFactor_closed (x : ℝ) (ω z : ℂ) (hz : z ≠ 0) :
    polarInverseFactor x ω z = polarA x z / z^2 -
      ω*((x:ℂ)^2/(2*z)-polarA x z/z^3) := by
  rw [polarInverseFactor, polarB_closed x z hz, polarC_closed x z hz]
  ring

theorem polarH_zero_closed (z : ℂ) (hz : z ≠ 0) :
    polarH 0 z = (1-Complex.exp (-z))/z := by
  rw [polarH]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
  rw [integral_exp_mul_complex (neg_ne_zero.mpr hz)]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero]
  field_simp
  ring

theorem polarH_one_closed (z : ℂ) (hz : z ≠ 0) :
    polarH 1 z = 1/z - (1-Complex.exp (-z))/z^2 := by
  have h := integral_cexp_quadratic 0 1 (-z) 0 (-1) 1 (neg_ne_zero.mpr hz)
  have heq : (fun t : ℝ => (1-(t:ℂ))^1/(Nat.factorial 1:ℂ)*Complex.exp (-z*t)) =
      (fun t : ℝ => Complex.exp (-z*t)*(0*(t:ℂ)^2+(-1)*t+1)) := by
    funext t; norm_num; ring
  rw [polarH, heq, h]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, mul_one, mul_zero, Complex.exp_zero]
  field_simp
  ring

theorem polarH_two_closed (z : ℂ) (hz : z ≠ 0) :
    polarH 2 z = 1/(2*z) - 1/z^2 + (1-Complex.exp (-z))/z^3 := by
  have h := integral_cexp_quadratic 0 1 (-z) (1/2) (-1) (1/2) (neg_ne_zero.mpr hz)
  have heq : (fun t : ℝ => (1-(t:ℂ))^2/(Nat.factorial 2:ℂ)*Complex.exp (-z*t)) =
      (fun t : ℝ => Complex.exp (-z*t)*((1/2)*(t:ℂ)^2+(-1)*t+1/2)) := by
    funext t; norm_num; ring
  rw [polarH, heq, h]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, mul_one, mul_zero, Complex.exp_zero]
  field_simp
  ring

theorem polarJ_residue_formula (a b : ℝ) (z : ℂ) (hz : z ≠ 0) :
    z^7 * polarJ a b z = z*(1+z/2)*polarA a z*polarA b z -
      z^3/2*((a:ℂ)^2*polarA b z+(b:ℂ)^2*polarA a z) +
      (a:ℂ)^2*(b:ℂ)^2*z^4/4*(1-Complex.exp (-z)) := by
  rw [polarJ, polarB_closed a z hz, polarB_closed b z hz,
    polarC_closed a z hz, polarC_closed b z hz,
    polarH_zero_closed z hz, polarH_one_closed z hz, polarH_two_closed z hz]
  field_simp
  ring


theorem polarB_zero (x : ℝ) : polarB x 0 = (x:ℂ)^2/2 := by
  unfold polarB
  simp only [neg_zero,zero_mul,Complex.exp_zero,mul_one]
  rw [intervalIntegral.integral_ofReal]
  have h : (∫ t in (0:ℝ)..x, x-t) = x^2/2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => x) (g := fun t : ℝ => t)
        intervalIntegrable_const (continuous_id.intervalIntegrable 0 x),
      intervalIntegral.integral_const,integral_id]
    simp
    ring
  exact_mod_cast h

theorem polarC_zero (x : ℝ) : polarC x 0 = -(x:ℂ)^3/6 := by
  unfold polarC
  simp only [neg_zero,zero_mul,Complex.exp_zero,mul_one]
  have hc : (fun t : ℝ => ((x-t:ℝ):ℂ)^2/2) =
      (fun t : ℝ => (((x-t)^2/2:ℝ):ℂ)) := by funext t; push_cast; rfl
  rw [hc,intervalIntegral.integral_ofReal]
  have hp := integral_finite_polynomial (![x^2/2,-x,1/2] : Fin 3 → ℝ) 0 x
  norm_num [Fin.sum_univ_succ] at hp
  have h : (∫ t in (0:ℝ)..x, (x-t)^2/2) = x^3/6 := by
    convert hp using 1
    · apply intervalIntegral.integral_congr
      intro t _
      ring
    · ring
  rw [h]
  push_cast
  ring

theorem polarH_zero (m : ℕ) : polarH m 0 = 1/(Nat.factorial (m+1):ℂ) := by
  unfold polarH
  simp only [neg_zero,zero_mul,Complex.exp_zero,mul_one]
  rw [intervalIntegral.integral_div]
  have hc : (fun t : ℝ => (1-(t:ℂ))^m) =
      (fun t : ℝ => (((1-t)^m:ℝ):ℂ)) := by funext t; push_cast; rfl
  rw [hc,intervalIntegral.integral_ofReal,
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^m) 1]
  norm_num [integral_pow,Nat.factorial_succ]
  field_simp


theorem polarB_continuous (x : ℝ) : Continuous (polarB x) := by
  unfold polarB
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

theorem polarC_continuous (x : ℝ) : Continuous (polarC x) := by
  unfold polarC
  apply Continuous.neg
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

theorem polarH_continuous (m : ℕ) : Continuous (polarH m) := by
  unfold polarH
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

theorem polarJ_continuous (a b : ℝ) : Continuous (polarJ a b) := by
  exact (((polarB_continuous a).mul (polarB_continuous b)).mul (polarH_continuous 2)).add
    ((((polarB_continuous a).mul (polarC_continuous b)).add
      ((polarC_continuous a).mul (polarB_continuous b))).mul (polarH_continuous 1)) |>.add
    (((polarC_continuous a).mul (polarC_continuous b)).mul (polarH_continuous 0))

theorem polarJ_differentiableAt_nonzero (a b : ℝ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (polarJ a b) z := by
  let F : ℂ → ℂ := fun w => (w*(1+w/2)*polarA a w*polarA b w -
    w^3/2*((a:ℂ)^2*polarA b w+(b:ℂ)^2*polarA a w) +
    (a:ℂ)^2*(b:ℂ)^2*w^4/4*(1-Complex.exp (-w))) / w^7
  have hn : DifferentiableAt ℂ (fun w : ℂ => w*(1+w/2)*polarA a w*polarA b w -
      w^3/2*((a:ℂ)^2*polarA b w+(b:ℂ)^2*polarA a w) +
      (a:ℂ)^2*(b:ℂ)^2*w^4/4*(1-Complex.exp (-w))) z := by
    unfold polarA
    fun_prop
  have hd : DifferentiableAt ℂ F z := hn.div (differentiableAt_id.pow 7) (pow_ne_zero _ hz)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz] with w hw
  dsimp [F]
  have h := polarJ_residue_formula a b w hw
  exact (eq_div_iff (pow_ne_zero _ hw)).mpr (by simpa only [mul_comm] using h)

theorem polarJ_analyticAt_zero (a b : ℝ) : AnalyticAt ℂ (polarJ a b) 0 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact polarJ_differentiableAt_nonzero a b (by simpa using hz)
  · exact (polarJ_continuous a b).continuousAt

theorem polarJ_differentiable (a b : ℝ) : Differentiable ℂ (polarJ a b) := by
  intro z
  by_cases hz : z = 0
  · subst z
    exact (polarJ_analyticAt_zero a b).differentiableAt
  · exact polarJ_differentiableAt_nonzero a b hz

theorem polarJ_analyticAt (a b : ℝ) (z : ℂ) : AnalyticAt ℂ (polarJ a b) z :=
  (polarJ_differentiable a b).analyticAt z

end Sechstmoment
