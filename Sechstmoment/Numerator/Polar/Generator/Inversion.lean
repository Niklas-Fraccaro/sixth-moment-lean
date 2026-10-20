import Sechstmoment.Numerator.Polar.Generator.Contour

namespace Sechstmoment
open Complex Metric

noncomputable def polarInverseLaplaceContour (x : ℝ) (ω z : ℂ) (R : ℝ) : ℂ :=
  (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
    ∮ u in C(0,R), Complex.exp ((x:ℂ)*u)*(u-ω)/(u^3*(u+z))

theorem circle_exp_center_power_atTime (x : ℝ) (n : ℕ) (R : ℝ) (hR : 0 < R) :
    (∮ ω in C(0,R), Complex.exp ((x:ℂ)*ω) / ω^(n+1)) =
      2*(Real.pi:ℂ)*Complex.I / (Nat.factorial n:ℂ) * (x:ℂ)^n := by
  have hd : DifferentiableOn ℂ (fun u : ℂ => Complex.exp ((x:ℂ)*u)) (closedBall (0:ℂ) R) := by fun_prop
  have h := hd.circleIntegral_one_div_sub_center_pow_smul hR n
  have hder := congrFun (iteratedDeriv_cexp_const_mul n (x:ℂ)) 0
  simp only [mul_zero, Complex.exp_zero, mul_one] at hder
  rw [hder] at h
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem circle_exp_shift_atTime (x : ℝ) (z : ℂ) (R : ℝ) (hR : ‖z‖ < R) :
    (∮ ω in C(0,R), Complex.exp ((x:ℂ)*ω) / (ω+z)) =
      2*(Real.pi:ℂ)*Complex.I * Complex.exp (-(x:ℂ)*z) := by
  have hw : -z ∈ ball (0:ℂ) R := by simpa [mem_ball, dist_eq_norm] using hR
  have hd : DifferentiableOn ℂ (fun u : ℂ => Complex.exp ((x:ℂ)*u)) (closedBall (0:ℂ) R) := by fun_prop
  have h := hd.circleIntegral_sub_inv_smul hw
  simpa [smul_eq_mul, div_eq_mul_inv, sub_neg_eq_add, mul_comm] using h

private theorem circle_nonzero (R : ℝ) (hR : 0 < R) (ω : ℂ) (hω : ω ∈ sphere (0:ℂ) R) :
    ω ≠ 0 := by
  have hnorm : ‖ω‖ = R := by simpa [mem_sphere, dist_eq_norm] using hω
  intro hw
  simp [hw] at hnorm
  linarith

private theorem circle_shift_nonzero (R : ℝ) (z : ℂ) (hR : ‖z‖ < R)
    (ω : ℂ) (hω : ω ∈ sphere (0:ℂ) R) : ω+z ≠ 0 := by
  have hnorm : ‖ω‖ = R := by simpa [mem_sphere, dist_eq_norm] using hω
  intro hw
  have heq : ω = -z := eq_neg_of_add_eq_zero_left hw
  rw [heq, norm_neg] at hnorm
  linarith

private theorem exp_center_integrable_atTime (x : ℝ) (R : ℝ) (hR : 0 < R) (n : ℕ) :
    CircleIntegrable (fun ω : ℂ => Complex.exp ((x:ℂ)*ω) / ω^n) 0 R := by
  apply ContinuousOn.circleIntegrable hR.le
  exact (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.div (continuous_id.pow n).continuousOn
    (fun ω hω => pow_ne_zero _ (circle_nonzero R hR ω hω))

private theorem exp_shift_integrable_atTime (x : ℝ) (R : ℝ) (z : ℂ) (hR : ‖z‖ < R) :
    CircleIntegrable (fun ω : ℂ => Complex.exp ((x:ℂ)*ω) / (ω+z)) 0 R := by
  apply ContinuousOn.circleIntegrable (le_trans (norm_nonneg z) hR.le)
  exact (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.div (continuous_id.add_const z).continuousOn
    (circle_shift_nonzero R z hR)

theorem polar_quadratic_contour_atTime (x : ℝ) (A B C z : ℂ) (R : ℝ)
    (hz : z ≠ 0) (hR : ‖z‖ < R) :
    (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
      (∮ ω in C(0,R), Complex.exp ((x:ℂ)*ω) * (A+B*ω+C*ω^2)/((ω+z)*ω^3)) =
      (A/z)*(x:ℂ)^2/2 + (B/z-A/z^2)*(x:ℂ) +
      (C/z-B/z^2+A/z^3) + (-C/z+B/z^2-A/z^3)*Complex.exp (-(x:ℂ)*z) := by
  have hpos : 0 < R := lt_of_le_of_lt (norm_nonneg z) hR
  let c3 := A/z
  let c2 := B/z-A/z^2
  let c1 := C/z-B/z^2+A/z^3
  let cs := -C/z+B/z^2-A/z^3
  have heq : (∮ ω in C(0,R), Complex.exp ((x:ℂ)*ω) * (A+B*ω+C*ω^2)/((ω+z)*ω^3)) =
      ∮ ω in C(0,R),
        c3*(Complex.exp ((x:ℂ)*ω)/ω^3) + c2*(Complex.exp ((x:ℂ)*ω)/ω^2) +
        c1*(Complex.exp ((x:ℂ)*ω)/ω) + cs*(Complex.exp ((x:ℂ)*ω)/(ω+z)) := by
    apply circleIntegral.integral_congr hpos.le
    intro ω hω
    have hp := polar_quadratic_partial_fractions A B C z ω hz
      (circle_nonzero R hpos ω hω) (circle_shift_nonzero R z hR ω hω)
    dsimp [c3,c2,c1,cs]
    calc
      _ = Complex.exp ((x:ℂ)*ω) * ((A+B*ω+C*ω^2)/((ω+z)*ω^3)) := by ring
      _ = _ := by rw [hp]; ring
  have i3 : CircleIntegrable (fun ω : ℂ => c3*(Complex.exp ((x:ℂ)*ω)/ω^3)) 0 R := by
    unfold CircleIntegrable
    exact IntervalIntegrable.const_mul (exp_center_integrable_atTime x R hpos 3) c3
  have i2 : CircleIntegrable (fun ω : ℂ => c2*(Complex.exp ((x:ℂ)*ω)/ω^2)) 0 R := by
    unfold CircleIntegrable
    exact IntervalIntegrable.const_mul (exp_center_integrable_atTime x R hpos 2) c2
  have i1 : CircleIntegrable (fun ω : ℂ => c1*(Complex.exp ((x:ℂ)*ω)/ω)) 0 R := by
    unfold CircleIntegrable
    simpa only [pow_one] using IntervalIntegrable.const_mul (exp_center_integrable_atTime x R hpos 1) c1
  have is : CircleIntegrable (fun ω : ℂ => cs*(Complex.exp ((x:ℂ)*ω)/(ω+z))) 0 R := by
    unfold CircleIntegrable
    exact IntervalIntegrable.const_mul (exp_shift_integrable_atTime x R z hR) cs
  rw [heq, circleIntegral.integral_add (i3.fun_add i2 |>.fun_add i1) is,
    circleIntegral.integral_add (i3.fun_add i2) i1, circleIntegral.integral_add i3 i2]
  simp only [circleIntegral.integral_const_mul]
  have h3 := circle_exp_center_power_atTime x 2 R hpos
  have h2 := circle_exp_center_power_atTime x 1 R hpos
  have h1 := circle_exp_center_power_atTime x 0 R hpos
  norm_num at h3 h2 h1
  rw [h3,h2,h1,circle_exp_shift_atTime x z R hR]
  dsimp [c3,c2,c1,cs]
  have hpi : (2*(Real.pi:ℂ)*Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  field_simp


theorem polarInverseLaplaceContour_eq (x : ℝ) (ω z : ℂ) (R : ℝ)
    (hz : z ≠ 0) (hR : ‖z‖ < R) :
    polarInverseLaplaceContour x ω z R = polarInverseFactor x ω z := by
  unfold polarInverseLaplaceContour
  have heq : (fun u : ℂ => Complex.exp ((x:ℂ)*u)*(u-ω)/(u^3*(u+z))) =
      (fun u : ℂ => Complex.exp ((x:ℂ)*u)*(-ω+1*u+0*u^2)/((u+z)*u^3)) := by funext u; ring
  rw [heq,polar_quadratic_contour_atTime x (-ω) 1 0 z R hz hR,
    polarInverseFactor_closed x ω z hz]
  unfold polarA
  field_simp
  ring

theorem polarInverseLaplaceContour_zero (x : ℝ) (ω : ℂ) (R : ℝ) (hR : 0 < R) :
    polarInverseLaplaceContour x ω 0 R = polarInverseFactor x ω 0 := by
  unfold polarInverseLaplaceContour
  have heq : (fun u : ℂ => Complex.exp ((x:ℂ)*u)*(u-ω)/(u^3*(u+0))) =
      (fun u : ℂ => Complex.exp ((x:ℂ)*u)/u^3-ω*(Complex.exp ((x:ℂ)*u)/u^4)) := by
    funext u
    by_cases hu : u = 0
    · simp [hu]
    · field_simp [hu]
      ring
  rw [heq]
  have i3 := exp_center_integrable_atTime x R hR 3
  have i4 : CircleIntegrable (fun u : ℂ => ω*(Complex.exp ((x:ℂ)*u)/u^4)) 0 R := by
    unfold CircleIntegrable
    exact IntervalIntegrable.const_mul (exp_center_integrable_atTime x R hR 4) ω
  rw [circleIntegral.integral_sub i3 i4,circleIntegral.integral_const_mul]
  have h3 := circle_exp_center_power_atTime x 2 R hR
  have h4 := circle_exp_center_power_atTime x 3 R hR
  norm_num at h3 h4
  rw [h3,h4,polarInverseFactor,polarB_zero,polarC_zero]
  have hpi : (2*(Real.pi:ℂ)*Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  field_simp
  ring

theorem polarInverseLaplaceContour_eq_all (x : ℝ) (ω z : ℂ) (R : ℝ) (hR : ‖z‖ < R) :
    polarInverseLaplaceContour x ω z R = polarInverseFactor x ω z := by
  by_cases hz : z = 0
  · subst z
    exact polarInverseLaplaceContour_zero x ω R (by simpa using hR)
  · exact polarInverseLaplaceContour_eq x ω z R hz hR

end Sechstmoment
