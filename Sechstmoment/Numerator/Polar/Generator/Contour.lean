import Mathlib.Analysis.Complex.CauchyIntegral
import Sechstmoment.Numerator.Polar.Generator.Integral

namespace Sechstmoment
open Complex Metric
open scoped Real

noncomputable def polarContourJ (a b : ℝ) (z : ℂ) (R : ℝ) : ℂ :=
  (2 * (Real.pi:ℂ) * Complex.I)⁻¹ *
    ∮ ω in C(0, R), Complex.exp ω / ((ω+z)*ω^3) *
      polarInverseFactor a ω z * polarInverseFactor b ω z

theorem circle_exp_center_power (n : ℕ) (R : ℝ) (hR : 0 < R) :
    (∮ ω in C(0,R), Complex.exp ω / ω^(n+1)) =
      2*(Real.pi:ℂ)*Complex.I / (Nat.factorial n:ℂ) := by
  have h := (Complex.differentiable_exp.differentiableOn :
      DifferentiableOn ℂ Complex.exp (closedBall (0:ℂ) R)).circleIntegral_one_div_sub_center_pow_smul hR n
  have hd : iteratedDeriv n Complex.exp (0:ℂ) = 1 := by
    have hfun : (fun s : ℂ => Complex.exp (1*s)) = Complex.exp := by funext s; simp
    rw [← hfun, iteratedDeriv_cexp_const_mul]
    simp
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm, hd] using h

theorem circle_exp_shift (z : ℂ) (R : ℝ) (hR : ‖z‖ < R) :
    (∮ ω in C(0,R), Complex.exp ω / (ω+z)) =
      2*(Real.pi:ℂ)*Complex.I * Complex.exp (-z) := by
  have hw : -z ∈ ball (0:ℂ) R := by simpa [mem_ball, dist_eq_norm] using hR
  have h := (Complex.differentiable_exp.differentiableOn :
      DifferentiableOn ℂ Complex.exp (closedBall (0:ℂ) R)).circleIntegral_sub_inv_smul hw
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

private theorem exp_center_integrable (R : ℝ) (hR : 0 < R) (n : ℕ) :
    CircleIntegrable (fun ω : ℂ => Complex.exp ω / ω^n) 0 R := by
  apply ContinuousOn.circleIntegrable hR.le
  exact Complex.continuous_exp.continuousOn.div (continuous_id.pow n).continuousOn
    (fun ω hω => pow_ne_zero _ (circle_nonzero R hR ω hω))

private theorem exp_shift_integrable (R : ℝ) (z : ℂ) (hR : ‖z‖ < R) :
    CircleIntegrable (fun ω : ℂ => Complex.exp ω / (ω+z)) 0 R := by
  apply ContinuousOn.circleIntegrable (le_trans (norm_nonneg z) hR.le)
  exact Complex.continuous_exp.continuousOn.div (continuous_id.add_const z).continuousOn
    (circle_shift_nonzero R z hR)

theorem polar_quadratic_partial_fractions (A B C z ω : ℂ)
    (hz : z ≠ 0) (hω : ω ≠ 0) (hplus : ω+z ≠ 0) :
    (A+B*ω+C*ω^2)/((ω+z)*ω^3) =
      (A/z)/ω^3 + (B/z-A/z^2)/ω^2 +
      (C/z-B/z^2+A/z^3)/ω + (-C/z+B/z^2-A/z^3)/(ω+z) := by
  field_simp
  ring

theorem polar_quadratic_contour (A B C z : ℂ) (R : ℝ)
    (hz : z ≠ 0) (hR : ‖z‖ < R) :
    (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
      (∮ ω in C(0,R), Complex.exp ω * (A+B*ω+C*ω^2)/((ω+z)*ω^3)) =
      A * polarH 2 z + B * polarH 1 z + C * polarH 0 z := by
  have hpos : 0 < R := lt_of_le_of_lt (norm_nonneg z) hR
  let c3 := A/z
  let c2 := B/z-A/z^2
  let c1 := C/z-B/z^2+A/z^3
  let cs := -C/z+B/z^2-A/z^3
  have heq : (∮ ω in C(0,R), Complex.exp ω * (A+B*ω+C*ω^2)/((ω+z)*ω^3)) =
      ∮ ω in C(0,R),
        c3*(Complex.exp ω/ω^3) + c2*(Complex.exp ω/ω^2) +
        c1*(Complex.exp ω/ω) + cs*(Complex.exp ω/(ω+z)) := by
    apply circleIntegral.integral_congr hpos.le
    intro ω hω
    have hp := polar_quadratic_partial_fractions A B C z ω hz
      (circle_nonzero R hpos ω hω) (circle_shift_nonzero R z hR ω hω)
    dsimp [c3,c2,c1,cs]
    calc
      _ = Complex.exp ω * ((A+B*ω+C*ω^2)/((ω+z)*ω^3)) := by ring
      _ = _ := by rw [hp]; ring
  have i3 : CircleIntegrable (fun ω : ℂ => c3*(Complex.exp ω/ω^3)) 0 R := by
    unfold CircleIntegrable
    exact IntervalIntegrable.const_mul (exp_center_integrable R hpos 3) c3
  have i2 : CircleIntegrable (fun ω : ℂ => c2*(Complex.exp ω/ω^2)) 0 R := by
    unfold CircleIntegrable
    exact IntervalIntegrable.const_mul (exp_center_integrable R hpos 2) c2
  have i1 : CircleIntegrable (fun ω : ℂ => c1*(Complex.exp ω/ω)) 0 R := by
    unfold CircleIntegrable
    simpa only [pow_one] using IntervalIntegrable.const_mul (exp_center_integrable R hpos 1) c1
  have is : CircleIntegrable (fun ω : ℂ => cs*(Complex.exp ω/(ω+z))) 0 R := by
    unfold CircleIntegrable
    exact IntervalIntegrable.const_mul (exp_shift_integrable R z hR) cs
  rw [heq, circleIntegral.integral_add (i3.fun_add i2 |>.fun_add i1) is,
    circleIntegral.integral_add (i3.fun_add i2) i1, circleIntegral.integral_add i3 i2]
  simp only [circleIntegral.integral_const_mul]
  have h3 := circle_exp_center_power 2 R hpos
  have h2 := circle_exp_center_power 1 R hpos
  have h1 := circle_exp_center_power 0 R hpos
  norm_num at h3 h2 h1
  rw [h3,h2,h1,circle_exp_shift z R hR,
    polarH_two_closed z hz,polarH_one_closed z hz,polarH_zero_closed z hz]
  dsimp [c3,c2,c1,cs]
  have hpi : (2*(Real.pi:ℂ)*Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  field_simp
  ring

theorem polar_quadratic_contour_zero (A B C : ℂ) (R : ℝ) (hR : 0 < R) :
    (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
      (∮ ω in C(0,R), Complex.exp ω*(A+B*ω+C*ω^2)/(ω^4)) =
      A*polarH 2 0+B*polarH 1 0+C*polarH 0 0 := by
  have heq : (∮ ω in C(0,R), Complex.exp ω*(A+B*ω+C*ω^2)/ω^4) =
      ∮ ω in C(0,R), A*(Complex.exp ω/ω^4)+B*(Complex.exp ω/ω^3)+C*(Complex.exp ω/ω^2) := by
    apply circleIntegral.integral_congr hR.le
    intro ω hω
    field_simp [circle_nonzero R hR ω hω]
  have i4 : CircleIntegrable (fun ω : ℂ => A*(Complex.exp ω/ω^4)) 0 R := by
    unfold CircleIntegrable
    exact IntervalIntegrable.const_mul (exp_center_integrable R hR 4) A
  have i3 : CircleIntegrable (fun ω : ℂ => B*(Complex.exp ω/ω^3)) 0 R := by
    unfold CircleIntegrable
    exact IntervalIntegrable.const_mul (exp_center_integrable R hR 3) B
  have i2 : CircleIntegrable (fun ω : ℂ => C*(Complex.exp ω/ω^2)) 0 R := by
    unfold CircleIntegrable
    exact IntervalIntegrable.const_mul (exp_center_integrable R hR 2) C
  rw [heq,circleIntegral.integral_add (i4.fun_add i3) i2,circleIntegral.integral_add i4 i3]
  simp only [circleIntegral.integral_const_mul]
  have h4 := circle_exp_center_power 3 R hR
  have h3 := circle_exp_center_power 2 R hR
  have h2 := circle_exp_center_power 1 R hR
  norm_num at h4 h3 h2
  rw [h4,h3,h2,polarH_zero,polarH_zero,polarH_zero]
  norm_num
  have hpi : (2*(Real.pi:ℂ)*Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  field_simp
  norm_num [Complex.I_sq]
  try ring

theorem polarContourJ_eq_polarJ (a b : ℝ) (z : ℂ) (R : ℝ)
    (hz : z ≠ 0) (hR : ‖z‖ < R) : polarContourJ a b z R = polarJ a b z := by
  unfold polarContourJ
  have heq : (fun ω : ℂ => Complex.exp ω/((ω+z)*ω^3)*
      polarInverseFactor a ω z*polarInverseFactor b ω z) =
      (fun ω : ℂ => Complex.exp ω *
        (polarB a z*polarB b z + (polarB a z*polarC b z+polarC a z*polarB b z)*ω +
          polarC a z*polarC b z*ω^2)/((ω+z)*ω^3)) := by
    funext ω; unfold polarInverseFactor; ring
  rw [heq, polar_quadratic_contour _ _ _ z R hz hR]
  rfl

theorem polarContourJ_eq_polarJ_all (a b : ℝ) (z : ℂ) (R : ℝ) (hR : ‖z‖ < R) :
    polarContourJ a b z R = polarJ a b z := by
  by_cases hz : z = 0
  · subst z
    have hpos : 0 < R := by simpa using hR
    unfold polarContourJ
    have heq : (fun ω : ℂ => Complex.exp ω/((ω+0)*ω^3)*
        polarInverseFactor a ω 0*polarInverseFactor b ω 0) =
        (fun ω : ℂ => Complex.exp ω *
          (polarB a 0*polarB b 0+(polarB a 0*polarC b 0+polarC a 0*polarB b 0)*ω+
            polarC a 0*polarC b 0*ω^2)/ω^4) := by
      funext ω
      unfold polarInverseFactor
      ring
    rw [heq,polar_quadratic_contour_zero _ _ _ R hpos]
    rfl
  · exact polarContourJ_eq_polarJ a b z R hz hR

theorem polarContourJ_residue_formula (a b : ℝ) (z : ℂ) (R : ℝ)
    (hz : z ≠ 0) (hR : ‖z‖ < R) :
    z^7 * polarContourJ a b z R = z*(1+z/2)*polarA a z*polarA b z -
      z^3/2*((a:ℂ)^2*polarA b z+(b:ℂ)^2*polarA a z) +
      (a:ℂ)^2*(b:ℂ)^2*z^4/4*(1-Complex.exp (-z)) := by
  rw [polarContourJ_eq_polarJ a b z R hz hR, polarJ_residue_formula a b z hz]

end Sechstmoment
