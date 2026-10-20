import Mathlib.Analysis.Polynomial.Basic
import Sechstmoment.Numerator.Polar.General.Residues

namespace Sechstmoment
open Complex Metric MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1000000

noncomputable def polarGeneralExponentialMoment (η : ℝ) (P : Polynomial ℝ) (r : ℂ) : ℂ :=
  ∫ a in (0:ℝ)..η, ((Polynomial.eval (1-a/η : ℝ) P:ℝ):ℂ)*Complex.exp ((a:ℂ)*r)

theorem polarGeneralProfile_sum (η : ℝ) (P : Polynomial ℝ) (q : Fin 4 → ℂ) (R : ℝ) (ω : ℂ)
    (hq : Function.Injective q) (hR : ∀ j, ‖q j‖ < R) :
    polarGeneralProfile η P q R ω = ∑ j : Fin 4,
      ((q j-ω)/polarPoleDenominator q j)*polarGeneralExponentialMoment η P (q j) := by
  unfold polarGeneralProfile
  simp_rw [polarGeneralInverseContour_sum _ _ q R hq hR,Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    unfold polarGeneralExponentialMoment
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro a _
    ring
  · intro j _
    apply Continuous.intervalIntegrable
    fun_prop

theorem polarGeneralProfile_differentiable (η : ℝ) (P : Polynomial ℝ) (q : Fin 4 → ℂ) (R : ℝ)
    (hq : Function.Injective q) (hR : ∀ j, ‖q j‖ < R) :
    Differentiable ℂ (polarGeneralProfile η P q R) := by
  have hf : polarGeneralProfile η P q R = fun ω => ∑ j : Fin 4,
      ((q j-ω)/polarPoleDenominator q j)*polarGeneralExponentialMoment η P (q j) :=
    funext (fun ω => polarGeneralProfile_sum η P q R ω hq hR)
  rw [hf]
  fun_prop

theorem polarGeneralProfile_atPole (η : ℝ) (P : Polynomial ℝ) (q : Fin 4 → ℂ) (R : ℝ) (j : Fin 4)
    (hR : ∀ k, ‖q k‖ < R) :
    polarGeneralProfile η P q R (q j) =
      polarGeneralTripleProfile η P (fun k => q (j.succAbove k)) R := by
  unfold polarGeneralProfile polarGeneralTripleProfile
  simp_rw [polarGeneralInverseContour_atPole _ q j R hR]

private theorem general_boundary_ne (q : Fin 4 → ℂ) (R : ℝ) (hR : ∀ j, ‖q j‖ < R)
    (u : ℂ) (hu : u ∈ sphere (0:ℂ) R) (j : Fin 4) : u ≠ q j := by
  have hnorm : ‖u‖ = R := by simpa [mem_sphere,dist_eq_norm] using hu
  intro heq
  rw [heq] at hnorm
  exact (ne_of_lt (hR j)) hnorm

theorem polarFourPole_contour (q : Fin 4 → ℂ) (F : ℂ → ℂ) (R : ℝ)
    (hq : Function.Injective q) (hR : ∀ j, ‖q j‖ < R) (hF : Differentiable ℂ F) :
    (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
      (∮ u in C(0,R), F u/(∏ j : Fin 4, (u-q j))) =
      ∑ j : Fin 4, F (q j)/polarPoleDenominator q j := by
  have hpos : 0 < R := lt_of_le_of_lt (norm_nonneg (q 0)) (hR 0)
  have heq : (∮ u in C(0,R), F u/(∏ j : Fin 4, (u-q j))) =
      ∮ u in C(0,R), ∑ j : Fin 4, (1/polarPoleDenominator q j)*(F u/(u-q j)) := by
    apply circleIntegral.integral_congr hpos.le
    intro u hu
    have h := polar4_constant_partial_fraction q u hq (general_boundary_ne q R hR u hu)
    calc
      _ = F u*(1/(∏ j : Fin 4, (u-q j))) := by ring
      _ = _ := by rw [h,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hint (j : Fin 4) : CircleIntegrable (fun u : ℂ =>
      (1/polarPoleDenominator q j)*(F u/(u-q j))) 0 R := by
    apply ContinuousOn.circleIntegrable hpos.le
    exact continuousOn_const.mul (hF.continuous.continuousOn.div
      (continuous_id.sub continuous_const).continuousOn
      (fun u hu => sub_ne_zero.mpr (general_boundary_ne q R hR u hu j)))
  rw [heq,circleIntegral.integral_fun_sum (fun j _ => hint j)]
  simp only [circleIntegral.integral_const_mul]
  have hC (j : Fin 4) : (∮ u in C(0,R), F u/(u-q j)) = (2*(Real.pi:ℂ)*Complex.I)*F (q j) := by
    have hw : q j ∈ ball (0:ℂ) R := by simpa [mem_ball,dist_eq_norm] using hR j
    have h := hF.differentiableOn.circleIntegral_sub_inv_smul (c := 0) (R := R) hw
    simpa [div_eq_mul_inv,smul_eq_mul,mul_comm] using h
  simp_rw [hC]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hpi : (2*(Real.pi:ℂ)*Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  calc
    _ = ((2*(Real.pi:ℂ)*Complex.I)⁻¹*(2*(Real.pi:ℂ)*Complex.I))*
        (F (q j)/polarPoleDenominator q j) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hpi,one_mul]

theorem polarGeneralGeneratorContour_residues (η : ℝ) (P : Polynomial ℝ) (q : Fin 4 → ℂ)
    (innerR outerR : ℝ) (hq : Function.Injective q)
    (hinner : ∀ j, ‖q j‖ < innerR) (houter : ∀ j, ‖q j‖ < outerR) :
    polarGeneralGeneratorContour η P q innerR outerR =
      ∑ j : Fin 4, Complex.exp (q j-q 2-q 3)*
        (polarGeneralProfile η P q innerR (q j))^2/polarPoleDenominator q j := by
  let F : ℂ → ℂ := fun ω => Complex.exp (ω-q 2-q 3)*(polarGeneralProfile η P q innerR ω)^2
  have hF : Differentiable ℂ F :=
    (by fun_prop : Differentiable ℂ (fun ω : ℂ => Complex.exp (ω-q 2-q 3))).mul
      ((polarGeneralProfile_differentiable η P q innerR hq hinner).pow 2)
  unfold polarGeneralGeneratorContour
  have heq : (fun ω : ℂ => Complex.exp (ω-q 2-q 3)/(∏ j : Fin 4, (ω-q j))*
      (polarGeneralProfile η P q innerR ω)^2) =
      (fun ω : ℂ => F ω/(∏ j : Fin 4, (ω-q j))) := by funext ω; dsimp [F]; ring
  rw [heq,polarFourPole_contour q F outerR hq houter hF]

theorem polarGeneralGeneratorContour_triple_residues (η : ℝ) (P : Polynomial ℝ) (q : Fin 4 → ℂ)
    (innerR outerR : ℝ) (hq : Function.Injective q)
    (hinner : ∀ j, ‖q j‖ < innerR) (houter : ∀ j, ‖q j‖ < outerR) :
    polarGeneralGeneratorContour η P q innerR outerR =
      ∑ j : Fin 4, Complex.exp (q j-q 2-q 3)*
        (polarGeneralTripleProfile η P (fun k => q (j.succAbove k)) innerR)^2/polarPoleDenominator q j := by
  rw [polarGeneralGeneratorContour_residues η P q innerR outerR hq hinner houter]
  simp_rw [polarGeneralProfile_atPole η P q innerR _ hinner]

end Sechstmoment
