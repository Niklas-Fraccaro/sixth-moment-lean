import Sechstmoment.Analysis.Simplex.Exponential
import Sechstmoment.Numerator.Polar.General.Residues

namespace Sechstmoment
open Complex Metric
open scoped BigOperators

private theorem triple_boundary_ne (q : Fin 3 → ℂ) (R : ℝ) (hR : ∀ j, ‖q j‖ < R)
    (u : ℂ) (hu : u ∈ sphere (0:ℂ) R) (j : Fin 3) : u ≠ q j := by
  have hnorm : ‖u‖ = R := by simpa [mem_sphere,dist_eq_norm] using hu
  intro heq
  rw [heq] at hnorm
  exact (ne_of_lt (hR j)) hnorm

theorem polarTripleInverseContour_sum (x : ℝ) (q : Fin 3 → ℂ) (R : ℝ)
    (hq : Function.Injective q) (hR : ∀ j, ‖q j‖ < R) :
    polarTripleInverseContour x q R =
      ∑ j : Fin 3, Complex.exp ((x:ℂ)*q j)/polarPoleDenominator q j := by
  have hpos : 0 < R := lt_of_le_of_lt (norm_nonneg (q 0)) (hR 0)
  unfold polarTripleInverseContour
  have heq : (∮ u in C(0,R), Complex.exp ((x:ℂ)*u)/(∏ j : Fin 3, (u-q j))) =
      ∮ u in C(0,R), ∑ j : Fin 3,
        (1/polarPoleDenominator q j)*(Complex.exp ((x:ℂ)*u)/(u-q j)) := by
    apply circleIntegral.integral_congr hpos.le
    intro u hu
    have h := polar3_constant_partial_fraction q u hq (triple_boundary_ne q R hR u hu)
    calc
      _ = Complex.exp ((x:ℂ)*u)*(1/(∏ j : Fin 3, (u-q j))) := by ring
      _ = _ := by rw [h,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hint (j : Fin 3) : CircleIntegrable (fun u : ℂ =>
      (1/polarPoleDenominator q j)*(Complex.exp ((x:ℂ)*u)/(u-q j))) 0 R := by
    apply ContinuousOn.circleIntegrable hpos.le
    exact continuousOn_const.mul
      ((by fun_prop : Continuous (fun u : ℂ => Complex.exp ((x:ℂ)*u))).continuousOn.div
        (continuous_id.sub continuous_const).continuousOn
        (fun u hu => sub_ne_zero.mpr (triple_boundary_ne q R hR u hu j)))
  rw [heq,circleIntegral.integral_fun_sum (fun j _ => hint j)]
  simp only [circleIntegral.integral_const_mul]
  simp_rw [polarCircle_exp_atPole x _ R (hR _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hpi : (2*(Real.pi:ℂ)*Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  calc
    _ = ((2*(Real.pi:ℂ)*Complex.I)⁻¹*(2*(Real.pi:ℂ)*Complex.I))*
        (Complex.exp ((x:ℂ)*q j)/polarPoleDenominator q j) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hpi,one_mul]

/-- The genuine triple inverse contour is the genuine triangular exponential convolution. -/
theorem polarTripleInverseContour_eq_triangle (x : ℝ) (q : Fin 3 → ℂ) (R : ℝ)
    (hq : Function.Injective q) (hR : ∀ j, ‖q j‖ < R) :
    polarTripleInverseContour x q R = simplexTriangleExpIntegral (q 0) (q 1) (q 2) 1 0 x := by
  have h01 := hq.ne (show (0:Fin 3) ≠ 1 by decide)
  have h02 := hq.ne (show (0:Fin 3) ≠ 2 by decide)
  have h12 := hq.ne (show (1:Fin 3) ≠ 2 by decide)
  rw [polarTripleInverseContour_sum x q R hq hR,
    simplexTriangleExpIntegral_closed _ _ _ _ _ _ (by norm_num) h01 h02 h12]
  have hu0 : (Finset.univ : Finset (Fin 3)).erase 0 = {1,2} := by decide
  have hu1 : (Finset.univ : Finset (Fin 3)).erase 1 = {0,2} := by decide
  have hu2 : (Finset.univ : Finset (Fin 3)).erase 2 = {0,1} := by decide
  norm_num [polarPoleDenominator,Fin.sum_univ_succ,hu0,hu1,hu2,Finset.prod_insert]
  rw [show (x:ℂ)*q 0 = q 0*x by ring,
    show (x:ℂ)*q 1 = q 1*x by ring,show (x:ℂ)*q 2 = q 2*x by ring]
  field_simp [sub_ne_zero.mpr h01,sub_ne_zero.mpr h02,sub_ne_zero.mpr h12,
    sub_ne_zero.mpr h01.symm,sub_ne_zero.mpr h02.symm,sub_ne_zero.mpr h12.symm]
  ring

end Sechstmoment
