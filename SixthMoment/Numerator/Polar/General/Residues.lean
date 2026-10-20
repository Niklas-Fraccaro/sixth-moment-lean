import SixthMoment.Numerator.Polar.General.Definitions

namespace SixthMoment
open scoped BigOperators
open Complex Metric

set_option maxHeartbeats 1000000

noncomputable def polarPoleDenominator {n : ℕ} (q : Fin n → ℂ) (j : Fin n) : ℂ :=
  ∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (q j-q k)

theorem polar3_constant_partial_fraction (q : Fin 3 → ℂ) (u : ℂ)
    (hq : Function.Injective q) (hu : ∀ j, u ≠ q j) :
    1/(∏ j : Fin 3, (u-q j)) =
      ∑ j : Fin 3, (1/polarPoleDenominator q j)/(u-q j) := by
  have hu0 : (Finset.univ : Finset (Fin 3)).erase 0 = {1,2} := by decide
  have hu1 : (Finset.univ : Finset (Fin 3)).erase 1 = {0,2} := by decide
  have hu2 : (Finset.univ : Finset (Fin 3)).erase 2 = {0,1} := by decide
  norm_num [polarPoleDenominator,Fin.sum_univ_succ,Fin.prod_univ_succ,hu0,hu1,hu2,Finset.prod_insert]
  field_simp [sub_ne_zero.mpr (hu 0),
    sub_ne_zero.mpr (hu 1),
    sub_ne_zero.mpr (hu 2),
    sub_ne_zero.mpr (hq.ne (show (0:Fin 3) ≠ 1 by decide)),
    sub_ne_zero.mpr (hq.ne (show (0:Fin 3) ≠ 2 by decide)),
    sub_ne_zero.mpr (hq.ne (show (1:Fin 3) ≠ 0 by decide)),
    sub_ne_zero.mpr (hq.ne (show (1:Fin 3) ≠ 2 by decide)),
    sub_ne_zero.mpr (hq.ne (show (2:Fin 3) ≠ 0 by decide)),
    sub_ne_zero.mpr (hq.ne (show (2:Fin 3) ≠ 1 by decide))]
  ring

theorem polar4_constant_partial_fraction (q : Fin 4 → ℂ) (u : ℂ)
    (hq : Function.Injective q) (hu : ∀ j, u ≠ q j) :
    1/(∏ j : Fin 4, (u-q j)) =
      ∑ j : Fin 4, (1/polarPoleDenominator q j)/(u-q j) := by
  have hu0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have hu1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have hu2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have hu3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  norm_num [polarPoleDenominator,Fin.sum_univ_succ,Fin.prod_univ_succ,hu0,hu1,hu2,hu3,Finset.prod_insert]
  field_simp [sub_ne_zero.mpr (hu 0),
    sub_ne_zero.mpr (hu 1),
    sub_ne_zero.mpr (hu 2),
    sub_ne_zero.mpr (hu 3),
    sub_ne_zero.mpr (hq.ne (show (0:Fin 4) ≠ 1 by decide)),
    sub_ne_zero.mpr (hq.ne (show (0:Fin 4) ≠ 2 by decide)),
    sub_ne_zero.mpr (hq.ne (show (0:Fin 4) ≠ 3 by decide)),
    sub_ne_zero.mpr (hq.ne (show (1:Fin 4) ≠ 0 by decide)),
    sub_ne_zero.mpr (hq.ne (show (1:Fin 4) ≠ 2 by decide)),
    sub_ne_zero.mpr (hq.ne (show (1:Fin 4) ≠ 3 by decide)),
    sub_ne_zero.mpr (hq.ne (show (2:Fin 4) ≠ 0 by decide)),
    sub_ne_zero.mpr (hq.ne (show (2:Fin 4) ≠ 1 by decide)),
    sub_ne_zero.mpr (hq.ne (show (2:Fin 4) ≠ 3 by decide)),
    sub_ne_zero.mpr (hq.ne (show (3:Fin 4) ≠ 0 by decide)),
    sub_ne_zero.mpr (hq.ne (show (3:Fin 4) ≠ 1 by decide)),
    sub_ne_zero.mpr (hq.ne (show (3:Fin 4) ≠ 2 by decide))]
  ring

theorem polar3_linear_partial_fraction (q : Fin 3 → ℂ) (u ω : ℂ)
    (hq : Function.Injective q) (hu : ∀ j, u ≠ q j) :
    (u-ω)/(∏ j : Fin 3, (u-q j)) =
      ∑ j : Fin 3, ((q j-ω)/polarPoleDenominator q j)/(u-q j) := by
  have hu0 : (Finset.univ : Finset (Fin 3)).erase 0 = {1,2} := by decide
  have hu1 : (Finset.univ : Finset (Fin 3)).erase 1 = {0,2} := by decide
  have hu2 : (Finset.univ : Finset (Fin 3)).erase 2 = {0,1} := by decide
  norm_num [polarPoleDenominator,Fin.sum_univ_succ,Fin.prod_univ_succ,hu0,hu1,hu2,Finset.prod_insert]
  field_simp [sub_ne_zero.mpr (hu 0),
    sub_ne_zero.mpr (hu 1),
    sub_ne_zero.mpr (hu 2),
    sub_ne_zero.mpr (hq.ne (show (0:Fin 3) ≠ 1 by decide)),
    sub_ne_zero.mpr (hq.ne (show (0:Fin 3) ≠ 2 by decide)),
    sub_ne_zero.mpr (hq.ne (show (1:Fin 3) ≠ 0 by decide)),
    sub_ne_zero.mpr (hq.ne (show (1:Fin 3) ≠ 2 by decide)),
    sub_ne_zero.mpr (hq.ne (show (2:Fin 3) ≠ 0 by decide)),
    sub_ne_zero.mpr (hq.ne (show (2:Fin 3) ≠ 1 by decide))]
  ring

theorem polar4_linear_partial_fraction (q : Fin 4 → ℂ) (u ω : ℂ)
    (hq : Function.Injective q) (hu : ∀ j, u ≠ q j) :
    (u-ω)/(∏ j : Fin 4, (u-q j)) =
      ∑ j : Fin 4, ((q j-ω)/polarPoleDenominator q j)/(u-q j) := by
  have hu0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have hu1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have hu2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have hu3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  norm_num [polarPoleDenominator,Fin.sum_univ_succ,Fin.prod_univ_succ,hu0,hu1,hu2,hu3,Finset.prod_insert]
  field_simp [sub_ne_zero.mpr (hu 0),
    sub_ne_zero.mpr (hu 1),
    sub_ne_zero.mpr (hu 2),
    sub_ne_zero.mpr (hu 3),
    sub_ne_zero.mpr (hq.ne (show (0:Fin 4) ≠ 1 by decide)),
    sub_ne_zero.mpr (hq.ne (show (0:Fin 4) ≠ 2 by decide)),
    sub_ne_zero.mpr (hq.ne (show (0:Fin 4) ≠ 3 by decide)),
    sub_ne_zero.mpr (hq.ne (show (1:Fin 4) ≠ 0 by decide)),
    sub_ne_zero.mpr (hq.ne (show (1:Fin 4) ≠ 2 by decide)),
    sub_ne_zero.mpr (hq.ne (show (1:Fin 4) ≠ 3 by decide)),
    sub_ne_zero.mpr (hq.ne (show (2:Fin 4) ≠ 0 by decide)),
    sub_ne_zero.mpr (hq.ne (show (2:Fin 4) ≠ 1 by decide)),
    sub_ne_zero.mpr (hq.ne (show (2:Fin 4) ≠ 3 by decide)),
    sub_ne_zero.mpr (hq.ne (show (3:Fin 4) ≠ 0 by decide)),
    sub_ne_zero.mpr (hq.ne (show (3:Fin 4) ≠ 1 by decide)),
    sub_ne_zero.mpr (hq.ne (show (3:Fin 4) ≠ 2 by decide))]
  ring

private theorem polarPole_boundary_ne {n : ℕ} (q : Fin n → ℂ) (R : ℝ)
    (hR : ∀ j, ‖q j‖ < R) (u : ℂ) (hu : u ∈ sphere (0:ℂ) R) (j : Fin n) : u ≠ q j := by
  have hnorm : ‖u‖ = R := by simpa [mem_sphere,dist_eq_norm] using hu
  intro heq
  rw [heq] at hnorm
  exact (ne_of_lt (hR j)) hnorm

private theorem polarCircle_integrable_shift (x : ℝ) {n : ℕ} (q : Fin n → ℂ) (R : ℝ)
    (hpos : 0 < R) (hR : ∀ j, ‖q j‖ < R) (j : Fin n) (c : ℂ) :
    CircleIntegrable (fun u : ℂ => c*(Complex.exp ((x:ℂ)*u)/(u-q j))) 0 R := by
  apply ContinuousOn.circleIntegrable hpos.le
  exact continuousOn_const.mul
    ((by fun_prop : Continuous (fun u : ℂ => Complex.exp ((x:ℂ)*u))).continuousOn.div
      (continuous_id.sub continuous_const).continuousOn
      (fun u hu => sub_ne_zero.mpr (polarPole_boundary_ne q R hR u hu j)))

theorem polarCircle_exp_atPole (x : ℝ) (r : ℂ) (R : ℝ) (hR : ‖r‖ < R) :
    (∮ u in C(0,R), Complex.exp ((x:ℂ)*u)/(u-r)) =
      (2*(Real.pi:ℂ)*Complex.I)*Complex.exp ((x:ℂ)*r) := by
  have h := circle_exp_shift_atTime x (-r) R (by simpa using hR)
  simpa only [sub_eq_add_neg,mul_neg,neg_mul,neg_neg] using h

theorem polarGeneralInverseContour_sum (x : ℝ) (ω : ℂ) (q : Fin 4 → ℂ) (R : ℝ)
    (hq : Function.Injective q) (hR : ∀ j, ‖q j‖ < R) :
    polarGeneralInverseContour x ω q R =
      ∑ j : Fin 4, ((q j-ω)/polarPoleDenominator q j)*Complex.exp ((x:ℂ)*q j) := by
  have hpos : 0 < R := lt_of_le_of_lt (norm_nonneg (q 0)) (hR 0)
  unfold polarGeneralInverseContour
  have heq : (∮ u in C(0,R), Complex.exp ((x:ℂ)*u)*(u-ω)/(∏ j : Fin 4, (u-q j))) =
      ∮ u in C(0,R), ∑ j : Fin 4,
        ((q j-ω)/polarPoleDenominator q j)*(Complex.exp ((x:ℂ)*u)/(u-q j)) := by
    apply circleIntegral.integral_congr hpos.le
    intro u hu
    have h := polar4_linear_partial_fraction q u ω hq (polarPole_boundary_ne q R hR u hu)
    calc
      _ = Complex.exp ((x:ℂ)*u)*((u-ω)/(∏ j : Fin 4, (u-q j))) := by ring
      _ = _ := by rw [h,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [heq,circleIntegral.integral_fun_sum]
  · simp only [circleIntegral.integral_const_mul]
    simp_rw [polarCircle_exp_atPole x _ R (hR _)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hpi : (2*(Real.pi:ℂ)*Complex.I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    field_simp
  · intro j _
    exact polarCircle_integrable_shift x q R hpos hR j _

theorem polarGeneralInverseContour_atPole (x : ℝ) (q : Fin 4 → ℂ) (j : Fin 4) (R : ℝ)
    (hR : ∀ k, ‖q k‖ < R) :
    polarGeneralInverseContour x (q j) q R =
      polarTripleInverseContour x (fun k => q (j.succAbove k)) R := by
  have hpos : 0 < R := lt_of_le_of_lt (norm_nonneg (q 0)) (hR 0)
  unfold polarGeneralInverseContour polarTripleInverseContour
  congr 1
  apply circleIntegral.integral_congr hpos.le
  intro u hu
  have hn : u-q j ≠ 0 := sub_ne_zero.mpr (polarPole_boundary_ne q R hR u hu j)
  dsimp only
  rw [Fin.prod_univ_succAbove (fun k : Fin 4 => u-q k) j]
  field_simp

end SixthMoment
