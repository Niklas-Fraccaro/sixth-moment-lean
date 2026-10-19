import Sechstmoment.Numerator.V.Contour.PolynomialAdditiveReduction

/-! Exact normalization budgets for the proven power-saving errors and
global bounds for the actual zero-extended polynomial profiles. -/

namespace Sechstmoment.Source
open Complex Real Set Polynomial
noncomputable section
set_option autoImplicit false

theorem polynomialProfile_global_norm_bound {η : ℝ} (hη : 0 < η) (P : ℝ[X]) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, ‖(zeroExtendedPolynomialProfile η P x:ℂ)‖ ≤ B := by
  obtain ⟨B,hB,HB⟩ := polynomialProfile_uniform_bound hη P
  refine ⟨B,hB,?_⟩
  intro x
  rw [Complex.norm_real,Real.norm_eq_abs]
  by_cases hx : x ∈ Icc (0:ℝ) η
  · exact HB x hx
  · have hn : x ∉ Ico (0:ℝ) η := fun h => hx ⟨h.1,h.2.le⟩
    rw [zeroExtendedPolynomialProfile,Set.indicator_of_notMem hn,abs_zero]
    exact hB.le

theorem normalized_power_log_error {T C a : ℝ} (hT : 0 < T)
    (hL : 1 ≤ Real.log T) (hC : 0 ≤ C) :
    C*T^a*(Real.log T)^4/(T*(Real.log T)^9) ≤ C*T^(a-1) := by
  have hL0 : 0 < Real.log T := by linarith
  have h49 : (Real.log T)^4 ≤ (Real.log T)^9 :=
    pow_le_pow_right₀ hL (by norm_num : (4:ℕ) ≤ 9)
  have hr : (Real.log T)^4/(Real.log T)^9 ≤ 1 :=
    (div_le_one (pow_pos hL0 9)).mpr h49
  calc
    _ = (C*T^(a-1))*((Real.log T)^4/(Real.log T)^9) := by
      rw [Real.rpow_sub_one hT.ne']
      simp only [div_eq_mul_inv,mul_inv]
      ring
    _ ≤ (C*T^(a-1))*1 := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := mul_one _

theorem normalized_power_error {T C a : ℝ} (hT : 0 < T)
    (hL : 1 ≤ Real.log T) (hC : 0 ≤ C) :
    C*T^a/(T*(Real.log T)^9) ≤ C*T^(a-1) := by
  have hL0 : 0 < Real.log T := by linarith
  have hr : 1/(Real.log T)^9 ≤ 1 :=
    (div_le_one (pow_pos hL0 9)).mpr (one_le_pow₀ hL)
  calc
    _ = (C*T^(a-1))*(1/(Real.log T)^9) := by
      rw [Real.rpow_sub_one hT.ne']
      simp only [div_eq_mul_inv,mul_inv]
      ring
    _ ≤ (C*T^(a-1))*1 := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := mul_one _

theorem norm_time_log_denominator {T : ℝ} (hT : 0 < T) (hL : 0 < Real.log T) (n : ℕ) :
    ‖(T:ℂ)*(Real.log T:ℂ)^n‖ = T*(Real.log T)^n := by
  rw [norm_mul,norm_pow,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hT,abs_of_pos hL]

end
end Sechstmoment.Source
