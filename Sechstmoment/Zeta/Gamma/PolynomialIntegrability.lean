import Sechstmoment.Zeta.Gamma.VerticalDecay

/-! Polynomially weighted absolute Gamma integrability on every actual D04
vertical line avoiding the Gamma pole at zero. -/

namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section

private theorem d04Gamma_vertical_line_continuous {c : ℝ}
    (hc : -1 < c) (hc0 : c ≠ 0) :
    Continuous (fun v : ℝ => Complex.Gamma ((c : ℂ)+(v : ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
  intro n he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,
    add_zero,Complex.neg_re,Complex.natCast_re] at hr
  rcases Nat.eq_zero_or_pos n with hn|hn
  · simp [hn] at hr
    exact hc0 hr
  · have hcast : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith

/-- An integrable rational envelope controls Gamma multiplied by any fixed
polynomial on the vertical lines used by the one-sided contour shift. -/
theorem d04Gamma_vertical_polynomial_rational_bound {c : ℝ}
    (hc : -1 < c) (hc2 : c ≤ 2) (hc0 : c ≠ 0) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
      (1+|v|)^k*‖Complex.Gamma ((c : ℂ)+(v : ℂ)*I)‖ ≤ C*(1+v^2)⁻¹ := by
  obtain ⟨V,hV,hlarge⟩ := d04Gamma_horizontal_polynomial_decay (k+2) 1 zero_lt_one
  let f : ℝ → ℝ := fun v =>
    ((1+|v|)^k*‖Complex.Gamma ((c : ℂ)+(v : ℂ)*I)‖)*(1+v^2)
  have hf : Continuous f := by
    have hΓ := d04Gamma_vertical_line_continuous hc hc0
    dsimp [f]
    fun_prop
  obtain ⟨D,hD⟩ := isCompact_Icc.bddAbove_image
    (hf.continuousOn : ContinuousOn f (Icc (-V) V))
  let C : ℝ := max 1 D
  have hC : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro v
  rw [← div_eq_mul_inv,le_div_iff₀ (by positivity : 0 < 1+v^2)]
  by_cases hv : |v| ≤ V
  · exact (hD (mem_image_of_mem f (abs_le.mp hv))).trans (le_max_right _ _)
  · have h := hlarge c v hc.le hc2 (le_of_lt (lt_of_not_ge hv))
    have hsq : 1+v^2 ≤ (1+|v|)^2 := by nlinarith [abs_nonneg v,sq_abs v]
    calc
      _ ≤ ((1+|v|)^k*‖Complex.Gamma ((c : ℂ)+(v : ℂ)*I)‖)*(1+|v|)^2 := by gcongr
      _ = (1+|v|)^(k+2)*‖Complex.Gamma ((c : ℂ)+(v : ℂ)*I)‖ := by rw [pow_add]; ring
      _ ≤ 1 := h.le
      _ ≤ C := le_max_left _ _

theorem d04Gamma_vertical_polynomial_norm_integrable {c : ℝ}
    (hc : -1 < c) (hc2 : c ≤ 2) (hc0 : c ≠ 0) (k : ℕ) :
    Integrable (fun v : ℝ => (1+|v|)^k*‖Complex.Gamma ((c : ℂ)+(v : ℂ)*I)‖) := by
  obtain ⟨C,hC,hbound⟩ := d04Gamma_vertical_polynomial_rational_bound hc hc2 hc0 k
  apply (integrable_inv_one_add_sq.const_mul C).mono'
  · have hΓ := d04Gamma_vertical_line_continuous hc hc0
    apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with v
    simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity :
      0 ≤ (1+|v|)^k*‖Complex.Gamma ((c : ℂ)+(v : ℂ)*I)‖)] using hbound v

theorem d04Gamma_vertical_polynomial_integrable {c : ℝ}
    (hc : -1 < c) (hc2 : c ≤ 2) (hc0 : c ≠ 0) (k : ℕ) :
    Integrable (fun v : ℝ => (((1+|v|)^k : ℝ):ℂ)*
      Complex.Gamma ((c : ℂ)+(v : ℂ)*I)) := by
  have h := d04Gamma_vertical_polynomial_norm_integrable hc hc2 hc0 k
  apply h.mono'
  · have hΓ := d04Gamma_vertical_line_continuous hc hc0
    apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with v
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (1+|v|)^k)]

end
end Sechstmoment
