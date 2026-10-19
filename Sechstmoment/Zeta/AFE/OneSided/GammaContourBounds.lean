import Sechstmoment.Zeta.Gamma.PolynomialIntegrability

/-! Uniform polynomial Gamma envelopes on the displaced horizontal edges.
All compact patches stay at imaginary height at least one, excluding poles. -/

namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section

theorem d04Gamma_vertical_strip_polynomial_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 1 ≤ |z.im| →
      (1+|z.im|)^k*‖Complex.Gamma z‖ ≤ C := by
  obtain ⟨V,hV,hlarge⟩ := d04Gamma_horizontal_polynomial_decay k 1 zero_lt_one
  let K : Set ℂ := (Icc (-1 : ℝ) 2 ×ℂ Icc (-V) V) ∩ {z : ℂ | 1 ≤ |z.im|}
  have hK : IsCompact K :=
    (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (by fun_prop))
  have hΓ : ContinuousOn Complex.Gamma K := by
    intro z hz
    apply (Complex.continuousAt_Gamma z ?_).continuousWithinAt
    intro n he
    have hi := congrArg Complex.im he
    simp only [Complex.neg_im,Complex.natCast_im,neg_zero] at hi
    have hzi : 1 ≤ |z.im| := hz.2
    norm_num [hi] at hzi
  let f : ℂ → ℝ := fun z => (1+|z.im|)^k*‖Complex.Gamma z‖
  have hf : ContinuousOn f K := (by fun_prop : ContinuousOn
    (fun z : ℂ => (1+|z.im|)^k) K).mul hΓ.norm
  obtain ⟨D,hD⟩ := hK.bddAbove_image hf
  let C : ℝ := max 1 D
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro z hz0 hz2 hzi
  by_cases hzV : |z.im| ≤ V
  · exact (hD (mem_image_of_mem f ⟨⟨⟨hz0,hz2⟩,abs_le.mp hzV⟩,hzi⟩)).trans
      (le_max_right _ _)
  · have he : (z.re : ℂ)+(z.im : ℂ)*I=z := by apply Complex.ext <;> simp
    have h := hlarge z.re z.im hz0 hz2 (le_of_lt (lt_of_not_ge hzV))
    rw [he] at h
    exact h.le.trans (le_max_left _ _)

theorem d04Gamma_horizontal_height_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T c v : ℝ, 4 ≤ T → -1 ≤ c → c ≤ 2 → |v|=T/4 →
      ‖Complex.Gamma ((c : ℂ)+(v : ℂ)*I)‖ ≤ C*4^k/T^k := by
  obtain ⟨C,hC,hΓ⟩ := d04Gamma_vertical_strip_polynomial_bound k
  refine ⟨C,hC,?_⟩
  intro T c v hT hc0 hc2 hv
  have hT0 : 0 < T := by linarith
  have hz := hΓ ((c : ℂ)+(v : ℂ)*I) (by simpa using hc0)
    (by simpa using hc2) (by simp; rw [hv]; linarith)
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hz
  have hm : (T/4)^k*‖Complex.Gamma ((c : ℂ)+(v : ℂ)*I)‖ ≤ C := by
    apply (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity : 0 ≤ T/4) (by rw [hv]; linarith) k)
      (norm_nonneg _)).trans hz
  have hk : 0 < (T/4)^k := by positivity
  calc
    _ ≤ C/(T/4)^k := (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using hm)
    _ = _ := by rw [div_pow]; field_simp

end
end Sechstmoment
