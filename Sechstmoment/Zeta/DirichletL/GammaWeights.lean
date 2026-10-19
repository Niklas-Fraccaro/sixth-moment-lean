import Sechstmoment.Analysis.Gaussian.Decay
import Sechstmoment.Zeta.Gamma.CompactStripEnvelope

/-! Gamma quotient estimates retaining the cancellation in the height.
These bounds depend on a fixed compact real strip, not on a character or a
conductor. They supply the estimates for the smooth-square AFE weights.
-/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped Topology
noncomputable section

theorem gamma_compact_strip_quotient_bound (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z w : ℂ, z.re ∈ Icc a b → w.re ∈ Icc a b →
      ‖Gamma z / Gamma w‖ ≤ C*(1+|z.im|)*(1+|w.im|)*
        Real.exp (Real.pi*|z.im-w.im|/2) := by
  obtain ⟨C,hC,hbound⟩ := gamma_compact_strip_envelopes a b ha hb
  refine ⟨C^2, by positivity, ?_⟩
  intro z w hz hw
  have htri : |w.im|-|z.im| ≤ |z.im-w.im| := by
    have h := abs_add_le (w.im-z.im) z.im
    rw [sub_add_cancel, abs_sub_comm w.im z.im] at h
    linarith
  rw [norm_div, div_eq_mul_inv]
  calc
    _ ≤ (C*(1+|z.im|)*Real.exp (-(Real.pi*|z.im|/2)))*
        (C*(1+|w.im|)*Real.exp (Real.pi*|w.im|/2)) := by
      gcongr
      · exact (hbound z hz).1
      · exact (hbound w hw).2
    _ = C^2*(1+|z.im|)*(1+|w.im|)*
        Real.exp (Real.pi*(|w.im|-|z.im|)/2) := by
      rw [show Real.pi*(|w.im|-|z.im|)/2 =
        -(Real.pi*|z.im|/2)+(Real.pi*|w.im|/2) by ring, Real.exp_add]
      ring
    _ ≤ _ := by gcongr

theorem gamma_compact_strip_nat_shift_bound (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖Gamma (z+m)‖ ≤ C*(1+|z.im|)^(m+1)*Real.exp (-(Real.pi*|z.im|/2)) := by
  induction m with
  | zero =>
    obtain ⟨C,hC,hbound⟩ := gamma_compact_strip_envelopes a b ha hb
    exact ⟨C,hC,fun z hz => by simpa using (hbound z hz).1⟩
  | succ m ih =>
    obtain ⟨C,hC,hbound⟩ := ih
    refine ⟨((m : ℝ)+2)*C, by positivity, ?_⟩
    intro z hz
    have hzm : z+(m : ℂ) ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [add_re, natCast_re, zero_re] at hr
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith [hz.1]
    have hzre : |z.re| ≤ 1 := by
      rw [abs_of_pos (by linarith [hz.1] : 0 < z.re)]
      linarith [hz.2]
    have hnorm : ‖z+(m : ℂ)‖ ≤ ((m : ℝ)+2)*(1+|z.im|) := by
      have hzN : ‖z‖ ≤ |z.re|+|z.im| := Complex.norm_le_abs_re_add_abs_im z
      have h := norm_add_le z (m : ℂ)
      simp only [Complex.norm_natCast] at h
      nlinarith [abs_nonneg z.im, Nat.cast_nonneg (α := ℝ) m]
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hzm, norm_mul]
    calc
      _ ≤ (((m : ℝ)+2)*(1+|z.im|))*
          (C*(1+|z.im|)^(m+1)*Real.exp (-(Real.pi*|z.im|/2))) := by
        gcongr
        exact hbound z hz
      _ = _ := by rw [pow_succ]; ring

theorem gamma_compact_strip_shifted_quotient_bound (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z w : ℂ, z.re ∈ Icc a b → w.re ∈ Icc a b →
      ‖Gamma (z+m)/Gamma w‖ ≤ C*(1+|z.im|)^(m+1)*(1+|w.im|)*
        Real.exp (Real.pi*|z.im-w.im|/2) := by
  obtain ⟨A,hA,hnum⟩ := gamma_compact_strip_nat_shift_bound a b ha hb m
  obtain ⟨B,hB,hden⟩ := gamma_compact_strip_envelopes a b ha hb
  refine ⟨A*B, by positivity, ?_⟩
  intro z w hz hw
  have htri : |w.im|-|z.im| ≤ |z.im-w.im| := by
    have h := abs_add_le (w.im-z.im) z.im
    rw [sub_add_cancel, abs_sub_comm w.im z.im] at h
    linarith
  rw [norm_div, div_eq_mul_inv]
  calc
    _ ≤ (A*(1+|z.im|)^(m+1)*Real.exp (-(Real.pi*|z.im|/2)))*
        (B*(1+|w.im|)*Real.exp (Real.pi*|w.im|/2)) := by
      gcongr
      · exact hnum z hz
      · exact (hden w hw).2
    _ = (A*B)*(1+|z.im|)^(m+1)*(1+|w.im|)*
        Real.exp (Real.pi*(|w.im|-|z.im|)/2) := by
      rw [show Real.pi*(|w.im|-|z.im|)/2 =
        -(Real.pi*|z.im|/2)+(Real.pi*|w.im|/2) by ring, Real.exp_add]
      ring
    _ ≤ _ := by gcongr

/-- Polynomial height loss, with the exponential depending only on the
vertical displacement, rather than on the height of either Gamma factor. -/
theorem gamma_compact_strip_vertical_ratio_bound (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc a b → ∀ y : ℝ,
      ‖Gamma (z+m+(y : ℂ)*I)/Gamma z‖ ≤
        C*(1+|z.im|)^(m+2)*(1+|y|)^(m+1)*Real.exp (Real.pi*|y|/2) := by
  obtain ⟨C,hC,hbound⟩ := gamma_compact_strip_shifted_quotient_bound a b ha hb m
  refine ⟨C,hC,?_⟩
  intro z hz y
  have h := hbound (z+(y : ℂ)*I) z (by simpa using hz) hz
  simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im,
    I_re, mul_zero, add_zero] at h
  rw [show z+(y : ℂ)*I+(m : ℂ) = z+(m : ℂ)+(y : ℂ)*I by ring] at h
  have hpoly : 1+|z.im+y| ≤ (1+|z.im|)*(1+|y|) := by
    have htri := abs_add_le z.im y
    nlinarith [mul_nonneg (abs_nonneg z.im) (abs_nonneg y)]
  have him : z.im+y-z.im = y := by ring
  rw [him] at h
  calc
    _ ≤ C*((1+|z.im|)*(1+|y|))^(m+1)*(1+|z.im|)*
        Real.exp (Real.pi*|y|/2) := by
      exact h.trans (by gcongr)
    _ = _ := by rw [mul_pow, show m+2 = (m+1)+1 by omega, pow_succ]; ring

end
end Sechstmoment.Source
