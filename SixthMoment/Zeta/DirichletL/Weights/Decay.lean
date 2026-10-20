import SixthMoment.Zeta.DirichletL.Weights.Shift


namespace SixthMoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

theorem squareSmoothGammaRatio_nat_line_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1/4 : ℝ) (3/4) →
      ∀ a : ℕ, a ≤ 1 → ∀ y : ℝ,
      ‖Complex.Gamma ((s+(a : ℂ)+(2*(m : ℂ)+(y : ℂ)*I))/2)/
          Complex.Gamma ((s+(a : ℂ))/2)‖ ≤
        C*(1+|s.im|)^(m+2)*(1+|y|)^(m+1)*Real.exp (Real.pi*|y|/4) := by
  obtain ⟨C,hC,hbound⟩ := gamma_compact_strip_vertical_ratio_bound
    (1/8) (7/8) (by norm_num) (by norm_num) m
  refine ⟨C,hC,?_⟩
  intro s hs a ha y
  let z : ℂ := (s+(a : ℂ))/2
  have hz : z.re ∈ Icc (1/8 : ℝ) (7/8) := by
    dsimp [z]
    simp only [Complex.div_ofNat_re, add_re, natCast_re]
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have ha1 : (a : ℝ) ≤ 1 := by exact_mod_cast ha
    constructor <;> linarith [hs.1,hs.2]
  have h := hbound z hz (y/2)
  have harg : (s+(a : ℂ)+(2*(m : ℂ)+(y : ℂ)*I))/2 = z+(m : ℂ)+(y/2 : ℝ)*I := by
    dsimp [z]
    push_cast
    ring
  rw [harg]
  have he : Real.pi*|y/2|/2 = Real.pi*|y|/4 := by
    rw [abs_div]
    norm_num
    ring
  rw [he] at h
  have hzi : |z.im| ≤ |s.im| := by
    dsimp [z]
    simp only [Complex.div_ofNat_im, add_im, natCast_im, add_zero, abs_div]
    norm_num
  have hy : |y/2| ≤ |y| := by rw [abs_div]; norm_num
  exact h.trans (by gcongr)

theorem squareSmoothWeight_nat_decay (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1/4 : ℝ) (3/4) →
      ∀ a : ℕ, a ≤ 1 → ∀ x : ℝ, 0 < x →
      ‖squareSmoothWeight s a x‖ ≤
        C*(1+|s.im|)^((m+2)*2)*x^(-(2*(m : ℝ))) := by
  obtain ⟨B,hB,hbound⟩ := squareSmoothGammaRatio_nat_line_bound m
  let c : ℝ := 2*(m : ℝ)
  have hc : 0 < c := by dsimp [c]; exact_mod_cast (by omega : 0 < 2*m)
  let g : ℝ → ℝ := fun y => (1+|y|)^((m+1)*2)*Real.exp (Real.pi*|y|/2-y^2)
  have hg : Integrable g := by
    simpa only [g, div_mul_eq_mul_div] using
      gaussianPolynomialExponential_integrable ((m+1)*2) (Real.pi/2)
  have hg0 : 0 ≤ ∫ y : ℝ, g y := integral_nonneg (fun y => by dsimp [g]; positivity)
  let A : ℝ := Real.exp (c^2)*B^2
  refine ⟨A*((∫ y : ℝ, g y)+1)/(2*Real.pi), by dsimp [A]; positivity, ?_⟩
  intro s hs a ha x hx
  let H : ℝ := 1+|s.im|
  have hH : 0 < H := by dsimp [H]; positivity
  have hpoint (y : ℝ) :
      ‖squareSmoothGammaContour s a x ((c : ℂ)+(y : ℂ)*I)/((c : ℂ)+(y : ℂ)*I)‖ ≤
        (A*H^((m+2)*2)*x^(-c))*g y := by
    have hratio := hbound s hs a ha y
    have hcast : (c : ℂ) = 2*(m : ℂ) := by dsimp [c]; push_cast; rfl
    rw [← hcast] at hratio
    have hden : 1 ≤ ‖(c : ℂ)+(y : ℂ)*I‖ := by
      have h := Complex.re_le_norm ((c : ℂ)+(y : ℂ)*I)
      have hc1 : 1 ≤ c := by dsimp [c]; exact_mod_cast (by omega : 1 ≤ 2*m)
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
        mul_one, sub_self, add_zero] at h
      exact hc1.trans h
    have he : ‖Complex.exp (((c : ℂ)+(y : ℂ)*I)^2)‖ = Real.exp (c^2)*Real.exp (-y^2) := by
      rw [Complex.norm_exp, ← Real.exp_add]
      congr 1
      norm_num [pow_two, sub_eq_add_neg]
    have he2 : (Real.exp (Real.pi*|y|/4))^2 = Real.exp (Real.pi*|y|/2) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [norm_div]
    apply (div_le_self (norm_nonneg _) hden).trans
    rw [squareSmoothGammaContour, norm_mul, norm_mul, norm_pow,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have him : (-((c : ℂ)+(y : ℂ)*I)).re = -c := by simp
    rw [him, he]
    calc
      _ ≤ (Real.exp (c^2)*Real.exp (-y^2))*
          (B*H^(m+2)*(1+|y|)^(m+1)*Real.exp (Real.pi*|y|/4))^2*x^(-c) := by
        gcongr
      _ = _ := by
        simp only [mul_pow, ← pow_mul, he2]
        dsimp only [A,g]
        rw [show Real.pi*|y|/2-y^2 = (-y^2)+(Real.pi*|y|/2) by ring, Real.exp_add]
        ring
  rw [squareSmoothWeight_eq_vertical_integral s a x c (by linarith [hs.1]) hx hc, norm_div]
  have hp : ‖(2*Real.pi : ℂ)‖ = 2*Real.pi := by
    simp
  rw [hp]
  have hnorm := norm_integral_le_of_norm_le
    (hg.const_mul (A*H^((m+2)*2)*x^(-c))) (Eventually.of_forall hpoint)
  rw [integral_const_mul] at hnorm
  calc
    _ ≤ ((A*H^((m+2)*2)*x^(-c))*(∫ y : ℝ, g y))/(2*Real.pi) :=
      div_le_div_of_nonneg_right hnorm (by positivity)
    _ ≤ ((A*H^((m+2)*2)*x^(-c))*((∫ y : ℝ, g y)+1))/(2*Real.pi) := by
      gcongr
      linarith
    _ = _ := by dsimp [H,c]; ring

end
end SixthMoment.Source
