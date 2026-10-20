import SixthMoment.Zeta.DirichletL.Weights.Decay
import SixthMoment.Zeta.DirichletL.Weights.Residue


namespace SixthMoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

theorem squareSmoothGammaRatio_left_line_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1/4 : ℝ) (3/4) →
      ∀ a : ℕ, a ≤ 1 → ∀ y : ℝ,
      ‖Complex.Gamma ((s+(a : ℂ)+(-1/16+(y : ℂ)*I))/2)/
          Complex.Gamma ((s+(a : ℂ))/2)‖ ≤
        C*(1+|s.im|)^2*(1+|y|)*Real.exp (Real.pi*|y|/4) := by
  obtain ⟨C,hC,hbound⟩ := gamma_compact_strip_quotient_bound
    (1/16) (15/16) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro s hs a ha y
  let z : ℂ := (s+(a : ℂ)+(-1/16+(y : ℂ)*I))/2
  let w : ℂ := (s+(a : ℂ))/2
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have ha1 : (a : ℝ) ≤ 1 := by exact_mod_cast ha
  have hz : z.re ∈ Icc (1/16 : ℝ) (15/16) := by
    dsimp [z]
    norm_num only [Complex.div_ofNat_re, add_re, natCast_re, mul_re, ofReal_re,
      ofReal_im, I_re, mul_zero, I_im, mul_one, sub_self, add_zero,
      neg_re, one_re, re_ofNat]
    constructor <;> linarith [hs.1,hs.2]
  have hw : w.re ∈ Icc (1/16 : ℝ) (15/16) := by
    dsimp [w]
    simp only [Complex.div_ofNat_re, add_re, natCast_re]
    constructor <;> linarith [hs.1,hs.2]
  have h := hbound z w hz hw
  have him : z.im-w.im = y/2 := by dsimp [z,w]; norm_num; ring
  have he : Real.pi*|z.im-w.im|/2 = Real.pi*|y|/4 := by
    rw [him, abs_div]
    norm_num
    ring
  rw [he] at h
  have hzpoly : 1+|z.im| ≤ (1+|s.im|)*(1+|y|) := by
    have hzi : z.im = (s.im+y)/2 := by dsimp [z]; norm_num
    rw [hzi, abs_div]
    norm_num
    nlinarith [abs_add_le s.im y, abs_nonneg s.im, abs_nonneg y,
      mul_nonneg (abs_nonneg s.im) (abs_nonneg y)]
  have hwpoly : 1+|w.im| ≤ 1+|s.im| := by dsimp [w]; norm_num [abs_div]
  calc
    _ ≤ C*((1+|s.im|)*(1+|y|))*(1+|s.im|)*Real.exp (Real.pi*|y|/4) := by
      exact h.trans (by gcongr)
    _ = _ := by ring

theorem squareSmoothWeight_small_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1/4 : ℝ) (3/4) →
      ∀ a : ℕ, a ≤ 1 → ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖squareSmoothWeight s a x‖ ≤ C*(1+|s.im|)^4 := by
  obtain ⟨B,hB,hbound⟩ := squareSmoothGammaRatio_left_line_bound
  let c : ℝ := -1/16
  let g : ℝ → ℝ := fun y => (1+|y|)^2*Real.exp (Real.pi*|y|/2-y^2)
  have hg : Integrable g := by
    simpa only [g, div_mul_eq_mul_div] using gaussianPolynomialExponential_integrable 2 (Real.pi/2)
  have hg0 : 0 ≤ ∫ y : ℝ, g y := integral_nonneg (fun y => by dsimp [g]; positivity)
  let A : ℝ := 16*Real.exp (c^2)*B^2
  let D : ℝ := A*(∫ y : ℝ, g y)/(2*Real.pi)
  have hD : 0 ≤ D := by dsimp [D,A]; positivity
  refine ⟨1+D, by positivity, ?_⟩
  intro s hs a ha x hx hx1
  let H : ℝ := 1+|s.im|
  have hH : 1 ≤ H := by dsimp [H]; linarith [abs_nonneg s.im]
  have hpoint (y : ℝ) :
      ‖squareSmoothGammaContour s a x ((c : ℂ)+(y : ℂ)*I)/((c : ℂ)+(y : ℂ)*I)‖ ≤
        (A*H^4)*g y := by
    have hratio := hbound s hs a ha y
    have hcast : (c : ℂ) = -1/16 := by norm_num [c]
    rw [← hcast] at hratio
    have hden : (1/16 : ℝ) ≤ ‖(c : ℂ)+(y : ℂ)*I‖ := by
      have h := Complex.abs_re_le_norm ((c : ℂ)+(y : ℂ)*I)
      norm_num [c] at h ⊢
      exact h
    have he : ‖Complex.exp (((c : ℂ)+(y : ℂ)*I)^2)‖ = Real.exp (c^2)*Real.exp (-y^2) := by
      rw [Complex.norm_exp, ← Real.exp_add]
      congr 1
      norm_num [pow_two, sub_eq_add_neg]
    have he2 : (Real.exp (Real.pi*|y|/4))^2 = Real.exp (Real.pi*|y|/2) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hxpow : ‖(x : ℂ)^(-((c : ℂ)+(y : ℂ)*I))‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      have hr : (-((c : ℂ)+(y : ℂ)*I)).re = 1/16 := by norm_num [c]
      rw [hr]
      exact Real.rpow_le_one hx.le hx1 (by norm_num)
    rw [norm_div]
    calc
      _ ≤ ‖squareSmoothGammaContour s a x ((c : ℂ)+(y : ℂ)*I)‖/(1/16 : ℝ) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden
      _ = 16*‖squareSmoothGammaContour s a x ((c : ℂ)+(y : ℂ)*I)‖ := by ring
      _ ≤ 16*((Real.exp (c^2)*Real.exp (-y^2))*
          (B*H^2*(1+|y|)*Real.exp (Real.pi*|y|/4))^2*1) := by
        rw [squareSmoothGammaContour, norm_mul, norm_mul, norm_pow, he]
        gcongr
      _ = _ := by
        simp only [mul_pow, ← pow_mul, he2]
        dsimp only [A,g]
        rw [show Real.pi*|y|/2-y^2 = (-y^2)+(Real.pi*|y|/2) by ring, Real.exp_add]
        norm_num
        ring
  have hnorm := norm_integral_le_of_norm_le (hg.const_mul (A*H^4)) (Eventually.of_forall hpoint)
  rw [integral_const_mul] at hnorm
  have hleft : ‖(∫ y : ℝ, squareSmoothGammaContour s a x ((c : ℂ)+(y : ℂ)*I)/
      ((c : ℂ)+(y : ℂ)*I))/(2*Real.pi : ℂ)‖ ≤ D*H^4 := by
    rw [norm_div, show ‖(2*Real.pi : ℂ)‖ = 2*Real.pi by simp]
    apply (div_le_div_of_nonneg_right hnorm (by positivity)).trans_eq
    dsimp only [D]
    ring
  rw [squareSmoothWeight_eq_residue_left s a x (1/16) hx (by norm_num) (by
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith [hs.1])]
  calc
    _ ≤ 1+D*H^4 := by
      exact (norm_add_le _ _).trans (by simpa [c, div_eq_mul_inv] using add_le_add_left hleft 1)
    _ ≤ (1+D)*H^4 := by nlinarith [one_le_pow₀ hH (n := 4)]

theorem squareSmoothWeight_uniform_decay (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1/4 : ℝ) (3/4) →
      ∀ a : ℕ, a ≤ 1 → ∀ x : ℝ, 0 < x →
      ‖squareSmoothWeight s a x‖ ≤
        C*(1+|s.im|)^((m+2)*2)/(1+x)^(2*m) := by
  obtain ⟨A,hA,hsmall⟩ := squareSmoothWeight_small_bound
  obtain ⟨B,hB,hlarge⟩ := squareSmoothWeight_nat_decay m hm
  refine ⟨(2 : ℝ)^(2*m)*(A+B), by positivity, ?_⟩
  intro s hs a ha x hx
  let H : ℝ := 1+|s.im|
  have hH : 1 ≤ H := by dsimp [H]; linarith [abs_nonneg s.im]
  have hHpow : H^4 ≤ H^((m+2)*2) := pow_le_pow_right₀ hH (by omega)
  have hden : 0 < (1+x)^(2*m) := by positivity
  apply (le_div_iff₀ hden).mpr
  by_cases hx1 : x ≤ 1
  · have hxpow : (1+x)^(2*m) ≤ (2 : ℝ)^(2*m) := pow_le_pow_left₀ (by positivity) (by linarith) _
    have h := hsmall s hs a ha x hx hx1
    change ‖squareSmoothWeight s a x‖ ≤ A*H^4 at h
    calc
      _ ≤ (A*H^4)*(2 : ℝ)^(2*m) := mul_le_mul h hxpow (by positivity) (by positivity)
      _ ≤ (A*H^((m+2)*2))*(2 : ℝ)^(2*m) := by gcongr
      _ ≤ _ := by
        have hAB : A ≤ A+B := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hAB (by positivity : 0 ≤ H^((m+2)*2)*(2 : ℝ)^(2*m))]

  · have hxge : 1 ≤ x := le_of_not_ge hx1
    have hxpow : (1+x)^(2*m) ≤ (2*x)^(2*m) := pow_le_pow_left₀ (by positivity) (by linarith) _
    have h := hlarge s hs a ha x hx
    have hexp : x^(-(2*(m : ℝ))) = (x^(2*m))⁻¹ := by
      rw [Real.rpow_neg hx.le]
      congr 1
      rw [show (2 : ℝ)*(m : ℝ) = ((2*m : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]
    rw [hexp] at h
    change ‖squareSmoothWeight s a x‖ ≤ B*H^((m+2)*2)*(x^(2*m))⁻¹ at h
    calc
      _ ≤ (B*H^((m+2)*2)*(x^(2*m))⁻¹)*(2*x)^(2*m) :=
        mul_le_mul h hxpow (by positivity) (by positivity)
      _ = (B*H^((m+2)*2))*(2 : ℝ)^(2*m) := by
        rw [mul_pow]
        field_simp
      _ ≤ _ := by
        have hAB : B ≤ A+B := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hAB (by positivity : 0 ≤ H^((m+2)*2)*(2 : ℝ)^(2*m))]


theorem rpow_le_one_add {x δ : ℝ} (hx : 0 < x) (hδ : δ ∈ Icc (0 : ℝ) 1) :
    x^δ ≤ 1+x := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx.le hx1 hδ.1).trans (by linarith)
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hδ.2
    rw [Real.rpow_one] at h
    linarith

theorem squareSmoothWeight_scaled_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ s : ℂ,
      s.re ∈ Icc (1/4 : ℝ) (3/4) → ∀ a : ℕ, a ≤ 1 →
      ∀ n : ℕ, 0 < n → ∀ δ : ℝ, δ ∈ Icc (0 : ℝ) 1 →
      ((n/N : ℕ)+1 : ℝ)*‖squareSmoothWeight s a (Real.pi*(n : ℝ)/(N : ℝ))‖ ≤
        C*(1+|s.im|)^6*(N : ℝ)^δ/(n : ℝ)^δ := by
  obtain ⟨C,hC,hbound⟩ := squareSmoothWeight_uniform_decay 1 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro N hN s hs a ha n hn δ hδ
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let r : ℝ := (n : ℝ)/(N : ℝ)
  have hr : 0 < r := div_pos hn' hN'
  let x : ℝ := Real.pi*(n : ℝ)/(N : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hrx : r ≤ x := by
    dsimp [r,x]
    have hp : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
    exact div_le_div_of_nonneg_right (by nlinarith) hN'.le
  have hfloor : ((n/N : ℕ)+1 : ℝ) ≤ 1+r := by
    have h := Nat.cast_div_le (α := ℝ) (m := n) (n := N)
    dsimp [r]
    linarith
  have h := hbound s hs a ha x hx
  norm_num only at h
  have hscale : ((n/N : ℕ)+1 : ℝ)*‖squareSmoothWeight s a x‖ ≤
      C*(1+|s.im|)^6/(1+r) := by
    calc
      _ ≤ (1+r)*(C*(1+|s.im|)^6/(1+x)^2) :=
        mul_le_mul hfloor h (norm_nonneg _) (by positivity)
      _ ≤ (1+r)*(C*(1+|s.im|)^6/(1+r)^2) := by gcongr
      _ = _ := by field_simp
  have hp := rpow_le_one_add hr hδ
  have hpow : 0 < r^δ := Real.rpow_pos_of_pos hr δ
  calc
    _ ≤ C*(1+|s.im|)^6/(1+r) := hscale
    _ ≤ C*(1+|s.im|)^6/r^δ := div_le_div_of_nonneg_left (by positivity) hpow hp
    _ = _ := by
      dsimp [r]
      rw [Real.div_rpow hn'.le hN'.le]
      field_simp

end
end SixthMoment.Source
