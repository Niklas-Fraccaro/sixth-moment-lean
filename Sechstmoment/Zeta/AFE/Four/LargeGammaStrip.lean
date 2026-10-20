import Mathlib.Tactic
import Sechstmoment.Zeta.Gamma.PositiveStrip


namespace Sechstmoment.Source
open Complex Filter Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem gamma_large_positive_strip_relative (r : ℕ) (σ y : ℝ)
    (hσ : σ ∈ Icc (1/8 : ℝ) ((r : ℝ)+7/8))
    (hy : 32*((r : ℝ)+1)^2 ≤ |y|) :
    ‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖ ≤
      2*(1+|y|)^(r+1)*‖Gamma ((1/2 : ℂ)+(y : ℂ)*I)‖ := by
  let s : ℂ := (1/2 : ℂ)+(y : ℂ)*I
  let u : ℂ := ((σ-1/2 : ℝ) : ℂ)
  let R : ℂ := (Gamma (s+u)/Gamma s)/s^u
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hsu : s+u = (σ : ℂ)+(y : ℂ)*I := by dsimp [s,u]; push_cast; ring
  have hu : ‖u‖ ≤ (r : ℝ)+1 := by
    dsimp [u]
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hσ.1],by linarith [hσ.2]⟩
  have hsi : s.im=y := by simp [s]
  have hsr : s.re=1/2 := by simp [s]
  have hy1 : 1 ≤ |y| := by nlinarith [sq_nonneg (r : ℝ)]
  have hu2 : ‖u‖^2 ≤ ((r : ℝ)+1)^2 := by nlinarith [norm_nonneg u]
  have hq : 8*(‖u‖+‖u‖^2) ≤ 16*((r : ℝ)+1)^2 := by
    nlinarith [sq_nonneg (r : ℝ)]
  have herr : ‖R-1‖ ≤ 1/2 := by
    have he := Sechstmoment.gammaRatio_normalized_error_vertical s u
      (by rw [hsr]; norm_num) (by rw [hsi]; exact hy1)
      (by rw [hsi]; nlinarith [sq_nonneg (r : ℝ)])
    apply he.trans
    rw [hsi,div_le_iff₀ (by linarith : 0 < |y|)]
    nlinarith
  have hR : ‖R‖ ≤ 2 := by
    have he := norm_add_le (R-1) (1 : ℂ)
    rw [sub_add_cancel,norm_one] at he
    linarith
  have hs0 : s ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    rw [hsr,Complex.zero_re] at h
    norm_num at h
  have hg0 := Gamma_ne_zero_of_re_pos (by rw [hsr]; norm_num)
  have hp0 : s^u ≠ 0 := by simp [hs0]
  have he : Gamma (s+u) = R*s^u*Gamma s := by dsimp [R]; field_simp
  have hs1 : 1 ≤ ‖s‖ := by
    exact hy1.trans (by simpa only [hsi] using Complex.abs_im_le_norm s)
  have hsN : ‖s‖ ≤ 1+|y| := by
    dsimp [s]
    exact (norm_add_le _ _).trans (by simp; linarith [abs_nonneg y])
  have hpN : ‖s^u‖ = ‖s‖^(σ-1/2) := by dsimp [u]; exact Complex.norm_cpow_real _ _
  have hp : ‖s^u‖ ≤ (1+|y|)^(r+1) := by
    rw [hpN]
    calc
      _ ≤ ‖s‖^((r+1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hs1 (by push_cast; linarith [hσ.2])
      _ = ‖s‖^(r+1) := Real.rpow_natCast _ _
      _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) hsN _
  rw [← hsu,he,norm_mul,norm_mul]
  gcongr

private theorem gamma_large_strip_compact_bound (r : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ y : ℝ,
      σ ∈ Icc (1/8 : ℝ) ((r : ℝ)+7/8) → |y|≤M →
      ‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖*Real.exp (Real.pi*|y|/2) ≤ C := by
  let K : Set (ℝ×ℝ) := Icc (1/8 : ℝ) ((r : ℝ)+7/8) ×ˢ Icc (-M) M
  let γ : ℝ×ℝ → ℂ := fun p => Gamma ((p.1 : ℂ)+(p.2 : ℂ)*I)
  have hγ : ContinuousOn γ K := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply (Complex.continuousAt_Gamma _ ?_).comp
    · fun_prop
    · intro n hn
      have h := congrArg Complex.re hn
      have hs : 1/8 ≤ p.1 := hp.1.1
      have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
      simp at h
      linarith
  let f : ℝ×ℝ → ℝ := fun p => ‖γ p‖*Real.exp (Real.pi*|p.2|/2)
  have hf : ContinuousOn f K := hγ.norm.mul (by fun_prop)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact K).bddAbove_image hf
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro σ y hσ hy
  exact (hC (mem_image_of_mem f (show (σ,y)∈K from ⟨hσ,abs_le.mp hy⟩))).trans
    (le_max_right _ _)

theorem gamma_large_positive_strip_envelope (r : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, z.re ∈ Icc (1/8 : ℝ) ((r : ℝ)+7/8) →
      ‖Gamma z‖ ≤ C*(1+|z.im|)^(r+1)*Real.exp (-(Real.pi*|z.im|/2)) := by
  obtain ⟨C₀,hC₀,hcompact⟩ :=
    gamma_large_strip_compact_bound r (32*((r : ℝ)+1)^2)
  let C : ℝ := max (C₀+1) (2*(2*Real.pi+1))
  have hC : 0<C := lt_of_lt_of_le (by linarith : 0<C₀+1) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro z hz
  have he : (z.re : ℂ)+(z.im : ℂ)*I=z := by apply Complex.ext <;> simp
  have hbound : ‖Gamma z‖*Real.exp (Real.pi*|z.im|/2) ≤ C*(1+|z.im|)^(r+1) := by
    by_cases hy : |z.im|≤32*((r : ℝ)+1)^2
    · have hc := hcompact z.re z.im hz hy
      rw [he] at hc
      exact hc.trans ((by linarith : C₀≤C₀+1).trans
        ((le_max_left _ _).trans
          (le_mul_of_one_le_right hC.le (one_le_pow₀ (by linarith [abs_nonneg z.im])))))
    · have hr := gamma_large_positive_strip_relative r z.re z.im hz (le_of_not_ge hy)
      rw [he] at hr
      have hh := (gamma_half_weighted_norm_bounds z.im).2
      calc
        _ ≤ 2*(1+|z.im|)^(r+1)*
            (‖Gamma ((1/2 : ℂ)+(z.im : ℂ)*I)‖*Real.exp (Real.pi*|z.im|/2)) := by
          have hm := mul_le_mul_of_nonneg_right hr
            (Real.exp_pos (Real.pi*|z.im|/2)).le
          simpa only [mul_assoc] using hm
        _ ≤ 2*(1+|z.im|)^(r+1)*(2*Real.pi+1) := by gcongr
        _ ≤ C*(1+|z.im|)^(r+1) := by
          have hc : 2*(2*Real.pi+1)≤C := le_max_right _ _
          calc
            _ = (2*(2*Real.pi+1))*(1+|z.im|)^(r+1) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hc
              (pow_nonneg (by linarith [abs_nonneg z.im]) (r+1))
  have hm := mul_le_mul_of_nonneg_right hbound
    (Real.exp_pos (-(Real.pi*|z.im|/2))).le
  simpa only [mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one] using hm

theorem bblrGamma_positive_strip_abs_sum (t v c : ℝ) (ht : 0≤t)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
    (∑ j : Fin 4, |((sourceZetaPoints t j+α j)/2).im|)-
      (∑ j : Fin 4, |((sourceZetaPoints t j+α j+((c:ℂ)+(v:ℂ)*I))/2).im|) ≤ 1 := by
  have hb (j : Fin 4) : |((sourceZetaPoints t j+α j)/2).im| ≤ t/2+1/8 := by
    have ha := (Complex.abs_im_le_norm (α j)).trans (hα j)
    have he : ((sourceZetaPoints t j+α j)/2).im =
        ((sourceZetaPoints t j).im+(α j).im)/2 := by simp
    rw [he,abs_div,show |(2:ℝ)|=2 by norm_num]
    have hp : |(sourceZetaPoints t j).im|=t := by
      fin_cases j <;> simp [sourceZetaPoints,criticalLinePoint,abs_of_nonneg ht]
    have h := abs_add_le (sourceZetaPoints t j).im (α j).im
    rw [hp] at h
    linarith
  have ha (j : Fin 4) := abs_le.mp ((Complex.abs_im_le_norm (α j)).trans (hα j))
  have h0 := le_abs_self (((sourceZetaPoints t 0+α 0+((c:ℂ)+(v:ℂ)*I))/2).im)
  have h1 := le_abs_self (((sourceZetaPoints t 1+α 1+((c:ℂ)+(v:ℂ)*I))/2).im)
  have h2 := neg_le_abs (((sourceZetaPoints t 2+α 2+((c:ℂ)+(v:ℂ)*I))/2).im)
  have h3 := neg_le_abs (((sourceZetaPoints t 3+α 3+((c:ℂ)+(v:ℂ)*I))/2).im)
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  have hb3 := hb 3
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have ha3 := ha 3
  simp only [Fin.sum_univ_succ,Fin.isValue,Fin.reduceSucc]
  simp [sourceZetaPoints,criticalLinePoint] at h0 h1 h2 h3 hb0 hb1 hb2 hb3 ⊢
  linarith

theorem bblrGammaQuotient_polynomial_large_positive_strip_bound (r : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ t v c : ℝ, 0≤t → 0≤c → c≤1+2*(r:ℝ) →
      ∀ α : MomentShifts, (∀ j, ‖α j‖≤1/4) →
      ‖bblrGammaQuotient t α ((c:ℂ)+(v:ℂ)*I)‖ ≤ C*(2+t+|v|)^(4*r+8) := by
  obtain ⟨D,hD,hΓ⟩ := gamma_large_positive_strip_envelope r
  obtain ⟨E,hE,hΓinv⟩ := gamma_positive_strip_envelopes
  refine ⟨(D*E)^4*Real.exp (Real.pi/2),by positivity,?_⟩
  intro t v c ht hc hcmax α hα
  let a : Fin 4 → ℂ := fun j => (sourceZetaPoints t j+α j+((c:ℂ)+(v:ℂ)*I))/2
  let b : Fin 4 → ℂ := fun j => (sourceZetaPoints t j+α j)/2
  let P : ℝ := 2+t+|v|
  have hP : 0<P := by dsimp [P]; positivity
  have hRe (j : Fin 4) :
      (a j).re∈Icc (1/8:ℝ) ((r:ℝ)+7/8) ∧ (b j).re∈Icc (1/8:ℝ) (7/8) := by
    have ha := abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))
    have hre := sourceZetaPoints_re t j
    dsimp [a,b]
    simp only [Complex.div_ofNat_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,hre,add_zero]
    constructor <;> constructor <;> linarith
  have hIm (j : Fin 4) : 1+|(a j).im|≤P ∧ 1+|(b j).im|≤P := by
    have ha := (Complex.abs_im_le_norm (α j)).trans (hα j)
    have hp : |(sourceZetaPoints t j).im|=t := by
      fin_cases j <;> simp [sourceZetaPoints,criticalLinePoint,abs_of_nonneg ht]
    have hba := abs_add_le (sourceZetaPoints t j).im (α j).im
    rw [hp] at hba
    have haa := abs_add_le ((sourceZetaPoints t j).im+(α j).im) v
    dsimp [a,b,P]
    simp only [Complex.div_ofNat_im,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero,zero_add,
      abs_div,show |(2:ℝ)|=2 by norm_num]
    constructor <;> linarith [abs_nonneg v]
  have hFactor (j : Fin 4) : ‖Gamma (a j)/Gamma (b j)‖ ≤
      (D*E*P^(r+2))*Real.exp (Real.pi*(|(b j).im|-|(a j).im|)/2) := by
    have hn := hΓ (a j) (hRe j).1
    have hd := (hΓinv (b j) (hRe j).2).2
    rw [norm_div,div_eq_mul_inv]
    calc
      _ ≤ (D*(1+|(a j).im|)^(r+1)*Real.exp (-(Real.pi*|(a j).im|/2)))*
          (E*(1+|(b j).im|)*Real.exp (Real.pi*|(b j).im|/2)) := by gcongr
      _ ≤ (D*P^(r+1)*Real.exp (-(Real.pi*|(a j).im|/2)))*
          (E*P*Real.exp (Real.pi*|(b j).im|/2)) := by
        gcongr
        · exact (hIm j).1
        · exact (hIm j).2
      _ = _ := by
        rw [show (D*P^(r+1)*Real.exp (-(Real.pi*|(a j).im|/2)))*
            (E*P*Real.exp (Real.pi*|(b j).im|/2)) =
            D*E*(P^(r+1)*P)*(Real.exp (-(Real.pi*|(a j).im|/2))*
              Real.exp (Real.pi*|(b j).im|/2)) by ring,
          ← Real.exp_add,← pow_succ]
        congr 2
        ring
  have hsum : (∑ j : Fin 4, Real.pi*(|(b j).im|-|(a j).im|)/2)≤Real.pi/2 := by
    have hs := bblrGamma_positive_strip_abs_sum t v c ht α hα
    have he : (∑ j : Fin 4, Real.pi*(|(b j).im|-|(a j).im|)/2) =
        (Real.pi/2)*((∑ j : Fin 4, |(b j).im|)-(∑ j : Fin 4, |(a j).im|)) := by
      rw [← Finset.sum_sub_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hs (by positivity : 0≤Real.pi/2)).trans_eq (mul_one _)
  change ‖∏ j : Fin 4, Gamma (a j)/Gamma (b j)‖≤_
  rw [norm_prod]
  calc
    _ ≤ ∏ j : Fin 4, (D*E*P^(r+2))*Real.exp (Real.pi*(|(b j).im|-|(a j).im|)/2) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hFactor j)
    _ = (D*E*P^(r+2))^4*Real.exp
        (∑ j : Fin 4, Real.pi*(|(b j).im|-|(a j).im|)/2) := by
      rw [Finset.prod_mul_distrib,← Real.exp_sum]
      simp
    _ ≤ (D*E*P^(r+2))^4*Real.exp (Real.pi/2) := by gcongr
    _ = _ := by
      dsimp [P]
      rw [mul_pow,← pow_mul,show (r+2)*4=4*r+8 by omega]
      ring

end
end Sechstmoment.Source
