import SixthMoment.Zeta.AFE.Four.Integrability
import SixthMoment.Zeta.Gamma.StripEnvelope


namespace SixthMoment.Source
open Complex Filter Set
open scoped BigOperators Topology
noncomputable section

private theorem bblr_Gamma_line_abs_sum (t v : ℝ) (ht : 0 ≤ t)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    (∑ j : Fin 4, |((sourceZetaPoints t j+α j)/2).im|) -
      (∑ j : Fin 4, |((sourceZetaPoints t j+α j+(1+(v : ℂ)*I))/2).im|) ≤ 1 := by
  have hb (j : Fin 4) : |((sourceZetaPoints t j+α j)/2).im| ≤ t/2+1/8 := by
    have ha := (Complex.abs_im_le_norm (α j)).trans (hα j)
    have he : ((sourceZetaPoints t j+α j)/2).im =
        ((sourceZetaPoints t j).im+(α j).im)/2 := by simp
    rw [he, abs_div, show |(2 : ℝ)| = 2 by norm_num]
    have hp : |(sourceZetaPoints t j).im| = t := by
      fin_cases j <;> simp [sourceZetaPoints, criticalLinePoint, abs_of_nonneg ht]
    have h := abs_add_le (sourceZetaPoints t j).im (α j).im
    rw [hp] at h
    linarith
  have ha (j : Fin 4) := abs_le.mp ((Complex.abs_im_le_norm (α j)).trans (hα j))
  have h0 := le_abs_self (((sourceZetaPoints t 0+α 0+(1+(v : ℂ)*I))/2).im)
  have h1 := le_abs_self (((sourceZetaPoints t 1+α 1+(1+(v : ℂ)*I))/2).im)
  have h2 := neg_le_abs (((sourceZetaPoints t 2+α 2+(1+(v : ℂ)*I))/2).im)
  have h3 := neg_le_abs (((sourceZetaPoints t 3+α 3+(1+(v : ℂ)*I))/2).im)
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  have hb3 := hb 3
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have ha3 := ha 3
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.reduceSucc]
  simp [sourceZetaPoints, criticalLinePoint] at h0 h1 h2 h3 hb0 hb1 hb2 hb3 ⊢
  linarith

theorem bblrGammaQuotient_polynomial_line_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t v : ℝ, 0 ≤ t → ∀ α : MomentShifts,
      (∀ j, ‖α j‖ ≤ 1/4) →
      ‖bblrGammaQuotient t α (1+(v : ℂ)*I)‖ ≤ C*(2+t+|v|)^8 := by
  obtain ⟨D,hD,hΓ⟩ := gamma_positive_strip_envelopes
  refine ⟨D^8*Real.exp (Real.pi/2), by positivity, ?_⟩
  intro t v ht α hα
  let a : Fin 4 → ℂ := fun j => (sourceZetaPoints t j+α j+(1+(v : ℂ)*I))/2
  let b : Fin 4 → ℂ := fun j => (sourceZetaPoints t j+α j)/2
  let P : ℝ := 2+t+|v|
  have hP : 0 < P := by dsimp [P]; positivity
  have hRe (j : Fin 4) : (a j).re ∈ Icc (1/8 : ℝ) (7/8) ∧
      (b j).re ∈ Icc (1/8 : ℝ) (7/8) := by
    have ha := abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))
    have hre := sourceZetaPoints_re t j
    dsimp [a,b]
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_self, hre, add_zero]
    constructor <;> constructor <;> linarith
  have hIm (j : Fin 4) : 1+|(a j).im| ≤ P ∧ 1+|(b j).im| ≤ P := by
    have ha := (Complex.abs_im_le_norm (α j)).trans (hα j)
    have hp : |(sourceZetaPoints t j).im| = t := by
      fin_cases j <;> simp [sourceZetaPoints, criticalLinePoint, abs_of_nonneg ht]
    have hba := abs_add_le (sourceZetaPoints t j).im (α j).im
    rw [hp] at hba
    have haa := abs_add_le ((sourceZetaPoints t j).im+(α j).im) v
    dsimp [a,b,P]
    simp only [Complex.div_ofNat_im, Complex.add_im, Complex.one_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, add_zero, zero_add, abs_div,
      show |(2 : ℝ)| = 2 by norm_num]
    constructor <;> linarith [abs_nonneg v]
  have hFactor (j : Fin 4) : ‖Gamma (a j)/Gamma (b j)‖ ≤
      (D^2*P^2)*Real.exp (Real.pi*(|(b j).im|-|(a j).im|)/2) := by
    have hn := (hΓ (a j) (hRe j).1).1
    have hd := (hΓ (b j) (hRe j).2).2
    rw [norm_div, div_eq_mul_inv]
    calc
      _ ≤ (D*(1+|(a j).im|)*Real.exp (-(Real.pi*|(a j).im|/2)))*
          (D*(1+|(b j).im|)*Real.exp (Real.pi*|(b j).im|/2)) := by gcongr
      _ ≤ (D*P*Real.exp (-(Real.pi*|(a j).im|/2)))*
          (D*P*Real.exp (Real.pi*|(b j).im|/2)) := by
        gcongr
        · exact (hIm j).1
        · exact (hIm j).2
      _ = _ := by
        rw [show (D*P*Real.exp (-(Real.pi*|(a j).im|/2)))*
            (D*P*Real.exp (Real.pi*|(b j).im|/2)) =
            D^2*P^2*(Real.exp (-(Real.pi*|(a j).im|/2))*
              Real.exp (Real.pi*|(b j).im|/2)) by ring,
          ← Real.exp_add]
        congr 2
        ring
  have hsum : (∑ j : Fin 4, (Real.pi*(|(b j).im|-|(a j).im|)/2)) ≤ Real.pi/2 := by
    have hs := bblr_Gamma_line_abs_sum t v ht α hα
    have he : (∑ j : Fin 4, (Real.pi*(|(b j).im|-|(a j).im|)/2)) =
        (Real.pi/2)*((∑ j : Fin 4, |(b j).im|)-(∑ j : Fin 4, |(a j).im|)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ Real.pi/2)).trans_eq
      (mul_one _)
  have hprod : (∏ j : Fin 4, ‖Gamma (a j)/Gamma (b j)‖) ≤
      ∏ j : Fin 4, (D^2*P^2)*Real.exp (Real.pi*(|(b j).im|-|(a j).im|)/2) := by
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hFactor j)
  change ‖∏ j : Fin 4, Gamma (a j)/Gamma (b j)‖ ≤ _
  rw [norm_prod]
  calc
    _ ≤ _ := hprod
    _ = (D^2*P^2)^4*Real.exp (∑ j : Fin 4, Real.pi*(|(b j).im|-|(a j).im|)/2) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      simp
    _ ≤ (D^2*P^2)^4*Real.exp (Real.pi/2) := by
      gcongr
    _ = (D^8*Real.exp (Real.pi/2))*(2+t+|v|)^8 := by dsimp [P]; ring

end
end SixthMoment.Source
