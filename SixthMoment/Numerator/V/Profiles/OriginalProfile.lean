import SixthMoment.Arithmetic.QuadraticDivisor.Definitions
import SixthMoment.Numerator.V.Profiles.ConvolutionLimit
import SixthMoment.Numerator.V.Profiles.WeightedReindex


namespace SixthMoment.Source.NoDPHarmonic
open Real Complex Set Polynomial NoDPGlobalConvolution NoDPGlobalRest
open scoped BigOperators
noncomputable section

def originalProfileSum (η L : ℝ) (i : Fin 4) (s : Fin 4 → ℂ)
    (P Q : ℝ[X]) : ℂ :=
  ∑ a ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
    ∑ b ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
      originalCoeffAt i s a b*profileWeight η L P a*profileWeight η L Q b

theorem sourceTripleSum_eq_tripleCoeff {η L : ℝ} (hL : 0 < L)
    (i : Fin 4) (σ : Fin 4 → ℂ) (P : ℝ[X]) {d : ℕ} (hd : 1 ≤ d) :
    sourceTripleSum η L P (residueShifts i σ 0) (residueShifts i σ 1)
        (residueShifts i σ 2) d =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
        tripleCoeffAt i (scaledShifts L σ) n*profileWeight η L P (d*n) := by
  symm
  unfold tripleCoeffAt
  rw [sum_weighted_triple _ _ _ (fun n hn => profileWeight_mul_zero_of_lt hL P hd hn)]
  unfold sourceTripleSum
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  have ha0 : a ≠ 0 := by have := (Finset.mem_Icc.mp ha).1; omega
  have hb0 : b ≠ 0 := by have := (Finset.mem_Icc.mp hb).1; omega
  have hc0 : c ≠ 0 := by have := (Finset.mem_Icc.mp hc).1; omega
  have hd0 : d ≠ 0 := by omega
  rw [powerAF_apply _ _ ha0,powerAF_apply _ _ hb0,powerAF_apply _ _ hc0]
  have logmul (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) :
      Real.log (x*y : ℕ) = Real.log x+Real.log y := by
    rw [Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr hx) (Nat.cast_ne_zero.mpr hy)]
  have hlog : Real.log (d*(a*b*c) : ℕ) =
      Real.log d+Real.log a+Real.log b+Real.log c := by
    rw [logmul d (a*b*c) hd0 (mul_ne_zero (mul_ne_zero ha0 hb0) hc0),
      logmul (a*b) c (mul_ne_zero ha0 hb0) hc0,logmul a b ha0 hb0]
    ring
  simp only [profileWeight,hlog]
  rfl

theorem tripleCoeff_profile_zero_of_lt {η L : ℝ} (hL : 0 < L)
    (i : Fin 4) (s : Fin 4 → ℂ) (P : ℝ[X]) {d : ℕ}
    (hd : ⌊Real.exp (L*η)⌋₊ < d) :
    (∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
      tripleCoeffAt i s n*profileWeight η L P (d*n)) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  rw [profileWeight_zero_of_lt hL P (hd.trans_le (Nat.le_mul_of_pos_right d hn1)),mul_zero]

theorem originalProfileSum_finite_convolution {η L ρ : ℝ}
    (hL : 0 < L) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4)
    (i : Fin 4) (s : Fin 4 → ℂ) (hs : ∀ j, ‖s j‖ ≤ ρ) (P Q : ℝ[X]) :
    originalProfileSum η L i s P Q =
      ∑ d ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
        ∑ e ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊, gammaAt i s (d,e)*
          ((∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
              tripleCoeffAt i s n*profileWeight η L P (d*n))*
            (∑ m ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
              tripleCoeffAt i s m*profileWeight η L Q (e*m))) := by
  let N := ⌊Real.exp (L*η)⌋₊
  let F := fun d n e m : ℕ => gammaAt i s (d,e)*tripleCoeffAt i s n*
    tripleCoeffAt i s m*profileWeight η L P (d*n)*profileWeight η L Q (e*m)
  have hid (a b : ℕ) :
      originalCoeffAt i s a b*profileWeight η L P a*profileWeight η L Q b =
        ∑ d ∈ a.divisors, ∑ e ∈ b.divisors, F d (a/d) e (b/e) := by
    rw [originalCoeffAt_convolution i s ρ hρ0 hρ hs a b]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    dsimp only [F]
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd),
      Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)]
  have hcut₁ : ∀ d n e m, N < d*n → F d n e m = 0 := by
    intro d n e m h
    dsimp only [F]
    rw [profileWeight_zero_of_lt hL P h,mul_zero,zero_mul]
  have hcut₂ : ∀ d n e m, N < e*m → F d n e m = 0 := by
    intro d n e m h
    dsimp only [F]
    rw [profileWeight_zero_of_lt hL Q h,mul_zero]
  unfold originalProfileSum
  simp_rw [hid]
  rw [sum_bivariate_divisors_reindex N F hcut₁ hcut₂]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  dsimp only [F]
  ring

theorem sourceTripleSum_zero_of_lt {η L : ℝ} (hL : 0 < L)
    (i : Fin 4) (σ : Fin 4 → ℂ) (P : ℝ[X]) {d : ℕ}
    (hd : ⌊Real.exp (L*η)⌋₊ < d) :
    sourceTripleSum η L P (residueShifts i σ 0) (residueShifts i σ 1)
      (residueShifts i σ 2) d = 0 := by
  rw [sourceTripleSum_eq_tripleCoeff hL i σ P (by omega)]
  exact tripleCoeff_profile_zero_of_lt hL i (scaledShifts L σ) P hd

theorem originalProfileSum_eq_sourceGammaProfileSum {η L ρ : ℝ}
    (hL : 0 < L) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4)
    (i : Fin 4) (σ : Fin 4 → ℂ) (hs : ∀ j, ‖scaledShifts L σ j‖ ≤ ρ)
    (P Q : ℝ[X]) :
    originalProfileSum η L i (scaledShifts L σ) P Q =
      sourceGammaProfileSum η L i (scaledShifts L σ)
        (residueShifts i σ) (residueShifts i σ) P Q := by
  rw [originalProfileSum_finite_convolution hL hρ0 hρ i _ hs P Q]
  symm
  unfold sourceGammaProfileSum
  let S := Finset.Icc 1 ⌊Real.exp (L*η)⌋₊
  rw [tsum_eq_sum (s := S ×ˢ S)]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    rw [sourceTripleSum_eq_tripleCoeff hL i σ P (Finset.mem_Icc.mp hd).1,
      sourceTripleSum_eq_tripleCoeff hL i σ Q (Finset.mem_Icc.mp he).1]
  · rintro ⟨d,e⟩ hnot
    by_cases hd : d = 0
    · subst d
      simp only [gammaAt,gamma_zero_left,zero_mul]
    by_cases he : e = 0
    · subst e
      simp only [gammaAt,gamma_zero_right,zero_mul]
    have hout : ⌊Real.exp (L*η)⌋₊ < d ∨ ⌊Real.exp (L*η)⌋₊ < e := by
      simp only [Finset.mem_product,Finset.mem_Icc,S] at hnot
      omega
    rcases hout with hout | hout
    · rw [sourceTripleSum_zero_of_lt hL i σ P hout,zero_mul,mul_zero]
    · rw [sourceTripleSum_zero_of_lt hL i σ Q hout,mul_zero,mul_zero]

theorem original_polynomial_profile_asymptotic {η R ρ : ℝ}
    (hη : 0 < η) (hR : 0 ≤ R) (hρ0 : 0 < ρ) (hρ : ρ < 1/4) (P Q : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → 2*R ≤ ρ*L →
      ∀ i : Fin 4, ∀ σ : Fin 4 → ℂ, ‖σ‖ ≤ R →
      let ν := residueShifts i σ
      ‖originalProfileSum η L i (scaledShifts L σ) P Q -
        arithmeticConstant*((η*L:ℝ):ℂ)^6*
          (dpNormalizedTriple η P (ν 0) (-(ν 1)) (-(ν 2))*
            dpNormalizedTriple η Q (ν 0) (-(ν 1)) (-(ν 2)))‖ ≤ C*L^5 := by
  obtain ⟨C,hC,H⟩ := source_polynomial_gamma_normalized_asymptotic hη hR hρ0 hρ P Q
  refine ⟨C,hC,?_⟩
  intro L hL hLR i σ hσ
  have hL0 : 0 < L := by linarith
  have hs : ∀ j, ‖scaledShifts L σ j‖ ≤ ρ := by
    intro j
    apply (norm_le_pi_norm _ j).trans ((scaledShifts_norm hL0 hσ).trans ?_)
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  rw [originalProfileSum_eq_sourceGammaProfileSum hL0 hρ0.le hρ i σ hs P Q]
  exact H L hL hLR i σ hσ

end
end SixthMoment.Source.NoDPHarmonic
