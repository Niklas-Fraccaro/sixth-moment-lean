import SixthMoment.Zeta.Bounds.ZetaStripGrowth


namespace SixthMoment.Source
open Complex Real Set
noncomputable section

theorem gammaR_inv_exponential_positive_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1/2:ℝ) (5/2) → 1 ≤ |s.im| →
      ‖(Complex.Gammaℝ s)⁻¹‖ ≤ C*Real.exp (Real.pi*|s.im|/2) := by
  obtain ⟨B,hB,HB⟩ := realGamma_norm_bounded_on_positive_interval
    (a := 3/4) (b := 7/4) (by norm_num)
  refine ⟨2*(B+1)*Real.pi,by positivity,?_⟩
  intro s hs ht
  have hi : s.im ≠ 0 := by intro he; simp only [he,abs_zero] at ht; linarith
  have hz : s/2-1 ≠ 0 := by
    intro he
    have H := congrArg Complex.im he
    simp only [sub_im,Complex.div_ofNat_im,one_im,zero_im,sub_zero] at H
    exact hi (by linarith)
  have hden : 1/2 ≤ ‖s/2-1‖ := by
    have H := Complex.abs_im_le_norm (s/2-1)
    simp only [sub_im,Complex.div_ofNat_im,one_im,sub_zero,abs_div] at H
    norm_num at H
    linarith
  have hΓ : ‖(Complex.Gamma (s/2-1))⁻¹‖ ≤
      B*Real.exp (Real.pi*|s.im|/2)/Real.pi := by
    have H := gamma_inv_norm_le_exp_nonreal (z := s/2-1)
      (by simpa only [sub_im,Complex.div_ofNat_im,one_im,sub_zero] using
        (div_ne_zero hi (by norm_num : (2:ℝ) ≠ 0)))
      (by simp only [sub_re,Complex.div_ofNat_re,one_re]; linarith [hs.2])
    have HB' := HB (1-(s/2-1).re) (by
      simp only [sub_re,Complex.div_ofNat_re,one_re]
      constructor <;> linarith [hs.1,hs.2])
    have him : Real.pi*|(s/2-1).im| = Real.pi*|s.im|/2 := by
      simp only [sub_im,Complex.div_ofNat_im,one_im,sub_zero,abs_div]
      norm_num
      ring
    rw [him] at H
    exact H.trans (by gcongr)
  have hΓ' : ‖(Complex.Gamma (s/2))⁻¹‖ ≤
      2*B*Real.exp (Real.pi*|s.im|/2)/Real.pi := by
    rw [show s/2 = (s/2-1)+1 by ring,Complex.Gamma_add_one _ hz,
      mul_inv_rev,norm_mul]
    have hrec : ‖(s/2-1)⁻¹‖ ≤ 1/(1/2:ℝ) := by
      simpa only [norm_inv,one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/2) hden)
    calc
      _ ≤ (B*Real.exp (Real.pi*|s.im|/2)/Real.pi)*(1/(1/2)) := by
        exact mul_le_mul hΓ hrec
          (by positivity) (by positivity)
      _ = _ := by ring
  have hπ : ‖((Real.pi:ℂ)^(-s/2))⁻¹‖ ≤ Real.pi^2 := by
    rw [← Complex.cpow_neg,show -(-s/2) = s/2 by ring,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,Complex.div_ofNat_re]
    exact (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Real.two_le_pi] : 1 ≤ Real.pi)
      (show s.re/2 ≤ (2:ℝ) by linarith [hs.2])).trans_eq (by norm_num)
  rw [Complex.Gammaℝ_def,mul_inv_rev,norm_mul]
  calc
    _ ≤ (2*B*Real.exp (Real.pi*|s.im|/2)/Real.pi)*Real.pi^2 := by gcongr
    _ = (2*B*Real.pi)*Real.exp (Real.pi*|s.im|/2) := by field_simp
    _ ≤ _ := by gcongr; linarith

theorem nonprincipalDirichlet_exponential_strip {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1/2:ℝ) (3/2) → 1 ≤ |s.im| →
      ‖χ.LFunction s‖ ≤ C*Real.exp (Real.pi*|s.im|/2) := by
  classical
  obtain ⟨A,hA,HA⟩ := completedDirichletL_strip_bound χ hχ (1/2) (3/2)
  obtain ⟨B,hB,HB⟩ := gammaR_inv_exponential_positive_strip
  refine ⟨(A+1)*B,by positivity,?_⟩
  intro s hs ht
  have hs0 : s ≠ 0 := by intro he; simp only [he,zero_re] at hs; linarith [hs.1]
  have hgamma : ‖(χ.gammaFactor s)⁻¹‖ ≤ B*Real.exp (Real.pi*|s.im|/2) := by
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact HB s ⟨hs.1,by linarith [hs.2]⟩ ht
    · simpa only [add_im,one_im,add_zero] using
        HB (s+1) (by simp only [add_re,one_re]; constructor <;> linarith [hs.1,hs.2])
          (by simpa only [add_im,one_im,add_zero] using ht)
  rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inl hs0),div_eq_mul_inv,norm_mul]
  calc
    _ ≤ A*(B*Real.exp (Real.pi*|s.im|/2)) :=
      mul_le_mul (HA s hs.1 hs.2) hgamma (norm_nonneg _) hA
    _ ≤ (A+1)*(B*Real.exp (Real.pi*|s.im|/2)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

theorem dirichletL_norm_le_dirichlet {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} {b : ℝ} (hb : 1 < b) (hs : b ≤ s.re) :
    ‖χ.LFunction s‖ ≤ zetaDirichletMajorant b := by
  rw [χ.LFunction_eq_LSeries (hb.trans_le hs)]
  apply tsum_of_norm_bounded (Real.summable_one_div_nat_rpow.mpr hb).hasSum
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero,norm_zero]
    positivity
  · have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.norm_term_eq,ite_eq_right hn]
    calc
      _ ≤ 1/(n:ℝ)^s.re := div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
      _ ≤ _ := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hnpos b)
        (Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hs)

end
end SixthMoment.Source
