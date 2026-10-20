import Sechstmoment.Zeta.Bounds.MellinZetaDirichletBounds


namespace Sechstmoment.Source
open Complex Real Set
open scoped BigOperators
noncomputable section

theorem zetaDirichletMajorant_ofReal {b : ℝ} (hb : 1 < b) :
    (zetaDirichletMajorant b:ℂ) = riemannZeta (b:ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hb)]
  unfold zetaDirichletMajorant
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_cpow (Nat.cast_nonneg n) b,
    Complex.ofReal_natCast]

theorem riemannZeta_real_norm {b : ℝ} (hb : 1 < b) :
    ‖riemannZeta (b:ℂ)‖ = zetaDirichletMajorant b := by
  rw [← zetaDirichletMajorant_ofReal hb,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (zetaDirichletMajorant_nonneg b)]

theorem riemannZeta_log_line_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ s : ℂ,
      1+1/L ≤ s.re → ‖riemannZeta s‖ ≤ C*L := by
  have hc : Continuous (fun x : ℝ => polarRegularizedZeta (x:ℂ)) :=
    (show Differentiable ℂ polarRegularizedZeta from polarRegularizedZeta_differentiable).continuous.comp
      Complex.continuous_ofReal
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (1:ℝ) 2) hc.continuousOn
  refine ⟨max 1 B,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro L hL s hs
  have hL0 : 0 < L := by linarith
  let b := 1+1/L
  have hb : 1 < b := by
    dsimp only [b]
    linarith [one_div_pos.mpr hL0]
  have hb2 : b ≤ 2 := by
    have H : 1/L ≤ 1 := (div_le_one hL0).mpr hL
    dsimp [b]
    linarith
  have hbne : (b:ℂ) ≠ 1 := by
    intro h
    have H := congrArg Complex.re h
    simp only [ofReal_re,one_re] at H
    linarith
  have H := hB b ⟨hb.le,hb2⟩
  rw [polarRegularizedZeta_of_ne_one hbne,norm_mul,riemannZeta_real_norm hb] at H
  have hp : ‖(b:ℂ)-1‖ = 1/L := by
    have he : (b:ℂ)-1 = ((1/L:ℝ):ℂ) := by dsimp [b]; push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hL0)]
  rw [hp] at H
  have hmajor : zetaDirichletMajorant b ≤ max 1 B*L := by
    apply (div_le_iff₀ hL0).mp
    calc
      _ = (1/L)*zetaDirichletMajorant b := by ring
      _ ≤ B := H
      _ ≤ _ := le_max_right _ _
  exact (riemannZeta_norm_le_dirichlet hb hs).trans hmajor

end
end Sechstmoment.Source
