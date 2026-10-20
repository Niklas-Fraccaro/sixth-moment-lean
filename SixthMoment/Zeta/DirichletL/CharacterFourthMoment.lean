import SixthMoment.Zeta.Bounds.ZetaPolynomialBound
import SixthMoment.Zeta.DirichletL.FourLProduct


namespace SixthMoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators Classical
noncomputable section

theorem principalDirichlet_fourthMoment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ _ : NeZero N,
      ∀ s : ℂ, s.re ∈ Icc (1/2 : ℝ) (3/4) →
      ‖(1 : DirichletCharacter ℂ N).LFunction s‖^4 ≤
        C*(N : ℝ)^ε*(1+|s.im|)^8 := by
  obtain ⟨A,hA,hEuler⟩ := dirichletL_changeLevel_subpower (ε := ε/4) (by linarith)
  obtain ⟨B,hB,hzeta⟩ := riemannZeta_polynomial_critical_strip
  refine ⟨(A*B)^4,by positivity,?_⟩
  intro N hN s hs
  have : NeZero N := hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h := hEuler N hN 1 inferInstance (one_dvd N) 1 s hs
  simp only [DirichletCharacter.changeLevel_one,DirichletCharacter.LFunction_modOne_eq] at h
  have hp : ((N : ℝ)^(ε/4))^4 = (N : ℝ)^ε := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hNr.le]
    congr 1
    ring
  calc
    _ ≤ (A*(N : ℝ)^(ε/4)*(B*(1+|s.im|)^2))^4 := by
      gcongr
      exact h.trans (by gcongr; exact hzeta s hs)
    _ = _ := by rw [mul_pow,mul_pow,mul_pow,hp]; ring

theorem allDirichlet_fourthMoment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ _ : NeZero N,
      ∀ s : ℂ, s.re ∈ Icc (1/2 : ℝ) (3/4) →
      (∑ χ : DirichletCharacter ℂ N, ‖χ.LFunction s‖^4) ≤
        C*(N : ℝ)^(1+ε)*(1+|s.im|)^20 := by
  obtain ⟨A,hA,hprincipal⟩ := principalDirichlet_fourthMoment hε
  obtain ⟨B,hB,hnonprincipal⟩ := nonprincipalDirichlet_fourthMoment hε
  refine ⟨B+A,by positivity,?_⟩
  intro N hN s hs
  have : NeZero N := hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hpow : (N : ℝ)^ε ≤ (N : ℝ)^(1+ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hheight : (1+|s.im|)^8 ≤ (1+|s.im|)^20 := by
    exact pow_le_pow_right₀ (by linarith [abs_nonneg s.im]) (by norm_num)
  have hsplit : (∑ χ : DirichletCharacter ℂ N, ‖χ.LFunction s‖^4) =
      (∑ χ : DirichletCharacter ℂ N with χ ≠ 1, ‖χ.LFunction s‖^4)+
        ‖(1 : DirichletCharacter ℂ N).LFunction s‖^4 := by
    have h := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun χ : DirichletCharacter ℂ N => χ ≠ 1) (f := fun χ => ‖χ.LFunction s‖^4)
    simpa [Finset.sum_filter] using h.symm
  rw [hsplit]
  calc
    _ ≤ B*(N : ℝ)^(1+ε)*(1+|s.im|)^20+A*(N : ℝ)^ε*(1+|s.im|)^8 :=
      add_le_add (hnonprincipal N hN s hs) (hprincipal N hN s hs)
    _ ≤ B*(N : ℝ)^(1+ε)*(1+|s.im|)^20+A*(N : ℝ)^(1+ε)*(1+|s.im|)^20 := by
      gcongr
    _ = _ := by ring

theorem allDirichlet_fourLProduct {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ _ : NeZero N,
      ∀ s : Fin 4 → ℂ, (∀ j, (s j).re ∈ Icc (1/2 : ℝ) (3/4)) →
      ∀ V : ℝ, 0 ≤ V → (∀ j, |(s j).im| ≤ V) →
      (∑ χ : DirichletCharacter ℂ N, ∏ j : Fin 4, ‖χ.LFunction (s j)‖) ≤
        C*(N : ℝ)^(1+ε)*(1+V)^20 := by
  obtain ⟨C,hC,hbound⟩ := allDirichlet_fourthMoment hε
  refine ⟨C,hC,?_⟩
  intro N hN s hs V hV ht
  have : NeZero N := hN
  have hmean (j : Fin 4) :
      (∑ χ : DirichletCharacter ℂ N, ‖χ.LFunction (s j)‖^4) ≤
        C*(N : ℝ)^(1+ε)*(1+V)^20 :=
    (hbound N hN (s j) (hs j)).trans (by gcongr; exact ht j)
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ N,
        (∑ j : Fin 4, ‖χ.LFunction (s j)‖^4)/4 := by
      apply Finset.sum_le_sum
      intro χ _
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
        (by nlinarith [four_product_le_fourth_powers (fun j => ‖χ.LFunction (s j)‖)])
    _ = (∑ j : Fin 4, ∑ χ : DirichletCharacter ℂ N,
        ‖χ.LFunction (s j)‖^4)/4 := by rw [← Finset.sum_div,Finset.sum_comm]
    _ ≤ (∑ _j : Fin 4, C*(N : ℝ)^(1+ε)*(1+V)^20)/4 := by
      gcongr with j
      exact hmean j
    _ = _ := by simp

end
end SixthMoment.Source
