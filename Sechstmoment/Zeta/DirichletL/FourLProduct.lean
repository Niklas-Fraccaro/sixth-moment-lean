import Sechstmoment.Zeta.DirichletL.ImprimitiveFourthMoment


namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators Classical
noncomputable section

theorem four_product_le_fourth_powers (a : Fin 4 → ℝ) :
    4*(∏ j : Fin 4, a j) ≤ ∑ j : Fin 4, (a j)^4 := by
  simp only [Fin.prod_univ_four,Fin.sum_univ_four]
  nlinarith [sq_nonneg ((a 0)^2-(a 1)^2),sq_nonneg ((a 2)^2-(a 3)^2),
    sq_nonneg (a 0*a 1-a 2*a 3)]

theorem nonprincipalDirichlet_fourLProduct {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ _ : NeZero N,
      ∀ s : Fin 4 → ℂ, (∀ j, (s j).re ∈ Icc (1/2 : ℝ) (3/4)) →
      ∀ V : ℝ, 0 ≤ V → (∀ j, |(s j).im| ≤ V) →
      (∑ χ : DirichletCharacter ℂ N with χ ≠ 1,
        ∏ j : Fin 4, ‖χ.LFunction (s j)‖) ≤
        C*(N : ℝ)^(1+ε)*(1+V)^20 := by
  obtain ⟨C,hC,hbound⟩ := nonprincipalDirichlet_fourthMoment hε
  refine ⟨C,hC,?_⟩
  intro N hN s hs V hV ht
  have : NeZero N := hN
  have hmean (j : Fin 4) :
      (∑ χ : DirichletCharacter ℂ N with χ ≠ 1, ‖χ.LFunction (s j)‖^4) ≤
        C*(N : ℝ)^(1+ε)*(1+V)^20 :=
    (hbound N hN (s j) (hs j)).trans (by gcongr; exact ht j)
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ N with χ ≠ 1,
        (∑ j : Fin 4, ‖χ.LFunction (s j)‖^4)/4 := by
      apply Finset.sum_le_sum
      intro χ _
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
        (by nlinarith [four_product_le_fourth_powers (fun j => ‖χ.LFunction (s j)‖)])
    _ = (∑ j : Fin 4, ∑ χ : DirichletCharacter ℂ N with χ ≠ 1,
        ‖χ.LFunction (s j)‖^4)/4 := by rw [← Finset.sum_div,Finset.sum_comm]
    _ ≤ (∑ _j : Fin 4, C*(N : ℝ)^(1+ε)*(1+V)^20)/4 := by gcongr with j; exact hmean j
    _ = _ := by simp

end
end Sechstmoment.Source
