import SixthMoment.Arithmetic.Euler.Convolution.Factorization
import SixthMoment.Zeta.Bounds.ZetaTripleLaurent


namespace SixthMoment.Source
open Complex Real NoDPGlobalConvolution
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem prod_reindexed_complement (i : Fin 4) (f : Fin 4 → ℂ) :
    (∏ j : Fin 3, f (Equiv.swap 0 i j.succ)) =
      ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, f j := by
  simpa [Fin.prod_univ_succ] using swap_complement_product i f

theorem riemannZeta_triple_pole_error (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ z : Fin 3 → ℂ,
      (∀ j, δ ≤ ‖z j‖) → (∀ j, ‖z j‖ ≤ L) →
      ‖(∏ j : Fin 3, riemannZeta (1+z j/(L:ℂ)))-
        (L:ℂ)^3*(∏ j : Fin 3, (z j)⁻¹)‖ ≤ C*L^2 := by
  obtain ⟨C,hC,HC⟩ := scaled_riemannZeta_triple_uniform_error δ hδ
  refine ⟨C,hC,?_⟩
  intro L hL z hgap hsize
  have hL0 : 0 < L := by linarith
  have hLC : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL0.ne'
  have H := HC L hL z hgap hsize
  have hscaled : (∏ j : Fin 3, riemannZeta (1+z j/(L:ℂ))/(L:ℂ)) =
      (∏ j : Fin 3, riemannZeta (1+z j/(L:ℂ)))/(L:ℂ)^3 := by
    simp only [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have he : (∏ j : Fin 3, riemannZeta (1+z j/(L:ℂ)))-
        (L:ℂ)^3*(∏ j : Fin 3, (z j)⁻¹) =
      (L:ℂ)^3*((∏ j : Fin 3, riemannZeta (1+z j/(L:ℂ))/(L:ℂ))-
        (∏ j : Fin 3, (z j)⁻¹)) := by
    rw [hscaled,mul_sub]
    have hcancel : (L:ℂ)^3*((∏ j : Fin 3, riemannZeta (1+z j/(L:ℂ)))/(L:ℂ)^3) =
        (∏ j : Fin 3, riemannZeta (1+z j/(L:ℂ))) := by field_simp [hLC]
    rw [hcancel]
  calc
    _ = L^3*‖(∏ j : Fin 3, riemannZeta (1+z j/(L:ℂ))/(L:ℂ))-
        (∏ j : Fin 3, (z j)⁻¹)‖ := by
      rw [he,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
    _ ≤ L^3*(C/L) := mul_le_mul_of_nonneg_left H (by positivity)
    _ = C*L^2 := by
      calc
        _ = (C*L^2)*(L/L) := by ring
        _ = _ := by rw [div_self hL0.ne',mul_one]

theorem residueZeta_complement_uniform_error (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R L : ℝ, 1 ≤ L → 2*R ≤ L →
      ∀ σ : Fin 4 → ℂ, ‖σ‖ ≤ R → ∀ i : Fin 4,
      (∀ j, j ≠ i → δ ≤ ‖σ j-σ i‖) →
      ‖(∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
          riemannZeta (1+(σ j-σ i)/(L:ℂ)))-
        (L:ℂ)^3*(∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, (σ j-σ i)⁻¹)‖ ≤ C*L^2 := by
  obtain ⟨C,hC,HC⟩ := riemannZeta_triple_pole_error δ hδ
  refine ⟨C,hC,?_⟩
  intro R L hL hLR σ hσ i hgap
  let z (j : Fin 3) := σ (Equiv.swap 0 i j.succ)-σ i
  have hneq (j : Fin 3) : Equiv.swap 0 i j.succ ≠ i := by
    intro h
    have H : Equiv.swap 0 i j.succ = Equiv.swap 0 i 0 := h.trans (by simp)
    exact Fin.succ_ne_zero j ((Equiv.swap (0:Fin 4) i).injective H)
  have hz (j : Fin 3) : δ ≤ ‖z j‖ := hgap _ (hneq j)
  have hsize (j : Fin 3) : ‖z j‖ ≤ L := by
    have ha := (norm_le_pi_norm σ (Equiv.swap 0 i j.succ)).trans hσ
    have hb := (norm_le_pi_norm σ i).trans hσ
    exact (norm_sub_le _ _).trans (by linarith)
  have H := HC L hL z hz hsize
  dsimp only [z] at H
  rw [prod_reindexed_complement i (fun j => riemannZeta (1+(σ j-σ i)/(L:ℂ))),
    prod_reindexed_complement i (fun j => (σ j-σ i)⁻¹)] at H
  exact H

end
end SixthMoment.Source
