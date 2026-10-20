import SixthMoment.Zeta.Bounds.ZetaLaurent


namespace SixthMoment.Source
open Complex Real
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem norm_triple_product_error (a b : Fin 3 → ℂ) {B E : ℝ}
    (hB : 0 ≤ B) (hE : 0 ≤ E) (ha : ∀ j, ‖a j‖ ≤ B)
    (hb : ∀ j, ‖b j‖ ≤ B) (he : ∀ j, ‖a j-b j‖ ≤ E) :
    ‖a 0*(a 1*a 2)-b 0*(b 1*b 2)‖ ≤ 3*B^2*E := by
  have hid : a 0*(a 1*a 2)-b 0*(b 1*b 2) =
      (a 0-b 0)*(a 1*a 2)+b 0*((a 1-b 1)*a 2)+b 0*(b 1*(a 2-b 2)) := by ring
  rw [hid]
  calc
    _ ≤ ‖(a 0-b 0)*(a 1*a 2)‖+‖b 0*((a 1-b 1)*a 2)‖+
        ‖b 0*(b 1*(a 2-b 2))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ E*(B*B)+B*(E*B)+B*(B*E) := by
      simp only [norm_mul]
      gcongr <;> first | exact ha _ | exact hb _ | exact he _
    _ = _ := by ring

theorem scaled_riemannZeta_triple_uniform_error (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ z : Fin 3 → ℂ,
      (∀ j, δ ≤ ‖z j‖) → (∀ j, ‖z j‖ ≤ L) →
      ‖(∏ j : Fin 3, riemannZeta (1+z j/(L:ℂ))/(L:ℂ))-
        (∏ j : Fin 3, (z j)⁻¹)‖ ≤ C/L := by
  obtain ⟨A,hA,HA⟩ := scaled_riemannZeta_uniform_error
  let B := 1/δ+A
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨3*B^2*A,by positivity,?_⟩
  intro L hL z hgap hsize
  have hL0 : 0 < L := by linarith
  let a (j : Fin 3) := riemannZeta (1+z j/(L:ℂ))/(L:ℂ)
  let b (j : Fin 3) := (z j)⁻¹
  have hz (j : Fin 3) : z j ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hgap j))
  have he (j : Fin 3) : ‖a j-b j‖ ≤ A/L := by
    simpa only [one_div] using HA L hL (z j) (hz j) (hsize j)
  have hbinv (j : Fin 3) : ‖b j‖ ≤ 1/δ := by
    dsimp only [b]
    rw [norm_inv,← one_div]
    exact one_div_le_one_div_of_le hδ (hgap j)
  have hb (j : Fin 3) : ‖b j‖ ≤ B := (hbinv j).trans (by dsimp only [B]; linarith)
  have ha (j : Fin 3) : ‖a j‖ ≤ B := by
    calc
      _ = ‖(a j-b j)+b j‖ := by rw [sub_add_cancel]
      _ ≤ ‖a j-b j‖+‖b j‖ := norm_add_le _ _
      _ ≤ A/L+1/δ := add_le_add (he j) (hbinv j)
      _ ≤ B := by dsimp only [B]; linarith [div_le_self hA.le hL]
  have H := norm_triple_product_error a b hB.le (div_nonneg hA.le hL0.le) ha hb he
  have Hprod : ‖(∏ j : Fin 3, a j)-(∏ j : Fin 3, b j)‖ ≤ 3*B^2*(A/L) := by
    simpa [Fin.prod_univ_succ] using H
  exact Hprod.trans_eq (by ring)

end
end SixthMoment.Source
