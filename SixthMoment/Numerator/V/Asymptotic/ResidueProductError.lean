import SixthMoment.Zeta.Bounds.ZetaTripleLaurent


namespace SixthMoment.Source
open Complex Real
noncomputable section
set_option autoImplicit false

theorem norm_triple_product_inverse_scale_error (a b : Fin 3 → ℂ)
    {B E L : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E) (hL : 1 ≤ L)
    (hb : ∀ j, ‖b j‖ ≤ B) (he : ∀ j, ‖a j-b j‖ ≤ E/L) :
    ‖a 0*(a 1*a 2)-b 0*(b 1*b 2)‖ ≤ (3*(B+E)^2*E)/L := by
  have hL0 : 0 < L := by linarith
  have ha (j : Fin 3) : ‖a j‖ ≤ B+E := by
    calc
      _ = ‖(a j-b j)+b j‖ := by rw [sub_add_cancel]
      _ ≤ ‖a j-b j‖+‖b j‖ := norm_add_le _ _
      _ ≤ E/L+B := add_le_add (he j) (hb j)
      _ ≤ B+E := by linarith [div_le_self hE hL]
  have hb' (j : Fin 3) : ‖b j‖ ≤ B+E := (hb j).trans (by linarith)
  exact (norm_triple_product_error a b (add_nonneg hB hE)
    (div_nonneg hE hL0.le) ha hb' he).trans_eq (by ring)

end
end SixthMoment.Source
