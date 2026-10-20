import Mathlib.Tactic
import Sechstmoment.Zeta.Bounds.MellinZetaDirichletBounds
import Sechstmoment.Zeta.Bounds.MellinZetaGrowth


namespace Sechstmoment

open Real Complex
open scoped Topology

noncomputable section

theorem riemannZeta_norm_le_exp_halfPlane {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → r ≤ ‖1-s‖ →
      ‖riemannZeta s‖ ≤ C*Real.exp (Real.pi*|s.im|/2) := by
  obtain ⟨K, hK0, hK⟩ := riemannZeta_norm_le_exp_strip (a := a) (b := 3/2) ha
    (by norm_num) hr
  let Z := zetaDirichletMajorant (3/2)
  have hZ0 : 0 ≤ Z := zetaDirichletMajorant_nonneg _
  refine ⟨max K Z, hK0.trans (le_max_left _ _), ?_⟩
  intro s hs hsep
  by_cases hs1 : s.re ≤ 3/2
  · exact (hK s hs hs1 hsep).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have he : 1 ≤ Real.exp (Real.pi*|s.im|/2) := Real.one_le_exp (by positivity)
    calc
      _ ≤ Z := riemannZeta_norm_le_dirichlet (by norm_num : (1:ℝ) < 3/2)
        (le_of_not_ge hs1)
      _ ≤ Z*Real.exp (Real.pi*|s.im|/2) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

end

end Sechstmoment
