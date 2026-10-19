import Sechstmoment.Numerator.V.Arithmetic.ProfileContourBounds
import Sechstmoment.Zeta.Bounds.ZetaPolynomialBound

/-! The literal unweighted holomorphic integrand in Section 4.1. All
zeta/chi growth estimates below concern the actual functions and are proved.
-/

namespace Sechstmoment.Source
open Complex Real Set
open scoped Topology BigOperators
noncomputable section

def sameSideZetaFactor (α : Fin 4 → ℂ) (s : ℂ) : ℂ :=
  zetaChi (1-s)*(∏ j : Fin 4, riemannZeta (s+α j))

def sameSideProfileFactor (T : ℝ) (α : Fin 4 → ℂ) (f g : ℝ → ℝ) (s : ℂ) : ℂ :=
  sameSideZetaFactor α s*profileDirichletSum T f (1-s)*profileDirichletSum T g (1-s)

theorem sameSide_shift_geometry {s α : ℂ} (hs : s.re ∈ Icc (1/2 : ℝ) (5/4))
    (ht : 40 ≤ |s.im|) (hα : ‖α‖ ≤ 1/8) :
    (s+α).re ∈ Icc (-1/2 : ℝ) (3/2) ∧ 1 ≤ |(s+α).im| ∧
      1+|(s+α).im| ≤ 2*(1+|s.im|) := by
  have hRe := abs_le.mp ((Complex.abs_re_le_norm α).trans hα)
  have hIm := (Complex.abs_im_le_norm α).trans hα
  have htri := abs_add_le (s.im+α.im) (-α.im)
  rw [add_neg_cancel_right,abs_neg] at htri
  have hup := abs_add_le s.im α.im
  simp only [add_re,add_im]
  refine ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,by linarith,?_⟩
  linarith [abs_nonneg s.im]

theorem sameSideZetaFactor_differentiableAt {s : ℂ} (α : Fin 4 → ℂ)
    (hs : s.re ∈ Icc (1/2 : ℝ) (5/4)) (ht : 40 ≤ |s.im|)
    (hα : ∀ j, ‖α j‖ ≤ 1/8) : DifferentiableAt ℂ (sameSideZetaFactor α) s := by
  have hi : s.im ≠ 0 := by intro h; norm_num [h] at ht
  apply (zetaChi_one_sub_differentiableAt_nonreal hi).mul
  apply DifferentiableAt.fun_finsetProd
  intro j _
  have hj := (sameSide_shift_geometry hs ht (hα j)).2.1
  have hne : s+α j ≠ 1 := by intro h; norm_num [h] at hj
  exact (differentiableAt_riemannZeta hne).comp s (differentiableAt_id.add_const _)

theorem sameSideZetaFactor_polynomial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ α : Fin 4 → ℂ, (∀ j, ‖α j‖ ≤ 1/8) →
      ∀ s : ℂ, s.re ∈ Icc (1/2 : ℝ) (5/4) → 40 ≤ |s.im| →
      ‖sameSideZetaFactor α s‖ ≤ C*(1+|s.im|)^12 := by
  obtain ⟨A,hA,hzeta⟩ := riemannZeta_polynomial_crossing_strip
  obtain ⟨B,hB,hchi⟩ := zetaChi_one_sub_polynomial_bound
  refine ⟨B*(4*A)^4,by positivity,?_⟩
  intro α hα s hs ht
  have hpoint (j : Fin 4) : ‖riemannZeta (s+α j)‖ ≤ 4*A*(1+|s.im|)^2 := by
    obtain ⟨hr,hi,hh⟩ := sameSide_shift_geometry hs ht (hα j)
    calc
      _ ≤ A*(1+|(s+α j).im|)^2 := hzeta _ hr hi
      _ ≤ A*(2*(1+|s.im|))^2 := by gcongr
      _ = _ := by ring
  have hprod : (∏ j : Fin 4, ‖riemannZeta (s+α j)‖) ≤ (4*A)^4*(1+|s.im|)^8 := by
    calc
      _ ≤ ∏ _j : Fin 4, 4*A*(1+|s.im|)^2 :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hpoint j)
      _ = _ := by simp; ring
  rw [sameSideZetaFactor,norm_mul,norm_prod]
  calc
    _ ≤ (B*(1+|s.im|)^4)*((4*A)^4*(1+|s.im|)^8) :=
      mul_le_mul (hchi s ⟨hs.1,by linarith [hs.2]⟩ ht) hprod
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = _ := by ring

theorem sameSideProfileFactor_differentiableAt {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g : ℝ → ℝ) (hf : ∀ x, a < x → f x = 0) (hg : ∀ x, b < x → g x = 0)
    {s : ℂ} (α : Fin 4 → ℂ) (hs : s.re ∈ Icc (1/2 : ℝ) (5/4))
    (ht : 40 ≤ |s.im|) (hα : ∀ j, ‖α j‖ ≤ 1/8) :
    DifferentiableAt ℂ (sameSideProfileFactor T α f g) s := by
  have hsub : DifferentiableAt ℂ (fun z : ℂ => 1-z) s := by fun_prop
  exact ((sameSideZetaFactor_differentiableAt α hs ht hα).mul
    ((profileDirichletSum_entire_of_supported hT a f hf (1-s)).comp s hsub)).mul
    ((profileDirichletSum_entire_of_supported hT b g hg (1-s)).comp s hsub)

theorem sameSideProfileFactor_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 < T → ∀ a b : ℝ, ∀ f g : ℝ → ℝ,
      (∀ x, a < x → f x = 0) → (∀ x, b < x → g x = 0) →
      ∀ α : Fin 4 → ℂ, (∀ j, ‖α j‖ ≤ 1/8) →
      ∀ s : ℂ, s.re ∈ Icc (1/2 : ℝ) (5/4) → 40 ≤ |s.im| →
      ‖sameSideProfileFactor T α f g s‖ ≤
        C*(1+|s.im|)^12*profileContourMass T a f*profileContourMass T b g := by
  obtain ⟨C,hC,hbound⟩ := sameSideZetaFactor_polynomial_bound
  refine ⟨C,hC,?_⟩
  intro T hT a b f g hf hg α hα s hs ht
  rw [sameSideProfileFactor,norm_mul,norm_mul]
  exact mul_le_mul
    (mul_le_mul (hbound α hα s hs ht)
      (profileDirichletSum_one_sub_norm_le_mass hT a f hf (by linarith [hs.2]))
      (norm_nonneg _) (by positivity))
    (profileDirichletSum_one_sub_norm_le_mass hT b g hg (by linarith [hs.2]))
    (norm_nonneg _) (mul_nonneg (by positivity) (profileContourMass_nonneg T a f))

end
end Sechstmoment.Source
