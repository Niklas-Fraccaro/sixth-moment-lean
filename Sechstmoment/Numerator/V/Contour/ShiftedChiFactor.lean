import Sechstmoment.Numerator.V.Chi.ShiftedIntegrability
import Sechstmoment.Numerator.V.Contour.SameSideFactor


namespace Sechstmoment.Source
open Complex Real Set
open scoped BigOperators
noncomputable section

def shiftedChiZetaFactor (u : ℂ) (β : Fin 4 → ℂ) (s : ℂ) : ℂ :=
  zetaChi (1-s+u)*(∏ j : Fin 4, riemannZeta (s+β j))

def shiftedChiProfileFactor (T : ℝ) (u : ℂ) (β : Fin 4 → ℂ)
    (f g : ℝ → ℝ) (s : ℂ) : ℂ :=
  shiftedChiZetaFactor u β s*profileDirichletSum T f (1-s)*profileDirichletSum T g (1-s)

theorem shifted_chi_differentiableAt {u s : ℂ} (ht : s.im-u.im ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => zetaChi (1-z+u)) s := by
  have he : (fun z : ℂ => zetaChi (1-z+u)) = fun z : ℂ => zetaChi (1-(z-u)) := by
    funext z
    congr 1
    ring
  rw [he]
  exact (zetaChi_one_sub_differentiableAt_nonreal
    (by simpa only [sub_im] using ht)).comp s (differentiableAt_id.sub_const u)

theorem shiftedChiZetaFactor_differentiableAt {s u : ℂ} (β : Fin 4 → ℂ)
    (ht : 40 ≤ |s.im|) (hu : ‖u‖ ≤ 1/8) (hβ : ∀ j, ‖β j‖ ≤ 1/8) :
    DifferentiableAt ℂ (shiftedChiZetaFactor u β) s := by
  have him := (Complex.abs_im_le_norm u).trans hu
  have hne : s.im-u.im ≠ 0 := by
    intro h
    have he : s.im = u.im := sub_eq_zero.mp h
    rw [he] at ht
    linarith
  apply (shifted_chi_differentiableAt hne).mul
  apply DifferentiableAt.fun_finsetProd
  intro j _
  have hb := (Complex.abs_im_le_norm (β j)).trans (hβ j)
  have harg : s+β j ≠ 1 := by
    intro h
    have hi : s.im+(β j).im = 0 := by simpa only [add_im,one_im] using congrArg Complex.im h
    have he : |s.im| = |(β j).im| := by rw [show s.im = -(β j).im by linarith,abs_neg]
    linarith
  exact (differentiableAt_riemannZeta harg).comp s (differentiableAt_id.add_const _)

theorem shiftedChiZetaFactor_polynomial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, ‖u‖ ≤ 1/8 → ∀ β : Fin 4 → ℂ,
      (∀ j, ‖β j‖ ≤ 1/8) → ∀ s : ℂ,
      s.re ∈ Icc (1/2:ℝ) (5/4) → 40 ≤ |s.im| →
      ‖shiftedChiZetaFactor u β s‖ ≤ C*(1+|s.im|)^12 := by
  obtain ⟨A,hA,hzeta⟩ := riemannZeta_polynomial_crossing_strip
  obtain ⟨D,hD,hchi⟩ := chi_positive_strip_global_polynomial_bound
  refine ⟨4*D*(4*A)^4,by positivity,?_⟩
  intro u hu β hβ s hs ht
  let W := 1+|s.im|
  have hW : 1 ≤ W := by dsimp only [W]; linarith [abs_nonneg s.im]
  have huRe := abs_le.mp ((Complex.abs_re_le_norm u).trans hu)
  have huIm := (Complex.abs_im_le_norm u).trans hu
  have hsr : (s-u).re ∈ Icc (1/8:ℝ) (15/8) := by
    simp only [sub_re]
    constructor <;> linarith [hs.1,hs.2,huRe.1,huRe.2]
  have hsi : (s-u).im ≠ 0 := by
    simp only [sub_im]
    intro h
    have he : s.im = u.im := sub_eq_zero.mp h
    rw [he] at ht
    linarith
  have hchi' : ‖zetaChi (1-s+u)‖ ≤ 4*D*W^2 := by
    have H := hchi (s-u).re hsr (s-u).im hsi
    rw [(s-u).re_add_im] at H
    rw [show 1-s+u = 1-(s-u) by ring]
    have hheight : 1+|(s-u).im| ≤ 2*W := by
      rw [sub_im]
      have Habs : |s.im-u.im| ≤ |s.im|+|u.im| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le s.im (-u.im)
      dsimp only [W]
      linarith [abs_nonneg s.im]
    calc
      _ ≤ D*(1+|(s-u).im|)^2 := H
      _ ≤ D*(2*W)^2 := by gcongr
      _ = _ := by ring
  have hprod : (∏ j : Fin 4, ‖riemannZeta (s+β j)‖) ≤ (4*A)^4*W^8 := by
    calc
      _ ≤ ∏ _j : Fin 4, 4*A*W^2 := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro j _
        obtain ⟨hr,hi,hh⟩ := sameSide_shift_geometry hs ht (hβ j)
        calc
          _ ≤ A*(1+|(s+β j).im|)^2 := hzeta _ hr hi
          _ ≤ A*(2*W)^2 := by gcongr
          _ = _ := by ring
      _ = _ := by simp; ring
  rw [shiftedChiZetaFactor,norm_mul,norm_prod]
  calc
    _ ≤ (4*D*W^2)*((4*A)^4*W^8) :=
      mul_le_mul hchi' hprod (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = (4*D*(4*A)^4)*W^10 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hW (by norm_num : (10:ℕ) ≤ 12)) (by positivity)

theorem shiftedChiProfileFactor_differentiableAt {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g : ℝ → ℝ) (hf : ∀ x, a < x → f x = 0) (hg : ∀ x, b < x → g x = 0)
    {s u : ℂ} (β : Fin 4 → ℂ) (ht : 40 ≤ |s.im|)
    (hu : ‖u‖ ≤ 1/8) (hβ : ∀ j, ‖β j‖ ≤ 1/8) :
    DifferentiableAt ℂ (shiftedChiProfileFactor T u β f g) s := by
  have hsub : DifferentiableAt ℂ (fun z : ℂ => 1-z) s := by fun_prop
  exact ((shiftedChiZetaFactor_differentiableAt β ht hu hβ).mul
    ((profileDirichletSum_entire_of_supported hT a f hf (1-s)).comp s hsub)).mul
    ((profileDirichletSum_entire_of_supported hT b g hg (1-s)).comp s hsub)

theorem shiftedChiProfileFactor_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 < T → ∀ a b : ℝ, ∀ f g : ℝ → ℝ,
      (∀ x, a < x → f x = 0) → (∀ x, b < x → g x = 0) →
      ∀ u : ℂ, ‖u‖ ≤ 1/8 → ∀ β : Fin 4 → ℂ, (∀ j, ‖β j‖ ≤ 1/8) →
      ∀ s : ℂ, s.re ∈ Icc (1/2:ℝ) (5/4) → 40 ≤ |s.im| →
      ‖shiftedChiProfileFactor T u β f g s‖ ≤
        C*(1+|s.im|)^12*profileContourMass T a f*profileContourMass T b g := by
  obtain ⟨C,hC,hbound⟩ := shiftedChiZetaFactor_polynomial_bound
  refine ⟨C,hC,?_⟩
  intro T hT a b f g hf hg u hu β hβ s hs ht
  rw [shiftedChiProfileFactor,norm_mul,norm_mul]
  exact mul_le_mul
    (mul_le_mul (hbound u hu β hβ s hs ht)
      (profileDirichletSum_one_sub_norm_le_mass hT a f hf (by linarith [hs.2]))
      (norm_nonneg _) (by positivity))
    (profileDirichletSum_one_sub_norm_le_mass hT b g hg (by linarith [hs.2]))
    (norm_nonneg _) (mul_nonneg (by positivity) (profileContourMass_nonneg T a f))

end
end Sechstmoment.Source
