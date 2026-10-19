import Mathlib.Tactic
import Sechstmoment.Numerator.Polar.Mellin.Holomorphic
import Sechstmoment.Numerator.Polar.RemainderMajorant

/-!
# The weighted sides of the literal Mellin contour

The actual factor `1/z * x^(2z)` is retained. Its horizontal bound follows
from the exact positive-real complex-power norm, and the right line is
absolutely integrable by the true Dirichlet-series bounds for all nine zeta
factors and the actual Gaussian pole killer.
-/

namespace Sechstmoment

open Real Complex MeasureTheory Filter Set
open scoped BigOperators Topology

noncomputable section

def polarMellinWeightedKernel (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (u v : ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  polarMellinArithmeticKernel T σ m u v z/z*(x:ℂ)^(2*z)

theorem polarMellinScaleWeight_horizontal_norm_bound {δ x c y : ℝ}
    (hx : 0 < x) (hc : c ∈ Icc (-δ/2) 1) (hy : 1 ≤ |y|) :
    ‖(((c:ℂ)+(y:ℂ)*I):ℂ)⁻¹*(x:ℂ)^(2*((c:ℂ)+(y:ℂ)*I))‖ ≤
      x^(-δ)+x^2 := by
  have hz : 1 ≤ ‖((c:ℂ)+(y:ℂ)*I : ℂ)‖ := by
    exact hy.trans (by simpa using Complex.abs_im_le_norm (((c:ℂ)+(y:ℂ)*I):ℂ))
  have hi : ‖((c:ℂ)+(y:ℂ)*I : ℂ)‖⁻¹ ≤ 1 :=
    (inv_anti₀ (by norm_num : (0:ℝ) < 1) hz).trans_eq (by norm_num)
  have hp : x^(2*c) ≤ x^(-δ)+x^2 := by
    by_cases hx1 : 1 ≤ x
    · have h := Real.rpow_le_rpow_of_exponent_le hx1 (show 2*c ≤ (2:ℝ) by linarith [hc.2])
      rw [Real.rpow_ofNat] at h
      linarith [Real.rpow_nonneg hx.le (-δ)]
    · have h := Real.rpow_le_rpow_of_exponent_ge hx (le_of_not_ge hx1)
        (show -δ ≤ 2*c by linarith [hc.1])
      linarith [sq_nonneg x]
  rw [norm_mul,norm_inv,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have he : (2*((c:ℂ)+(y:ℂ)*I)).re = 2*c := by simp
  rw [he]
  exact (mul_le_mul_of_nonneg_right hi (Real.rpow_nonneg hx.le _)).trans
    (by simpa only [one_mul] using hp)

theorem polarMellinScaleWeight_right_norm_bound {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖((1+(y:ℂ)*I):ℂ)⁻¹*(x:ℂ)^(2*(1+(y:ℂ)*I))‖ ≤ x^2 := by
  have hz : 1 ≤ ‖(1+(y:ℂ)*I : ℂ)‖ := by
    simpa using Complex.re_le_norm ((1+(y:ℂ)*I):ℂ)
  have hi : ‖(1+(y:ℂ)*I : ℂ)‖⁻¹ ≤ 1 :=
    (inv_anti₀ (by norm_num : (0:ℝ) < 1) hz).trans_eq (by norm_num)
  rw [norm_mul,norm_inv,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have he : (2*(1+(y:ℂ)*I)).re = 2 := by simp
  rw [he,Real.rpow_ofNat]
  exact (mul_le_mul_of_nonneg_right hi (sq_nonneg x)).trans_eq (one_mul _)

theorem purePolarZetaProduct_right_norm_bound (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {δ : ℝ} (hδ1 : δ < 1/4)
    (hρ : ∀ ij : Fin 2 × Fin 2, ‖purePolarRoot T σ (m,ij)‖ ≤ δ/4) (y : ℝ) :
    ‖purePolarZetaProduct T σ m (1+(y:ℂ)*I)‖ ≤ (zetaDirichletMajorant 2)^4 := by
  have harg (ij : Fin 2 × Fin 2) :
      (2:ℝ) ≤ (1+2*((1+(y:ℂ)*I)-purePolarRoot T σ (m,ij))).re := by
    have hre := (Complex.abs_re_le_norm (purePolarRoot T σ (m,ij))).trans (hρ ij)
    have he : (1+2*((1+(y:ℂ)*I)-purePolarRoot T σ (m,ij))).re =
        3-2*(purePolarRoot T σ (m,ij)).re := by simp; ring
    rw [he]
    linarith [(abs_le.mp hre).2]
  simpa only [purePolarZetaProduct,Finset.card_univ,Fintype.card_prod,Fintype.card_fin] using
    finiteRiemannZetaProduct_norm_le_dirichlet Finset.univ
      (fun ij : Fin 2 × Fin 2 => 1+2*((1+(y:ℂ)*I)-purePolarRoot T σ (m,ij)))
      (by norm_num : (1:ℝ) < 2) (fun ij _ => harg ij)

theorem purePolarZetaProduct_right_continuous (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {δ : ℝ} (hδ1 : δ < 1/4)
    (hρ : ∀ ij : Fin 2 × Fin 2, ‖purePolarRoot T σ (m,ij)‖ ≤ δ/4) :
    Continuous (fun y : ℝ => purePolarZetaProduct T σ m (1+(y:ℂ)*I)) := by
  unfold purePolarZetaProduct
  apply continuous_finsetProd
  intro ij _
  apply continuous_iff_continuousAt.mpr
  intro y
  have hne : 1+2*((1+(y:ℂ)*I)-purePolarRoot T σ (m,ij)) ≠ 1 := by
    intro heq
    have hre := (Complex.abs_re_le_norm (purePolarRoot T σ (m,ij))).trans (hρ ij)
    have he : (1+2*((1+(y:ℂ)*I)-purePolarRoot T σ (m,ij))).re =
        3-2*(purePolarRoot T σ (m,ij)).re := by simp; ring
    have hh := congrArg Complex.re heq
    rw [he,one_re] at hh
    linarith [(abs_le.mp hre).2]
  exact ContinuousAt.comp (f := fun y : ℝ => 1+2*((1+(y:ℂ)*I)-purePolarRoot T σ (m,ij)))
    (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)

theorem polarMellinWeightedKernel_right_integrable
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {δ x : ℝ} {u v : ℂ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4) (hx : 0 < x)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) :
    Integrable (fun y : ℝ => polarMellinWeightedKernel T σ m u v x (1+(y:ℂ)*I)) := by
  have hρ (ij : Fin 2 × Fin 2) : ‖purePolarRoot T σ (m,ij)‖ ≤ δ/4 :=
    purePolarRoot_norm_le_of_rawShifts hα (m,ij)
  have hshift (j : Fin 4) :
      ‖Source.bblrSixShifts (rawMomentShifts T σ) m j‖ ≤ δ/4 :=
    bblrSixShifts_norm_le _ hα m j
  have hA := polarArithmeticEntangledFactor_vertical_continuous hδ hδ1 hshift hu hv
    (show -δ/2 ≤ (1:ℝ) by linarith)
  have hZ := purePolarZetaProduct_right_continuous T σ m hδ1 hρ
  have hxne : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hz : Continuous (fun y : ℝ => (1+(y:ℂ)*I : ℂ)) := by fun_prop
  have hzne (y : ℝ) : (1+(y:ℂ)*I : ℂ) ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp at h
  have hw := (hz.inv₀ hzne).mul ((hz.const_mul (2:ℂ)).const_cpow (.inl hxne))
  have hcont := (hA.mul hZ).mul hw
  have hI := (polarPoleKiller_vertical_integrable T σ 1).bdd_mul
    hcont.aestronglyMeasurable
    (c := polarArithmeticEntangledMajorant δ*(zetaDirichletMajorant 2)^4*x^2)
    (Eventually.of_forall (fun y : ℝ => by
      simp only [Pi.mul_apply,Pi.inv_apply,Complex.ofReal_one]
      rw [norm_mul,norm_mul]
      apply mul_le_mul _ (polarMellinScaleWeight_right_norm_bound hx y)
        (norm_nonneg _) (mul_nonneg (polarArithmeticEntangledMajorant_nonneg δ)
          (pow_nonneg (zetaDirichletMajorant_nonneg _) _))
      exact mul_le_mul
        (polarArithmeticEntangledFactor_norm_bound hδ hδ1 hshift hu hv (by simp; linarith))
        (purePolarZetaProduct_right_norm_bound T σ m hδ1 hρ y) (norm_nonneg _)
        (polarArithmeticEntangledMajorant_nonneg δ)))
  convert hI using 1
  funext y
  simp only [polarMellinWeightedKernel,polarMellinArithmeticKernel,div_eq_mul_inv,
    Pi.mul_apply,Pi.inv_apply,Complex.ofReal_one]
  ring

theorem polarMellinWeightedKernel_horizontal_bound (T : ℝ) (σ : MomentShifts)
    (m : Fin 6) {δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1/4) (hx : 0 < x)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ y : ℝ, M+1 ≤ |y| →
      ∀ u v : ℂ, δ ≤ u.re → δ ≤ v.re → ∀ c ∈ Icc (-δ/2) 1,
        ‖polarMellinWeightedKernel T σ m u v x ((c:ℂ)+(y:ℂ)*I)‖ ≤
          C*(1+|y|)^48*Real.exp (4*Real.pi*|y|-y^2) := by
  obtain ⟨C,M,hC0,hM0,hbound⟩ :=
    polarMellinArithmeticKernel_horizontal_bound T σ m hδ hδ1 hα
  have hxW : 0 ≤ x^(-δ)+x^2 := by positivity
  refine ⟨C*(x^(-δ)+x^2),M,mul_nonneg hC0 hxW,hM0,?_⟩
  intro y hy u v hu hv c hc
  unfold polarMellinWeightedKernel
  rw [div_eq_mul_inv,mul_assoc,norm_mul]
  calc
    _ ≤ (C*(1+|y|)^48*Real.exp (4*Real.pi*|y|-y^2))*(x^(-δ)+x^2) :=
      mul_le_mul (hbound y hy u v hu hv c hc)
        (polarMellinScaleWeight_horizontal_norm_bound hx hc (by linarith))
        (norm_nonneg _) (by positivity)
    _ = _ := by ac_rfl

theorem polarMellinWeightedKernel_horizontal_integral_tendsto_zero
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {δ x : ℝ} {u v : ℂ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4) (hx : 0 < x)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) :
    Tendsto (fun y : ℝ => ∫ c in (-δ/2)..1,
      polarMellinWeightedKernel T σ m u v x ((c:ℂ)+(y:ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C,M,_hC0,_hM0,hbound⟩ :=
    polarMellinWeightedKernel_horizontal_bound T σ m hδ hδ1 hx hα
  have hlarge : ∀ᶠ y : ℝ in cocompact ℝ, M+1 ≤ |y| := by
    rw [cocompact_eq_atBot_atTop,← comap_abs_atTop]
    exact (eventually_ge_atTop (M+1)).comap _
  have hnorm : ∀ᶠ y : ℝ in cocompact ℝ,
      ‖∫ c in (-δ/2)..1, polarMellinWeightedKernel T σ m u v x ((c:ℂ)+(y:ℂ)*I)‖ ≤
      (C*|1-(-δ/2)|)*((1+|y|)^48*Real.exp (4*Real.pi*|y|-y^2)) := by
    filter_upwards [hlarge] with y hy
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -δ/2) (b := 1)
      (f := fun c => polarMellinWeightedKernel T σ m u v x ((c:ℂ)+(y:ℂ)*I))
      (C := C*(1+|y|)^48*Real.exp (4*Real.pi*|y|-y^2))
      (by
        intro c hc
        rw [uIoc_of_le (by linarith : -δ/2 ≤ (1:ℝ))] at hc
        exact hbound y hy u v hu hv c ⟨hc.1.le,hc.2⟩)
    exact hb.trans_eq (by ac_rfl)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim := (gaussianPolynomialExponential_tendsto_zero 48 (4*Real.pi)).const_mul
    (C*|1-(-δ/2)|)
  simp only [mul_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hnorm hlim

end

end Sechstmoment
