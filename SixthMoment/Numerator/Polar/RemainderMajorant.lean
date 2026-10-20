import Mathlib.Tactic
import SixthMoment.Numerator.Polar.EulerMellinKernel
import SixthMoment.Numerator.Polar.GaussianLogGrowth


namespace SixthMoment

open Real Complex MeasureTheory Set
open scoped BigOperators

noncomputable section

theorem purePolarZetaProduct_left_uniform_norm_bound {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : ℝ) (σ : MomentShifts) (m : Fin 6),
      (∀ ij : Fin 2 × Fin 2, ‖purePolarRoot T σ (m,ij)‖ ≤ δ/4) → ∀ y : ℝ,
        ‖purePolarZetaProduct T σ m ((-δ/2:ℝ)+(y:ℂ)*I)‖ ≤
          D*Real.exp (4*Real.pi*|y|) := by
  obtain ⟨C,hC0,hC⟩ := riemannZeta_norm_le_exp_halfPlane
    (a := 1/4) (r := δ/2) (by norm_num) (by linarith)
  refine ⟨C^4*Real.exp (Real.pi*δ),by positivity,?_⟩
  intro T σ m hρ y
  have hz (ij : Fin 2 × Fin 2) :
      ‖riemannZeta (1+2*(((-δ/2:ℝ)+(y:ℂ)*I)-purePolarRoot T σ (m,ij)))‖ ≤
        C*Real.exp (Real.pi*(|y|+δ/4)) := by
    have hre := (Complex.abs_re_le_norm (purePolarRoot T σ (m,ij))).trans (hρ ij)
    have him := (Complex.abs_im_le_norm (purePolarRoot T σ (m,ij))).trans (hρ ij)
    have he : (1+2*(((-δ/2:ℝ)+(y:ℂ)*I)-purePolarRoot T σ (m,ij))).re =
        1-δ-2*(purePolarRoot T σ (m,ij)).re := by simp; ring
    have harg : (1/4:ℝ) ≤
        (1+2*(((-δ/2:ℝ)+(y:ℂ)*I)-purePolarRoot T σ (m,ij))).re := by
      rw [he]
      linarith [(abs_le.mp hre).2]
    have hsep : δ/2 ≤ ‖1-(1+2*(((-δ/2:ℝ)+(y:ℂ)*I)-purePolarRoot T σ (m,ij)))‖ := by
      have hn := Complex.re_le_norm
        (1-(1+2*(((-δ/2:ℝ)+(y:ℂ)*I)-purePolarRoot T σ (m,ij))))
      rw [sub_re,one_re,he] at hn
      linarith [(abs_le.mp hre).1]
    have hi : |(1+2*(((-δ/2:ℝ)+(y:ℂ)*I)-purePolarRoot T σ (m,ij))).im| ≤
        2*(|y|+δ/4) := by
      have hei : (1+2*(((-δ/2:ℝ)+(y:ℂ)*I)-purePolarRoot T σ (m,ij))).im =
          2*(y-(purePolarRoot T σ (m,ij)).im) := by simp
      rw [hei,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left ((abs_sub y _).trans (add_le_add le_rfl him))
        (by norm_num)
    exact (hC _ harg hsep).trans (by gcongr; nlinarith [Real.pi_pos])
  unfold purePolarZetaProduct
  calc
    _ ≤ ∏ ij : Fin 2 × Fin 2,
        ‖riemannZeta (1+2*(((-δ/2:ℝ)+(y:ℂ)*I)-purePolarRoot T σ (m,ij)))‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ _ij : Fin 2 × Fin 2, C*Real.exp (Real.pi*(|y|+δ/4)) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun ij _ => hz ij)
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
      norm_num only
      rw [mul_pow,← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring

theorem polarMellinArithmeticKernel_left_uniform_log_bound {δ κ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ), 1 < T → 1 ≤ Real.log T →
      ∀ (σ : MomentShifts),
      (∀ k : PurePolarIndex, κ ≤ ‖Source.normalizedPurePolarRoot σ k‖) →
      (∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4) →
      ∀ (m : Fin 6) (u v : ℂ), δ ≤ u.re → δ ≤ v.re → ∀ y : ℝ,
        ‖polarMellinArithmeticKernel T σ m u v ((-δ/2:ℝ)+(y:ℂ)*I)‖ ≤
          C*(Real.log T)^48*((1+|y|)^48*Real.exp (4*Real.pi*|y|-y^2)) := by
  obtain ⟨D,hD0,hD⟩ := purePolarZetaProduct_left_uniform_norm_bound hδ hδ1
  let B : ℝ := Real.exp ((-δ/2)^2)*(1+|-δ/2|)^48*(1+1/κ^2)^24
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨polarArithmeticEntangledMajorant δ*B*D,
    mul_nonneg (mul_nonneg (polarArithmeticEntangledMajorant_nonneg δ) hB0) hD0,?_⟩
  intro T hT hL σ hgap hα m u v hu hv y
  have hρ (ij : Fin 2 × Fin 2) : ‖purePolarRoot T σ (m,ij)‖ ≤ δ/4 :=
    purePolarRoot_norm_le_of_rawShifts hα (m,ij)
  have hshift (j : Fin 4) :
      ‖Source.bblrSixShifts (rawMomentShifts T σ) m j‖ ≤ δ/4 :=
    bblrSixShifts_norm_le _ hα m j
  have hA := polarArithmeticEntangledFactor_norm_bound hδ hδ1 hshift hu hv
    (show -δ/2 ≤ ((-δ/2:ℝ)+(y:ℂ)*I).re by simp)
  have hG := (polarPoleKiller_vertical_norm_le T σ (-δ/2) y).trans
    (show polarGaussianConstant T σ (-δ/2)*(1+|y|)^48*Real.exp (-y^2) ≤
      (B*(Real.log T)^48)*(1+|y|)^48*Real.exp (-y^2) by
      gcongr
      exact polarGaussianConstant_log_growth hT hL hκ σ (-δ/2) hgap)
  unfold polarMellinArithmeticKernel
  rw [norm_mul,norm_mul]
  calc
    _ ≤ polarArithmeticEntangledMajorant δ*
        (((B*(Real.log T)^48)*(1+|y|)^48*Real.exp (-y^2))*
          (D*Real.exp (4*Real.pi*|y|))) := by
      apply mul_le_mul hA _ (by positivity) (polarArithmeticEntangledMajorant_nonneg δ)
      exact mul_le_mul hG (hD T σ m hρ y) (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (-y^2)*Real.exp (4*Real.pi*|y|) =
          Real.exp (4*Real.pi*|y|-y^2) := by rw [← Real.exp_add]; congr 1; ring
      calc
        _ = (polarArithmeticEntangledMajorant δ*B*D)*(Real.log T)^48*
            ((1+|y|)^48*(Real.exp (-y^2)*Real.exp (4*Real.pi*|y|))) := by ac_rfl
        _ = _ := by rw [he]

def polarMellinRemainderIntegral (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (u v : ℂ) (x δ : ℝ) : ℂ :=
  Source.verticalIntegral (-δ/2) fun z =>
    polarMellinArithmeticKernel T σ m u v z/z*(x:ℂ)^(2*z)

theorem polarMellinScaleWeight_left_norm_bound {δ x : ℝ}
    (hδ : 0 < δ) (hx : 0 < x) (y : ℝ) :
    ‖(((-δ/2:ℝ)+(y:ℂ)*I):ℂ)⁻¹*(x:ℂ)^(2*((-δ/2:ℝ)+(y:ℂ)*I))‖ ≤
      (2/δ)*x^(-δ) := by
  have hz : δ/2 ≤ ‖((-δ/2:ℝ)+(y:ℂ)*I : ℂ)‖ := by
    have hn := Complex.abs_re_le_norm (((-δ/2:ℝ)+(y:ℂ)*I):ℂ)
    have he : (((-δ/2:ℝ)+(y:ℂ)*I):ℂ).re = -δ/2 := by simp
    rw [he,abs_of_nonpos (by linarith : -δ/2 ≤ (0:ℝ))] at hn
    linarith
  rw [norm_mul,norm_inv,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have he : (2*((-δ/2:ℝ)+(y:ℂ)*I)).re = -δ := by simp; ring
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
  calc
    _ ≤ (δ/2)⁻¹ := inv_anti₀ (by linarith) hz
    _ = _ := by field_simp

theorem polarMellinRemainderIntegrand_left_integrable
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {δ x : ℝ} {u v : ℂ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4) (hx : 0 < x)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) :
    Integrable (fun y : ℝ =>
      polarMellinArithmeticKernel T σ m u v ((-δ/2:ℝ)+(y:ℂ)*I)/
        ((-δ/2:ℝ)+(y:ℂ)*I)*(x:ℂ)^(2*((-δ/2:ℝ)+(y:ℂ)*I))) := by
  have hz : Continuous (fun y : ℝ => ((-δ/2:ℝ)+(y:ℂ)*I : ℂ)) := by fun_prop
  have hzne (y : ℝ) : ((-δ/2:ℝ)+(y:ℂ)*I : ℂ) ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp at hre
    linarith
  have hxne : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hw : Continuous (fun y : ℝ =>
      (((-δ/2:ℝ)+(y:ℂ)*I):ℂ)⁻¹*(x:ℂ)^(2*((-δ/2:ℝ)+(y:ℂ)*I))) :=
    (hz.inv₀ hzne).mul ((hz.const_mul (2:ℂ)).const_cpow (.inl hxne))
  have hI := (polarMellinArithmeticKernel_left_integrable T σ m hδ hδ1 hα hu hv).mul_bdd
    hw.aestronglyMeasurable
    (Filter.Eventually.of_forall (polarMellinScaleWeight_left_norm_bound hδ hx))
  simpa only [div_eq_mul_inv,mul_assoc] using hI

theorem polarMellinRemainderIntegral_uniform_log_bound {δ κ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ), 1 < T → 1 ≤ Real.log T →
      ∀ (σ : MomentShifts),
      (∀ k : PurePolarIndex, κ ≤ ‖Source.normalizedPurePolarRoot σ k‖) →
      (∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4) →
      ∀ (m : Fin 6) (u v : ℂ), δ ≤ u.re → δ ≤ v.re → ∀ x : ℝ, 0 < x →
        ‖polarMellinRemainderIntegral T σ m u v x δ‖ ≤
          C*(Real.log T)^48*x^(-δ) := by
  obtain ⟨B,hB0,hB⟩ := polarMellinArithmeticKernel_left_uniform_log_bound hδ hδ1 hκ
  let J : ℝ := ∫ y : ℝ, (1+|y|)^48*Real.exp (4*Real.pi*|y|-y^2)
  have hJ0 : 0 ≤ J := integral_nonneg (fun _ => by positivity)
  refine ⟨(1/(2*Real.pi))*B*(2/δ)*J,by positivity,?_⟩
  intro T hT hL σ hgap hα m u v hu hv x hx
  have hdom := (gaussianPolynomialExponential_integrable 48 (4*Real.pi)).const_mul
    (B*(Real.log T)^48*((2/δ)*x^(-δ)))
  have hN := norm_integral_le_of_norm_le
    (f := fun y : ℝ =>
      polarMellinArithmeticKernel T σ m u v ((-δ/2:ℝ)+(y:ℂ)*I)/
        ((-δ/2:ℝ)+(y:ℂ)*I)*(x:ℂ)^(2*((-δ/2:ℝ)+(y:ℂ)*I))) hdom
    (Filter.Eventually.of_forall (fun y : ℝ => by
      rw [div_eq_mul_inv,mul_assoc,norm_mul]
      calc
        _ ≤ (B*(Real.log T)^48*((1+|y|)^48*Real.exp (4*Real.pi*|y|-y^2)))*
            ((2/δ)*x^(-δ)) :=
          mul_le_mul (hB T hT hL σ hgap hα m u v hu hv y)
            (polarMellinScaleWeight_left_norm_bound hδ hx y) (norm_nonneg _) (by positivity)
        _ = _ := by ac_rfl))
  rw [integral_const_mul] at hN
  unfold polarMellinRemainderIntegral Source.verticalIntegral
  rw [norm_mul]
  have hp : ‖(1/(2*Real.pi):ℂ)‖ = 1/(2*Real.pi) := by
    rw [norm_div,norm_one,norm_mul]
    norm_num only [Complex.norm_ofNat]
    rw [Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  rw [hp]
  calc
    _ ≤ (1/(2*Real.pi))*(B*(Real.log T)^48*((2/δ)*x^(-δ))*J) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    _ = _ := by ring

end

end SixthMoment
