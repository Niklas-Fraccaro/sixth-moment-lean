import Mathlib.Tactic
import SixthMoment.Arithmetic.QuadraticDivisor.Definitions
import SixthMoment.Numerator.Polar.GaussianControl
import SixthMoment.Numerator.Polar.PureRemoval
import SixthMoment.Zeta.Bounds.MellinZetaGrowth


namespace SixthMoment

open Real Complex MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

theorem purePolarZetaProduct_vertical_norm_bound
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) (c : ℝ)
    {a b r M : ℝ} (ha : 0 < a) (hb : b < 2) (hr : 0 < r)
    (hM : ∀ ij : Fin 2 × Fin 2, |(purePolarRoot T σ (m,ij)).im| ≤ M)
    (harg : ∀ v : ℝ, ∀ ij : Fin 2 × Fin 2,
      a ≤ (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).re ∧
      (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).re ≤ b ∧
      r ≤ ‖1-(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)))‖) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ v : ℝ,
      ‖purePolarZetaProduct T σ m ((c:ℂ)+(v:ℂ)*I)‖ ≤
        D*Real.exp (4*Real.pi*|v|) := by
  obtain ⟨C, hC0, hC⟩ := riemannZeta_norm_le_exp_strip ha hb hr
  refine ⟨C^4*Real.exp (4*Real.pi*M), by positivity, ?_⟩
  intro v
  have hz (ij : Fin 2 × Fin 2) :
      ‖riemannZeta (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)))‖ ≤
        C*Real.exp (Real.pi*(|v|+M)) := by
    have h := hC _ (harg v ij).1 (harg v ij).2.1 (harg v ij).2.2
    have him : |(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).im| ≤
        2*(|v|+M) := by
      have he : (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).im =
          2*(v-(purePolarRoot T σ (m,ij)).im) := by simp
      rw [he, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left ((abs_sub v _).trans
        (add_le_add le_rfl (hM ij))) (by norm_num)
    exact h.trans (by gcongr; nlinarith [Real.pi_pos])
  unfold purePolarZetaProduct
  calc
    _ ≤ ∏ ij : Fin 2 × Fin 2,
        ‖riemannZeta (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)))‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ _ij : Fin 2 × Fin 2, C*Real.exp (Real.pi*(|v|+M)) :=
      Finset.prod_le_prod₀ (fun ij _ => norm_nonneg _) (fun ij _ => hz ij)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      norm_num only
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem polarPoleKiller_mul_pureZeta_vertical_integrable
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) (c : ℝ)
    {a b r M : ℝ} (ha : 0 < a) (hb : b < 2) (hr : 0 < r)
    (hM : ∀ ij : Fin 2 × Fin 2, |(purePolarRoot T σ (m,ij)).im| ≤ M)
    (harg : ∀ v : ℝ, ∀ ij : Fin 2 × Fin 2,
      a ≤ (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).re ∧
      (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).re ≤ b ∧
      r ≤ ‖1-(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)))‖) :
    Integrable (fun v : ℝ => polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I) *
      purePolarZetaProduct T σ m ((c:ℂ)+(v:ℂ)*I)) := by
  obtain ⟨D, hD0, hD⟩ := purePolarZetaProduct_vertical_norm_bound T σ m c ha hb hr hM harg
  have hI := (gaussianPolynomialExponential_integrable 48 (4*Real.pi)).const_mul
    (polarGaussianConstant T σ c*D)
  apply hI.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (polarPoleKiller_differentiable T σ).continuous.comp (by fun_prop)
    · unfold purePolarZetaProduct
      apply continuous_finsetProd
      intro ij _
      apply continuous_iff_continuousAt.mpr
      intro v
      have hne : 1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)) ≠ 1 := by
        intro h
        have hs := (harg v ij).2.2
        rw [h, sub_self, norm_zero] at hs
        linarith
      have hg : ContinuousAt (fun x : ℝ =>
          1+2*(((c:ℂ)+(x:ℂ)*I)-purePolarRoot T σ (m,ij))) v := by fun_prop
      exact ContinuousAt.comp (f := fun x : ℝ =>
          1+2*(((c:ℂ)+(x:ℂ)*I)-purePolarRoot T σ (m,ij)))
        (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt hg
  · apply Filter.Eventually.of_forall
    intro v
    rw [norm_mul]
    calc
      _ ≤ (polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2)) *
          (D*Real.exp (4*Real.pi*|v|)) := by
        exact mul_le_mul (polarPoleKiller_vertical_norm_le T σ c v) (hD v)
          (norm_nonneg _) (by
            have hG0 := polarGaussianConstant_nonneg T σ c
            positivity)
      _ = _ := by
        have he : Real.exp (-v^2)*Real.exp (4*Real.pi*|v|) =
            Real.exp (4*Real.pi*|v|-v^2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hm : (polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2)) *
            (D*Real.exp (4*Real.pi*|v|)) =
            (polarGaussianConstant T σ c*D)*((1+|v|)^48 *
              (Real.exp (-v^2)*Real.exp (4*Real.pi*|v|))) := by ac_rfl
        rw [hm, he]

end

end SixthMoment
