import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Sechstmoment.Analysis.Gaussian.Decay
import Sechstmoment.Numerator.Polar.PureLeftContour
import Sechstmoment.Zeta.Bounds.MellinZetaHalfPlaneGrowth

/-!
# Vanishing horizontal sides for the actual pure-zeta Gaussian factor

On the literal strip between `-δ/2` and `1`, the actual four zeta arguments
have uniformly positive real parts. At large height their poles are uniformly
separated. The actual Gaussian majorant therefore makes both horizontal side
integrals vanish. This is one ingredient of the full Mellin contour move;
the arithmetic factor and five entangled factors remain separate.
-/

namespace Sechstmoment

open Real Complex MeasureTheory Filter Set
open scoped BigOperators Topology

noncomputable section

theorem polarGaussianConstant_le_of_abs_le (T : ℝ) (σ : MomentShifts)
    {c R : ℝ} (hR : 0 ≤ R) (hc : |c| ≤ R) :
    polarGaussianConstant T σ c ≤ polarGaussianConstant T σ R := by
  unfold polarGaussianConstant
  rw [abs_of_nonneg hR]
  have hc2 : c^2 ≤ R^2 := by nlinarith [sq_abs c, abs_nonneg c]
  gcongr

theorem purePolarZetaProduct_norm_halfPlane_bound
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {a r M : ℝ}
    (ha : 0 < a) (hr : 0 < r)
    (hM : ∀ ij : Fin 2 × Fin 2, |(purePolarRoot T σ (m,ij)).im| ≤ M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℂ,
      (∀ ij : Fin 2 × Fin 2, a ≤ (1+2*(z-purePolarRoot T σ (m,ij))).re) →
      (∀ ij : Fin 2 × Fin 2, r ≤ ‖1-(1+2*(z-purePolarRoot T σ (m,ij)))‖) →
      ‖purePolarZetaProduct T σ m z‖ ≤ D*Real.exp (4*Real.pi*|z.im|) := by
  obtain ⟨C, hC0, hC⟩ := riemannZeta_norm_le_exp_halfPlane ha hr
  refine ⟨C^4*Real.exp (4*Real.pi*M), by positivity, ?_⟩
  intro z harg hsep
  have hz (ij : Fin 2 × Fin 2) :
      ‖riemannZeta (1+2*(z-purePolarRoot T σ (m,ij)))‖ ≤
        C*Real.exp (Real.pi*(|z.im|+M)) := by
    have h := hC _ (harg ij) (hsep ij)
    have him : |(1+2*(z-purePolarRoot T σ (m,ij))).im| ≤ 2*(|z.im|+M) := by
      have he : (1+2*(z-purePolarRoot T σ (m,ij))).im =
          2*(z.im-(purePolarRoot T σ (m,ij)).im) := by simp
      rw [he, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left ((abs_sub z.im _).trans
        (add_le_add le_rfl (hM ij))) (by norm_num)
    exact h.trans (by gcongr; nlinarith [Real.pi_pos])
  unfold purePolarZetaProduct
  calc
    _ ≤ ∏ ij : Fin 2 × Fin 2, ‖riemannZeta (1+2*(z-purePolarRoot T σ (m,ij)))‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ _ij : Fin 2 × Fin 2, C*Real.exp (Real.pi*(|z.im|+M)) :=
      Finset.prod_le_prod₀ (fun ij _ => norm_nonneg _) (fun ij _ => hz ij)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      norm_num only
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem polarPureGaussian_horizontal_bound (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1/2)
    (hρ : ∀ ij : Fin 2 × Fin 2, ‖purePolarRoot T σ (m,ij)‖ ≤ δ/4) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ v : ℝ, M+1 ≤ |v| →
      ∀ c ∈ Icc (-δ/2) 1,
        ‖polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)*
          purePolarZetaProduct T σ m ((c:ℂ)+(v:ℂ)*I)‖ ≤
        C*(1+|v|)^48*Real.exp (4*Real.pi*|v|-v^2) := by
  let M : ℝ := ∑ ij : Fin 2 × Fin 2, |(purePolarRoot T σ (m,ij)).im|
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hM (ij : Fin 2 × Fin 2) : |(purePolarRoot T σ (m,ij)).im| ≤ M := by
    dsimp only [M]
    exact Finset.single_le_sum (fun k _ => abs_nonneg ((purePolarRoot T σ (m,k)).im))
      (Finset.mem_univ ij)
  obtain ⟨D, hD0, hD⟩ := purePolarZetaProduct_norm_halfPlane_bound T σ m
    (a := 1/4) (r := 1) (by norm_num) (by norm_num) hM
  let C : ℝ := polarGaussianConstant T σ 1*D
  have hG0 := polarGaussianConstant_nonneg T σ 1
  refine ⟨C, M, mul_nonneg hG0 hD0, hM0, ?_⟩
  intro v hv c hc
  have hc1 : |c| ≤ 1 := abs_le.mpr ⟨by linarith [hc.1], hc.2⟩
  have harg (ij : Fin 2 × Fin 2) :
      (1/4:ℝ) ≤ (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).re := by
    have hre := (Complex.abs_re_le_norm (purePolarRoot T σ (m,ij))).trans (hρ ij)
    have he : (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).re =
        1+2*(c-(purePolarRoot T σ (m,ij)).re) := by simp
    rw [he]
    linarith [(abs_le.mp hre).1, (abs_le.mp hre).2, hc.1]
  have hsep (ij : Fin 2 × Fin 2) :
      (1:ℝ) ≤ ‖1-(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)))‖ := by
    have hab : |v| ≤ |v-(purePolarRoot T σ (m,ij)).im|+|(purePolarRoot T σ (m,ij)).im| :=
      by simpa only [sub_add_cancel] using
        abs_add_le (v-(purePolarRoot T σ (m,ij)).im) (purePolarRoot T σ (m,ij)).im
    have him : |(1-(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)))).im| =
        2*|v-(purePolarRoot T σ (m,ij)).im| := by
      have he : (1-(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)))).im =
          -(2*(v-(purePolarRoot T σ (m,ij)).im)) := by simp
      rw [he, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hn := Complex.abs_im_le_norm
      (1-(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))))
    rw [him] at hn
    linarith [hM ij]
  have hZ := hD _ harg hsep
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
    add_zero, zero_add] at hZ
  have hG := polarPoleKiller_vertical_norm_le T σ c v
  have hCG := polarGaussianConstant_le_of_abs_le T σ (by norm_num : (0:ℝ) ≤ 1) hc1
  have hG' : ‖polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)‖ ≤
      polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-v^2) := by
    exact hG.trans (by gcongr)
  rw [norm_mul]
  calc
    _ ≤ (polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-v^2)) *
        (D*Real.exp (4*Real.pi*|v|)) :=
      mul_le_mul hG' hZ (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (-v^2)*Real.exp (4*Real.pi*|v|) =
          Real.exp (4*Real.pi*|v|-v^2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hm : (polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-v^2)) *
          (D*Real.exp (4*Real.pi*|v|)) =
          C*(1+|v|)^48*(Real.exp (-v^2)*Real.exp (4*Real.pi*|v|)) := by dsimp [C]; ac_rfl
      rw [hm, he]

theorem polarPureGaussian_horizontal_integral_tendsto_zero
    (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1/2)
    (hρ : ∀ ij : Fin 2 × Fin 2, ‖purePolarRoot T σ (m,ij)‖ ≤ δ/4) :
    Tendsto (fun v : ℝ => ∫ c in (-δ/2)..1,
      polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)*
        purePolarZetaProduct T σ m ((c:ℂ)+(v:ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, M, _hC0, _hM0, hbound⟩ :=
    polarPureGaussian_horizontal_bound T σ m hδ hδ1 hρ
  have hlarge : ∀ᶠ v : ℝ in cocompact ℝ, M+1 ≤ |v| := by
    rw [cocompact_eq_atBot_atTop, ← comap_abs_atTop]
    exact (eventually_ge_atTop (M+1)).comap _
  have hnorm : ∀ᶠ v : ℝ in cocompact ℝ,
      ‖∫ c in (-δ/2)..1, polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)*
        purePolarZetaProduct T σ m ((c:ℂ)+(v:ℂ)*I)‖ ≤
      (C*|1-(-δ/2)|)*((1+|v|)^48*Real.exp (4*Real.pi*|v|-v^2)) := by
    filter_upwards [hlarge] with v hv
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -δ/2) (b := 1)
      (f := fun c => polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)*
        purePolarZetaProduct T σ m ((c:ℂ)+(v:ℂ)*I))
      (C := C*(1+|v|)^48*Real.exp (4*Real.pi*|v|-v^2))
      (by
        intro c hc
        rw [uIoc_of_le (by linarith : -δ/2 ≤ (1:ℝ))] at hc
        exact hbound v hv c ⟨hc.1.le, hc.2⟩)
    exact hb.trans_eq (by ac_rfl)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim := (gaussianPolynomialExponential_tendsto_zero 48 (4*Real.pi)).const_mul
    (C*|1-(-δ/2)|)
  simp only [mul_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hnorm hlim

end

end Sechstmoment
