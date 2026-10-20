import Mathlib.Tactic
import Sechstmoment.Numerator.Polar.PureIntegrability
import Sechstmoment.Numerator.U.Replacement.GaussianCoefficientGrowth


namespace Sechstmoment

open Real Complex MeasureTheory Filter Set
open scoped BigOperators Topology

noncomputable section

theorem bblrSixShifts_norm_le (σ : MomentShifts) {R : ℝ}
    (hσ : ∀ i : Fin 4, ‖σ i‖ ≤ R) (m : Fin 6) (j : Fin 4) :
    ‖Source.bblrSixShifts σ m j‖ ≤ R := by
  fin_cases m <;> fin_cases j <;> simp [Source.bblrSixShifts] <;>
    first | exact hσ 0 | exact hσ 1 | exact hσ 2 | exact hσ 3

theorem normalizedPurePolarRoot_norm_le (σ : MomentShifts) {R : ℝ}
    (hσ : ∀ i : Fin 4, ‖σ i‖ ≤ R) (k : PurePolarIndex) :
    ‖Source.normalizedPurePolarRoot σ k‖ ≤ R := by
  unfold Source.normalizedPurePolarRoot
  rw [norm_div, norm_neg]
  norm_num only [Complex.norm_ofNat]
  have h1 := bblrSixShifts_norm_le σ hσ k.1 (purePolarLeft k.2.1)
  have h2 := bblrSixShifts_norm_le σ hσ k.1 (purePolarRight k.2.2)
  have hsum := norm_add_le
    (Source.bblrSixShifts σ k.1 (purePolarLeft k.2.1))
    (Source.bblrSixShifts σ k.1 (purePolarRight k.2.2))
  linarith

theorem purePolarRoot_uniform_eventually_small {R δ : ℝ} (_hR : 0 ≤ R) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts, (∀ i : Fin 4, ‖σ i‖ ≤ R) →
      ∀ k : PurePolarIndex, ‖purePolarRoot T σ k‖ ≤ δ/4 := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (max 1 (4*R/δ)))]
    with T hT hL σ hσ k
  have hLp : 0 < Real.log T := Real.log_pos hT
  have hLC : 4*R/δ < Real.log T := lt_of_le_of_lt (le_max_right _ _) hL
  rw [Source.purePolarRoot_normalized, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hLp.le]
  apply (div_le_div_of_nonneg_right (normalizedPurePolarRoot_norm_le σ hσ k) hLp.le).trans
  rw [div_le_iff₀ hLp]
  have h := (div_lt_iff₀ hδ).mp hLC
  nlinarith

theorem polarPureLeftContour_integrable (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1/2)
    (hρ : ∀ ij : Fin 2 × Fin 2, ‖purePolarRoot T σ (m,ij)‖ ≤ δ/4) :
    Integrable (fun v : ℝ => polarPoleKiller T σ ((-δ/2:ℝ)+(v:ℂ)*I) *
      purePolarZetaProduct T σ m ((-δ/2:ℝ)+(v:ℂ)*I)) := by
  let M : ℝ := ∑ ij : Fin 2 × Fin 2, |(purePolarRoot T σ (m,ij)).im|
  apply polarPoleKiller_mul_pureZeta_vertical_integrable T σ m (-δ/2)
    (a := 1-3*δ/2) (b := 1-δ/2) (r := δ/2) (M := M)
    (by linarith) (by linarith) (by linarith)
  · intro ij
    dsimp only [M]
    exact Finset.single_le_sum (fun k _ => abs_nonneg ((purePolarRoot T σ (m,k)).im))
      (Finset.mem_univ ij)
  · intro v ij
    have hre : |(purePolarRoot T σ (m,ij)).re| ≤ δ/4 :=
      (Complex.abs_re_le_norm _).trans (hρ ij)
    have he : (1+2*(((-δ/2:ℝ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).re =
        1-δ-2*(purePolarRoot T σ (m,ij)).re := by simp; ring
    have h1 : 1-3*δ/2 ≤ (1+2*(((-δ/2:ℝ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).re := by
      rw [he]
      linarith [(abs_le.mp hre).1, (abs_le.mp hre).2]
    have h2 : (1+2*(((-δ/2:ℝ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).re ≤ 1-δ/2 := by
      rw [he]
      linarith [(abs_le.mp hre).1, (abs_le.mp hre).2]
    refine ⟨h1, h2, ?_⟩
    have hn := Complex.re_le_norm (1-(1+2*(((-δ/2:ℝ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))))
    rw [sub_re, one_re, he] at hn
    linarith

theorem polarPureLeftContour_uniform_eventually_integrable {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1/2) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts, (∀ i : Fin 4, ‖σ i‖ ≤ R) →
      ∀ m : Fin 6, Integrable (fun v : ℝ =>
        polarPoleKiller T σ ((-δ/2:ℝ)+(v:ℂ)*I) *
          purePolarZetaProduct T σ m ((-δ/2:ℝ)+(v:ℂ)*I)) := by
  filter_upwards [purePolarRoot_uniform_eventually_small hR hδ] with T hT σ hσ m
  exact polarPureLeftContour_integrable T σ m hδ hδ1 (fun ij => hT σ hσ (m,ij))

end

end Sechstmoment
