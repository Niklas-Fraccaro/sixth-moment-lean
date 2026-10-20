import Sechstmoment.Numerator.U.MainTerm.MovingPolarFactors
import Sechstmoment.Numerator.U.MainTerm.PrincipalDominatedLimit


namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem principalNormalizedPureZetaProduct_uniform_eventually_bounded
    {R κ : ℝ} (_hR : 0 ≤ R) (hκ : 0 < κ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ L : ℝ in atTop,
      ∀ α : MomentShifts, (∀ j : Fin 4, ‖α j‖ ≤ R) →
      (∀ ij : Fin 2 × Fin 2, 2*κ ≤ ‖principalNormalizedPureArgument α ij‖) →
      ‖principalNormalizedPureZetaProduct L α‖ ≤ B := by
  let K : Set ℂ := {w | ‖w‖ ≤ 2*R ∧ 2*κ ≤ ‖w‖}
  have hball : Bornology.IsBounded (Metric.closedBall (0:ℂ) (2*R)) :=
    (isCompact_closedBall (0:ℂ) (2*R)).isBounded
  have hKb : Bornology.IsBounded K :=
    hball.subset (by
      intro w hw
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1)
  have hu := (Metric.tendstoUniformlyOn_iff.mp
    (scaled_riemannZeta_uniform hKb (show 0 < 2*κ by positivity)
      (fun _ hw => hw.2))) 1 (by norm_num)
  refine ⟨(1/(2*κ)+1)^4, by positivity, ?_⟩
  filter_upwards [hu] with L hL α hα hgap
  unfold principalNormalizedPureZetaProduct
  calc
    _ ≤ ∏ ij : Fin 2 × Fin 2,
        ‖riemannZeta (1+principalNormalizedPureArgument α ij/(L:ℂ))/(L:ℂ)‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ _ij : Fin 2 × Fin 2, (1/(2*κ)+1) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro ij _
      let w := principalNormalizedPureArgument α ij
      have hwK : w ∈ K := by
        refine ⟨?_, hgap ij⟩
        have hh := (norm_add_le (α (purePolarLeft ij.1))
          (α (purePolarRight ij.2))).trans (add_le_add
            (hα (purePolarLeft ij.1)) (hα (purePolarRight ij.2)))
        change ‖α (purePolarLeft ij.1)+α (purePolarRight ij.2)‖ ≤ 2*R
        linarith
      have hi : ‖1/w‖ ≤ 1/(2*κ) := by
        rw [norm_div, norm_one]
        exact one_div_le_one_div_of_le (by positivity) hwK.2
      have hz := hL w hwK
      have hn := norm_le_norm_sub_add
        (riemannZeta (1+w/(L:ℂ))/(L:ℂ)) (1/w)
      rw [← dist_eq_norm, dist_comm] at hn
      exact (hn.trans (add_le_add hz.le hi)).trans (by ring_nf; rfl)
    _ = _ := by simp [Fintype.card_prod]

theorem normalizedPurePolarRoot_norm_eq (σ : MomentShifts) (m : Fin 6)
    (ij : Fin 2 × Fin 2) :
    ‖normalizedPurePolarRoot σ (m,ij)‖ =
      ‖principalNormalizedPureArgument (bblrSixShifts σ m) ij‖/2 := by
  simp only [normalizedPurePolarRoot, principalNormalizedPureArgument,
    norm_div, norm_neg]
  norm_num

theorem actualPrincipalProfileRescaledKernel_uniform_eventually_dominated
    {R c κ : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c) (hκ : 0 < κ)
    (f g : ℝ → ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      (∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖) →
      ∀ (m : Fin 6) (y : ℝ × ℝ),
        ‖actualPrincipalProfileRescaledKernel T σ m f g (Real.log T) c c y/
          (Real.log T:ℂ)^9‖ ≤
        C*(‖profileLaplaceTransform f ((c:ℂ)+(y.1:ℂ)*I)‖*
          ‖profileLaplaceTransform g ((c:ℂ)+(y.2:ℂ)*I)‖) := by
  have hc1 : R+1 ≤ c := by linarith
  have hcp : 0 < c := by linarith
  obtain ⟨B,hB,hpure⟩ :=
    principalNormalizedPureZetaProduct_uniform_eventually_bounded hR hκ
  let A : ℝ := Real.exp
    (∑' p : {n : ℕ // Nat.Prime n}, shiftedPolarPrimeUniformMajorant (1/8) p)
  have hA : 0 < A := Real.exp_pos _
  refine ⟨A*(2:ℝ)^5*B,by positivity,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hpure,
    eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/32)]
    with T hpure hT hL hraw σ hσ hgap m y
  let α := bblrSixShifts σ m
  have hα (j : Fin 4) : ‖α j‖ ≤ R := bblrSixShifts_norm_le σ hσ m j
  have hρ (ij : Fin 2 × Fin 2) : normalizedPurePolarRoot σ (m,ij) ≠ 0 :=
    norm_pos_iff.mp (hκ.trans_le (hgap (m,ij)))
  have hpure' : ‖principalNormalizedPureZetaProduct (Real.log T) α‖ ≤ B := by
    apply hpure α hα
    intro ij
    have hh := hgap (m,ij)
    rw [normalizedPurePolarRoot_norm_eq] at hh
    linarith
  have hLp : 0 < Real.log T := Real.log_pos hT
  have hroot (ij : Fin 2 × Fin 2) : purePolarRoot T σ (m,ij) ≠ 0 := by
    rw [purePolarRoot_normalized]
    exact div_ne_zero (hρ ij) (Complex.ofReal_ne_zero.mpr hLp.ne')
  let u : ℂ := (c:ℂ)+(y.1:ℂ)*I
  let v : ℂ := (c:ℂ)+(y.2:ℂ)*I
  have hE : ‖shiftedPolarEulerRest
      (fun i => polarLeftArguments u 0 α i/(Real.log T:ℂ))
      (fun i => polarRightArguments v 0 α i/(Real.log T:ℂ))‖ ≤ A := by
    apply shiftedPolarEulerRest_norm_uniform_bound _ _ (by norm_num : (1/8:ℝ)<1/4)
    · intro i
      fin_cases i
      · simpa [polarLeftArguments,u] using
          (show -(1/8:ℝ) ≤ c/Real.log T by
            have hp := div_nonneg hcp.le hLp.le
            linarith)
      · have hh := bblrSixShifts_norm_le _ (hraw σ hσ) m 0
        rw [bblrSixShifts_rawMomentShifts] at hh
        have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hh)).1
        simpa [polarLeftArguments,α] using (show -(1/8:ℝ) ≤
          (bblrSixShifts σ m 0/(Real.log T:ℂ)).re by linarith)
      · have hh := bblrSixShifts_norm_le _ (hraw σ hσ) m 1
        rw [bblrSixShifts_rawMomentShifts] at hh
        have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hh)).1
        simpa [polarLeftArguments,α] using (show -(1/8:ℝ) ≤
          (bblrSixShifts σ m 1/(Real.log T:ℂ)).re by linarith)
    · intro i
      fin_cases i
      · simpa [polarRightArguments,v] using
          (show -(1/8:ℝ) ≤ c/Real.log T by
            have hp := div_nonneg hcp.le hLp.le
            linarith)
      · have hh := bblrSixShifts_norm_le _ (hraw σ hσ) m 2
        rw [bblrSixShifts_rawMomentShifts] at hh
        have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hh)).1
        simpa [polarRightArguments,α] using (show -(1/8:ℝ) ≤
          (bblrSixShifts σ m 2/(Real.log T:ℂ)).re by linarith)
      · have hh := bblrSixShifts_norm_le _ (hraw σ hσ) m 3
        rw [bblrSixShifts_rawMomentShifts] at hh
        have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hh)).1
        simpa [polarRightArguments,α] using (show -(1/8:ℝ) ≤
          (bblrSixShifts σ m 3/(Real.log T:ℂ)).re by linarith)
  have hZ := principalNormalizedEntangledZetaProduct_norm_bound hL hR hc1 α hα y
  dsimp [actualPrincipalProfileRescaledKernel]
  rw [mul_div_assoc,polarMellinRemovedKernel_principal_scaled_identity T σ m _ _ hroot,
    ninePolarZetaFactor_zero_eq_normalized_split,norm_mul,norm_mul,norm_mul,norm_mul]
  change (‖profileLaplaceTransform f u‖*‖profileLaplaceTransform g v‖)*
    (‖shiftedPolarEulerRest _ _‖*(‖principalNormalizedEntangledZetaProduct (Real.log T) α u v‖*
      ‖principalNormalizedPureZetaProduct (Real.log T) α‖)) ≤ _
  calc
    _ ≤ (‖profileLaplaceTransform f u‖*‖profileLaplaceTransform g v‖)*(A*((2:ℝ)^5*B)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hE (mul_le_mul hZ hpure' (norm_nonneg _) (by positivity))
        (by positivity) hA.le
    _ = _ := by dsimp [u,v]; ring

end
end Sechstmoment
