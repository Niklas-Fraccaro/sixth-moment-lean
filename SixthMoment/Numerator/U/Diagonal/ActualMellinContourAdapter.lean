import SixthMoment.Numerator.Polar.ContourShift
import SixthMoment.Numerator.U.Diagonal.ActualSixMainMellin
import SixthMoment.Numerator.U.Replacement.CentralContourShift


namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

def actualMellinEulerVerticalKernel (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (u v z : ℂ) : ℂ :=
  actualDiagonalMellinFactor G 1 1 t z*
    ((∏ ij : Fin 3 × Fin 3, riemannZeta (1+polarMellinLeftTriple α u z ij.1+
      polarMellinRightTriple α v z ij.2))*
      shiftedPolarEulerRest (polarMellinLeftTriple α u z) (polarMellinRightTriple α v z))

theorem actualTripleMellinEulerKernel_eq_profile_mul_vertical
    (G : ℂ → ℂ) (α : MomentShifts) (f g : ℝ → ℂ) (L δ t : ℝ)
    (w : ℝ × (ℝ × ℝ)) : actualTripleMellinEulerKernel G α f g L δ t w =
      (actualProfileTransformLine f L δ w.2.1*actualProfileTransformLine g L δ w.2.2)*
        actualMellinEulerVerticalKernel G α t ((δ:ℂ)+(w.2.1:ℂ)*I)
          ((δ:ℂ)+(w.2.2:ℂ)*I) (1+(w.1:ℂ)*I) := by
  unfold actualTripleMellinEulerKernel actualMellinEulerVerticalKernel
  ring

theorem actualTripleMellinEulerKernel_integrable {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4) :
    Integrable (actualTripleMellinEulerKernel G α f g L δ t)
      (volume.prod (volume.prod volume)) := by
  let B := actualTripleMellinIndexMajorant α δ
  let S : ℝ × (ℝ × ℝ) → ℂ := fun w => ∑' x : DiagonalSixIndices,
    literalDiagonalSixTerm
      (polarMellinLeftTriple α ((δ:ℂ)+(w.2.1:ℂ)*I) (1+(w.1:ℂ)*I))
      (polarMellinRightTriple α ((δ:ℂ)+(w.2.2:ℂ)*I) (1+(w.1:ℂ)*I)) x
  have hB : Summable B :=
    literalDiagonalSixTerm_initial_mellin_majorant_summable hδ hα (z := 1) (by simpa using hδ1)
  have hn (w : ℝ × (ℝ × ℝ)) (x : DiagonalSixIndices) :
      ‖literalDiagonalSixTerm
        (polarMellinLeftTriple α ((δ:ℂ)+(w.2.1:ℂ)*I) (1+(w.1:ℂ)*I))
        (polarMellinRightTriple α ((δ:ℂ)+(w.2.2:ℂ)*I) (1+(w.1:ℂ)*I)) x‖ = B x := by
    simpa only [B,actualTripleMellinIndexMajorant,
      show ((1:ℂ)+(w.1:ℂ)*I).re=1 by simp,Complex.ofReal_one] using
        literalDiagonalSixTerm_mellin_norm α δ w.2.1 w.2.2 (1+(w.1:ℂ)*I) x
  have hS : Continuous S := by
    apply continuous_tsum (u := B)
    · exact literalDiagonalSixTerm_triple_mellin_continuous α δ
    · exact hB
    · exact fun x w => (hn w x).le
  have hSnorm (w : ℝ × (ℝ × ℝ)) : ‖S w‖ ≤ ∑' x : DiagonalSixIndices, B x := by
    have hs := hB.congr (fun x => (hn w x).symm)
    exact (norm_tsum_le_tsum_norm hs).trans_eq (tsum_congr (hn w))
  have heq : actualTripleMellinEulerKernel G α f g L δ t = fun w =>
      actualDiagonalMellinFactor G 1 1 t (1+(w.1:ℂ)*I)*
        (actualProfileTransformLine f L δ w.2.1*actualProfileTransformLine g L δ w.2.2)*S w := by
    funext w
    obtain ⟨ha,hb⟩ := polarMellinTriples_initial_re_lower_bound hδ hα
      (u := (δ:ℂ)+(w.2.1:ℂ)*I) (v := (δ:ℂ)+(w.2.2:ℂ)*I)
      (z := 1+(w.1:ℂ)*I) (by simp) (by simp) (by simpa using hδ1)
    dsimp [S,actualTripleMellinEulerKernel]
    rw [literalDiagonalSixTerm_eq_zetaProduct_mul_rest (by linarith : 0 < δ/2) ha hb]
  rw [heq]
  have hi := (actualDiagonalCommonMellinFactor_integrable ht G α hG).mul_prod
    ((actualProfileTransformLine_integrable hf hfs hL δ).mul_prod
      (actualProfileTransformLine_integrable hg hgs hL δ))
  apply ((actualTripleMellinEnvelope_integrable t G α hG hf hfs hg hgs hL δ).mul_const
    (∑' x : DiagonalSixIndices, B x)).mono' (hi.aestronglyMeasurable.mul hS.aestronglyMeasurable)
  filter_upwards [] with w
  have hc : ‖actualDiagonalMellinFactor G 1 1 t (1+(w.1:ℂ)*I)*
      (actualProfileTransformLine f L δ w.2.1*actualProfileTransformLine g L δ w.2.2)‖ ≤
        actualTripleMellinEnvelope G f g L δ t w := by
    dsimp [actualTripleMellinEnvelope]
    rw [norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_right (actualDiagonalMellinFactor_norm_le ht G 1 1 w.1)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_mul hc (hSnorm w) (norm_nonneg _) ((norm_nonneg _).trans hc)

theorem actualMellinEuler_integral_eq_profiles_vertical {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4) :
    (1/(2*π):ℂ)*((L:ℂ)/(2*π))^2*
      (∫ w : ℝ × (ℝ × ℝ), actualTripleMellinEulerKernel G α f g L δ t w
        ∂(volume.prod (volume.prod volume))) =
      ((L:ℂ)/(2*π))^2*∫ y : ℝ × ℝ,
        (actualProfileTransformLine f L δ y.1*actualProfileTransformLine g L δ y.2)*
          verticalIntegral 1 (actualMellinEulerVerticalKernel G α t
            ((δ:ℂ)+(y.1:ℂ)*I) ((δ:ℂ)+(y.2:ℂ)*I)) ∂(volume.prod volume) := by
  have hi := actualTripleMellinEulerKernel_integrable ht G α hG hf hfs hg hgs hL hδ hδ1 hα
  rw [integral_prod_symm _ hi]
  have hinner (y : ℝ × ℝ) : (∫ s : ℝ, actualTripleMellinEulerKernel G α f g L δ t (s,y)) =
      (actualProfileTransformLine f L δ y.1*actualProfileTransformLine g L δ y.2)*
        ∫ s : ℝ, actualMellinEulerVerticalKernel G α t ((δ:ℂ)+(y.1:ℂ)*I)
          ((δ:ℂ)+(y.2:ℂ)*I) (1+(s:ℂ)*I) := by
    simp_rw [actualTripleMellinEulerKernel_eq_profile_mul_vertical]
    exact integral_const_mul _ _
  simp_rw [hinner]
  unfold verticalIntegral
  simp only [Complex.ofReal_one]
  rw [← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring


theorem actualDiagonalMellinFactor_eq_scale {t : ℝ} (ht : 0 < t)
    (G : ℂ → ℂ) (z : ℂ) : actualDiagonalMellinFactor G 1 1 t z =
      G z/z*((t/(2*π):ℝ):ℂ)^(2*z) := by
  have hp : (t:ℂ)^(2*z)=((t^2:ℝ):ℂ)^z := by
    simpa only [Complex.ofReal_ofNat,Real.rpow_two] using
      Complex.cpow_mul_ofReal_nonneg ht.le (2:ℝ) z
  have hs : ((t/(2*π):ℝ):ℂ)^(2*z)=
      ((t^2:ℝ):ℂ)^z/(2*π:ℂ)^(2*z) := by
    rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg ht.le (by positivity)]
    simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,hp]
  unfold actualDiagonalMellinFactor
  norm_num only [Nat.one_mul,Nat.cast_one,Complex.one_cpow,div_one]
  rw [hs,show -2*z=-(2*z) by ring,Complex.cpow_neg]
  ring

theorem actualMellinEulerVerticalKernel_eq_polarMellinWeightedKernel
    {t : ℝ} (ht : 0 < t) (T : ℝ) (σ : MomentShifts) (m : Fin 6) (u v z : ℂ) :
    actualMellinEulerVerticalKernel (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) m)
      t u v z = polarMellinWeightedKernel T σ m u v (t/(2*π)) z := by
  unfold actualMellinEulerVerticalKernel
  rw [actualDiagonalMellinFactor_eq_scale ht,
    polarNineZetaProduct_eq_entangled_mul_pure]
  unfold polarMellinWeightedKernel polarMellinArithmeticKernel polarArithmeticEntangledFactor
  ring


theorem actualAmplifiedDiagonal_eq_shiftedProfiles {t L δ : ℝ}
    (ht : 0 < t) (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ < 1/4)
    (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hρ : ∀ ij : Fin 2 × Fin 2, purePolarRoot T σ (m,ij) ≠ 0)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    (∑' p : ActualPositiveAmplifierIndex × ActualPositiveAmplifierIndex,
      f (Real.log p.1.val/L)*g (Real.log p.2.val/L)*
        bblrDiagonalTerm (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) m)
          p.1.val p.2.val t) =
      ((L:ℂ)/(2*π))^2*∫ y : ℝ × ℝ,
        (actualProfileTransformLine f L δ y.1*actualProfileTransformLine g L δ y.2)*
          (polarMellinRemovedKernel T σ m ((δ:ℂ)+(y.1:ℂ)*I) ((δ:ℂ)+(y.2:ℂ)*I) 0+
            polarMellinRemainderIntegral T σ m ((δ:ℂ)+(y.1:ℂ)*I)
              ((δ:ℂ)+(y.2:ℂ)*I) (t/(2*π)) δ) ∂(volume.prod volume) := by
  have hshift : ∀ j : Fin 4, ‖bblrSixShifts (rawMomentShifts T σ) m j‖ ≤ δ/4 :=
    bblrSixShifts_norm_le _ hα m
  have hG := polarPoleKiller_BBLREntireWeight T σ (bblrSixShifts (rawMomentShifts T σ) m)
  have hδle : δ ≤ 1 := by linarith
  rw [actualAmplifiedDiagonal_eq_MellinEuler ht.ne' _ _ hG hf hfs hg hgs hL hδ hδle hshift,
    actualMellinEuler_integral_eq_profiles_vertical ht.ne' _ _ hG hf hfs hg hgs hL hδ hδle hshift]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  have heq : actualMellinEulerVerticalKernel (polarPoleKiller T σ)
      (bblrSixShifts (rawMomentShifts T σ) m) t ((δ:ℂ)+(y.1:ℂ)*I) ((δ:ℂ)+(y.2:ℂ)*I) =
      polarMellinWeightedKernel T σ m ((δ:ℂ)+(y.1:ℂ)*I) ((δ:ℂ)+(y.2:ℂ)*I) (t/(2*π)) :=
    funext (fun z => actualMellinEulerVerticalKernel_eq_polarMellinWeightedKernel ht T σ m _ _ z)
  rw [heq]
  exact polarMellinWeightedKernel_contour_shift T σ m hδ hδ1 (div_pos ht (by positivity))
    hα (by simp) (by simp) hρ

end
end SixthMoment
