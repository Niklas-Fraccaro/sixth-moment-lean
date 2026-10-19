import Sechstmoment.Numerator.U.Diagonal.ActualProfileMellin

/-! The actual source VStar and the genuine three-variable Mellin Euler integral. -/

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem actualDiagonalMellinKernel_eq_six_source (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (z : ℂ) (x : DiagonalSixIndices) :
    actualDiagonalMellinKernel G α x.val.1.1 x.val.2.1 t (diagonalSixQuad x) z =
      actualDiagonalMellinFactor G 1 1 t z*
        literalDiagonalSixTerm (polarMellinLeftTriple α 0 z) (polarMellinRightTriple α 0 z) x := by
  rw [literalDiagonalSixTerm_eq_sourceDirichlet]
  obtain ⟨hm,_,_,hn,_,_⟩ := diagonalSixIndices_components_ne_zero x
  simp only [shiftedPowerArithmetic, ArithmeticFunction.coe_mk, hm,hn, ite_false,
    neg_zero, Complex.cpow_zero, one_mul]
  unfold actualDiagonalMellinKernel actualDiagonalMellinFactor
  norm_num only [Nat.one_mul,Nat.cast_one,Complex.one_cpow,div_one]
  ring

theorem bblrDiagonalSummand_eq_six_source (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (x : DiagonalSixIndices) :
    bblrDiagonalSummand G α x.val.1.1 x.val.2.1 t (diagonalSixQuad x) =
      verticalIntegral 1 (fun z => actualDiagonalMellinFactor G 1 1 t z*
        literalDiagonalSixTerm (polarMellinLeftTriple α 0 z) (polarMellinRightTriple α 0 z) x) := by
  rw [bblrDiagonalSummand_eq_actualMellin]
  congr 1
  funext z
  exact actualDiagonalMellinKernel_eq_six_source G α t z x

theorem actualDiagonalCommonMellinFactor_integrable {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    Integrable (fun w : ℝ => actualDiagonalMellinFactor G 1 1 t (1+(w:ℂ)*I)) := by
  have hc : Continuous (fun w : ℝ => actualDiagonalMellinFactor G 1 1 t (1+(w:ℂ)*I)) := by
    simpa [actualDiagonalMellinKernel, actualDiagonalQuadDirichletTerm] using
      actualDiagonalMellinKernel_line_continuous ht G
        (continuousOn_univ.mp hG.1.continuousOn) α 1 1 (fun _ => 0)
  apply ((rectangular_BBLR_weight_vertical_integrable G α hG).const_mul
    (actualDiagonalMellinMajorant 1 1 t)).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall (fun w => actualDiagonalMellinFactor_norm_le ht G 1 1 w)

theorem literalDiagonalSixTerm_triple_mellin_continuous (α : MomentShifts) (δ : ℝ)
    (x : DiagonalSixIndices) :
    Continuous (fun w : ℝ × (ℝ × ℝ) => literalDiagonalSixTerm
      (polarMellinLeftTriple α ((δ:ℂ)+(w.2.1:ℂ)*I) (1+(w.1:ℂ)*I))
      (polarMellinRightTriple α ((δ:ℂ)+(w.2.2:ℂ)*I) (1+(w.1:ℂ)*I)) x) := by
  simp_rw [literalDiagonalSixTerm_eq_sourceDirichlet]
  obtain ⟨hm,_,_,hn,_,_⟩ := diagonalSixIndices_components_ne_zero x
  simp only [shiftedPowerArithmetic, ArithmeticFunction.coe_mk, hm,hn, ite_false]
  unfold actualDiagonalQuadDirichletTerm
  apply Continuous.div_const
  apply Continuous.mul
  · apply Continuous.mul
    · apply Continuous.const_cpow (by fun_prop)
      exact Or.inl (by exact_mod_cast hm)
    · apply Continuous.const_cpow (by fun_prop)
      exact Or.inl (by exact_mod_cast hn)
  · apply Continuous.div continuous_const
    · apply continuous_finsetProd
      intro j _
      apply Continuous.const_cpow (by fun_prop)
      exact Or.inl (by exact_mod_cast Nat.succ_ne_zero (diagonalSixQuad x j))
    · intro w
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact Complex.natCast_add_one_cpow_ne_zero (diagonalSixQuad x j) _

def actualTripleMellinTerm (G : ℂ → ℂ) (α : MomentShifts) (f g : ℝ → ℂ)
    (L δ t : ℝ) (x : DiagonalSixIndices) (w : ℝ × (ℝ × ℝ)) : ℂ :=
  actualDiagonalMellinFactor G 1 1 t (1+(w.1:ℂ)*I)*
    (actualProfileTransformLine f L δ w.2.1*actualProfileTransformLine g L δ w.2.2)*
      literalDiagonalSixTerm
        (polarMellinLeftTriple α ((δ:ℂ)+(w.2.1:ℂ)*I) (1+(w.1:ℂ)*I))
        (polarMellinRightTriple α ((δ:ℂ)+(w.2.2:ℂ)*I) (1+(w.1:ℂ)*I)) x

def actualTripleMellinEnvelope (G : ℂ → ℂ) (f g : ℝ → ℂ)
    (L δ t : ℝ) (w : ℝ × (ℝ × ℝ)) : ℝ :=
  actualDiagonalMellinMajorant 1 1 t*‖G (1+(w.1:ℂ)*I)‖*
    (‖actualProfileTransformLine f L δ w.2.1‖*‖actualProfileTransformLine g L δ w.2.2‖)

def actualTripleMellinIndexMajorant (α : MomentShifts) (δ : ℝ) (x : DiagonalSixIndices) : ℝ :=
  ‖literalDiagonalSixTerm
    (polarMellinLeftTriple (fun j => ((α j).re:ℂ)) (δ:ℂ) 1)
    (polarMellinRightTriple (fun j => ((α j).re:ℂ)) (δ:ℂ) 1) x‖

theorem actualTripleMellinTerm_norm_le {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (f g : ℝ → ℂ) (L δ : ℝ)
    (x : DiagonalSixIndices) (w : ℝ × (ℝ × ℝ)) :
    ‖actualTripleMellinTerm G α f g L δ t x w‖ ≤
      actualTripleMellinEnvelope G f g L δ t w*actualTripleMellinIndexMajorant α δ x := by
  unfold actualTripleMellinTerm actualTripleMellinEnvelope actualTripleMellinIndexMajorant
  have hn := literalDiagonalSixTerm_mellin_norm α δ w.2.1 w.2.2 (1+(w.1:ℂ)*I) x
  simp only [show ((1:ℂ)+(w.1:ℂ)*I).re = 1 by simp, Complex.ofReal_one] at hn
  rw [norm_mul,norm_mul,norm_mul,hn]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (actualDiagonalMellinFactor_norm_le ht G 1 1 w.1)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _)

theorem actualTripleMellinEnvelope_integrable (t : ℝ)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L : ℝ} (hL : 0 < L) (δ : ℝ) :
    Integrable (actualTripleMellinEnvelope G f g L δ t) (volume.prod (volume.prod volume)) := by
  have hi := ((rectangular_BBLR_weight_vertical_integrable G α hG).const_mul
      (actualDiagonalMellinMajorant 1 1 t)).mul_prod
    ((actualProfileTransformLine_integrable hf hfs hL δ).norm.mul_prod
      (actualProfileTransformLine_integrable hg hgs hL δ).norm)
  exact hi

theorem actualTripleMellinTerm_integrable {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L : ℝ} (hL : 0 < L) (δ : ℝ) (x : DiagonalSixIndices) :
    Integrable (actualTripleMellinTerm G α f g L δ t x) (volume.prod (volume.prod volume)) := by
  have hi := (actualDiagonalCommonMellinFactor_integrable ht G α hG).mul_prod
    ((actualProfileTransformLine_integrable hf hfs hL δ).mul_prod
      (actualProfileTransformLine_integrable hg hgs hL δ))
  apply ((actualTripleMellinEnvelope_integrable t G α hG hf hfs hg hgs hL δ).mul_const
    (actualTripleMellinIndexMajorant α δ x)).mono'
    (hi.aestronglyMeasurable.mul
      (literalDiagonalSixTerm_triple_mellin_continuous α δ x).aestronglyMeasurable)
  exact Eventually.of_forall (actualTripleMellinTerm_norm_le ht G α f g L δ x)

theorem actualTripleMellinTerm_integral_source {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L : ℝ} (hL : 0 < L) (δ : ℝ) (x : DiagonalSixIndices) :
    (1/(2*π):ℂ)*((L:ℂ)/(2*π))^2*
      (∫ w : ℝ × (ℝ × ℝ), actualTripleMellinTerm G α f g L δ t x w
        ∂(volume.prod (volume.prod volume))) =
      f (Real.log x.val.1.1/L)*g (Real.log x.val.2.1/L)*
        bblrDiagonalSummand G α x.val.1.1 x.val.2.1 t (diagonalSixQuad x) := by
  have hi := actualTripleMellinTerm_integrable ht G α hG hf hfs hg hgs hL δ x
  rw [integral_prod _ hi]
  have hinner (s : ℝ) : ((L:ℂ)/(2*π))^2*
      (∫ y : ℝ × ℝ, actualTripleMellinTerm G α f g L δ t x (s,y) ∂(volume.prod volume)) =
      actualDiagonalMellinFactor G 1 1 t (1+(s:ℂ)*I)*
        (f (Real.log x.val.1.1/L)*g (Real.log x.val.2.1/L)*
          literalDiagonalSixTerm
            (polarMellinLeftTriple α 0 (1+(s:ℂ)*I))
            (polarMellinRightTriple α 0 (1+(s:ℂ)*I)) x) := by
    have he : (∫ y : ℝ × ℝ, actualTripleMellinTerm G α f g L δ t x (s,y) ∂(volume.prod volume)) =
        actualDiagonalMellinFactor G 1 1 t (1+(s:ℂ)*I)*
          ∫ y : ℝ × ℝ,
            actualProfileTransformLine f L δ y.1*actualProfileTransformLine g L δ y.2*
              literalDiagonalSixTerm
                (polarMellinLeftTriple α ((δ:ℂ)+(y.1:ℂ)*I) (1+(s:ℂ)*I))
                (polarMellinRightTriple α ((δ:ℂ)+(y.2:ℂ)*I) (1+(s:ℂ)*I)) x
            ∂(volume.prod volume) := by
      unfold actualTripleMellinTerm
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    rw [he, ← mul_assoc, mul_comm (((L:ℂ)/(2*π))^2), mul_assoc,
      literalDiagonalSixTerm_profile_integral hf hfs hg hgs hL]
  rw [mul_assoc, ← integral_const_mul]
  simp_rw [hinner]
  rw [bblrDiagonalSummand_eq_six_source]
  unfold verticalIntegral
  dsimp only
  simp only [Complex.ofReal_one]
  have he : (∫ s : ℝ, actualDiagonalMellinFactor G 1 1 t (1+(s:ℂ)*I)*
      (f (Real.log x.val.1.1/L)*g (Real.log x.val.2.1/L)*
        literalDiagonalSixTerm (polarMellinLeftTriple α 0 (1+(s:ℂ)*I))
          (polarMellinRightTriple α 0 (1+(s:ℂ)*I)) x)) =
      (f (Real.log x.val.1.1/L)*g (Real.log x.val.2.1/L))*
        ∫ s : ℝ, actualDiagonalMellinFactor G 1 1 t (1+(s:ℂ)*I)*
          literalDiagonalSixTerm (polarMellinLeftTriple α 0 (1+(s:ℂ)*I))
            (polarMellinRightTriple α 0 (1+(s:ℂ)*I)) x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with s
    ring
  rw [he]
  ring

def actualTripleMellinEulerKernel (G : ℂ → ℂ) (α : MomentShifts) (f g : ℝ → ℂ)
    (L δ t : ℝ) (w : ℝ × (ℝ × ℝ)) : ℂ :=
  actualDiagonalMellinFactor G 1 1 t (1+(w.1:ℂ)*I)*
    (actualProfileTransformLine f L δ w.2.1*actualProfileTransformLine g L δ w.2.2)*
      ((∏ ij : Fin 3 × Fin 3, riemannZeta (1+
        polarMellinLeftTriple α ((δ:ℂ)+(w.2.1:ℂ)*I) (1+(w.1:ℂ)*I) ij.1+
        polarMellinRightTriple α ((δ:ℂ)+(w.2.2:ℂ)*I) (1+(w.1:ℂ)*I) ij.2))*
        shiftedPolarEulerRest
          (polarMellinLeftTriple α ((δ:ℂ)+(w.2.1:ℂ)*I) (1+(w.1:ℂ)*I))
          (polarMellinRightTriple α ((δ:ℂ)+(w.2.2:ℂ)*I) (1+(w.1:ℂ)*I)))

theorem actualSourceSixDiagonal_MellinEuler_hasSum {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4) :
    HasSum (fun x : DiagonalSixIndices =>
      f (Real.log x.val.1.1/L)*g (Real.log x.val.2.1/L)*
        bblrDiagonalSummand G α x.val.1.1 x.val.2.1 t (diagonalSixQuad x))
      ((1/(2*π):ℂ)*((L:ℂ)/(2*π))^2*
        ∫ w : ℝ × (ℝ × ℝ), actualTripleMellinEulerKernel G α f g L δ t w
          ∂(volume.prod (volume.prod volume))) := by
  let B := actualTripleMellinIndexMajorant α δ
  have hB : Summable B :=
    literalDiagonalSixTerm_initial_mellin_majorant_summable hδ hα (z := 1) (by simpa using hδ1)
  have hbase := (actualDiagonalCommonMellinFactor_integrable ht G α hG).mul_prod
    ((actualProfileTransformLine_integrable hf hfs hL δ).mul_prod
      (actualProfileTransformLine_integrable hg hgs hL δ))
  have hs : HasSum (fun x : DiagonalSixIndices =>
      ∫ w : ℝ × (ℝ × ℝ), actualTripleMellinTerm G α f g L δ t x w
        ∂(volume.prod (volume.prod volume)))
      (∫ w : ℝ × (ℝ × ℝ), actualDiagonalMellinFactor G 1 1 t (1+(w.1:ℂ)*I)*
        (actualProfileTransformLine f L δ w.2.1*actualProfileTransformLine g L δ w.2.2)*
          ∑' x : DiagonalSixIndices, literalDiagonalSixTerm
            (polarMellinLeftTriple α ((δ:ℂ)+(w.2.1:ℂ)*I) (1+(w.1:ℂ)*I))
            (polarMellinRightTriple α ((δ:ℂ)+(w.2.2:ℂ)*I) (1+(w.1:ℂ)*I)) x
        ∂(volume.prod (volume.prod volume))) := by
    apply hasSum_integral_of_dominated_convergence (fun x (w : ℝ × (ℝ × ℝ)) =>
      actualTripleMellinEnvelope G f g L δ t w*B x)
    · intro x
      exact hbase.aestronglyMeasurable.mul
        (literalDiagonalSixTerm_triple_mellin_continuous α δ x).aestronglyMeasurable
    · intro x
      exact Eventually.of_forall (actualTripleMellinTerm_norm_le ht G α f g L δ x)
    · exact Eventually.of_forall (fun w => hB.mul_left _)
    · simp_rw [tsum_mul_left]
      exact (actualTripleMellinEnvelope_integrable t G α hG hf hfs hg hgs hL δ).mul_const _
    · filter_upwards [] with w
      have hn (x : DiagonalSixIndices) :
          ‖literalDiagonalSixTerm
            (polarMellinLeftTriple α ((δ:ℂ)+(w.2.1:ℂ)*I) (1+(w.1:ℂ)*I))
            (polarMellinRightTriple α ((δ:ℂ)+(w.2.2:ℂ)*I) (1+(w.1:ℂ)*I)) x‖ = B x := by
        have he := literalDiagonalSixTerm_mellin_norm α δ w.2.1 w.2.2 (1+(w.1:ℂ)*I) x
        simpa only [B,actualTripleMellinIndexMajorant,
          show ((1:ℂ)+(w.1:ℂ)*I).re = 1 by simp, Complex.ofReal_one] using he
      have hraw := (hB.congr (fun x => (hn x).symm)).of_norm
      exact hraw.hasSum.mul_left
        (actualDiagonalMellinFactor G 1 1 t (1+(w.1:ℂ)*I)*
          (actualProfileTransformLine f L δ w.2.1*actualProfileTransformLine g L δ w.2.2))
  have hsum := (hs.mul_left ((1/(2*π):ℂ)*((L:ℂ)/(2*π))^2)).congr_fun
    (fun x => (actualTripleMellinTerm_integral_source ht G α hG hf hfs hg hgs hL δ x).symm)
  convert hsum using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with w
  obtain ⟨ha,hb⟩ := polarMellinTriples_initial_re_lower_bound hδ hα
    (u := (δ:ℂ)+(w.2.1:ℂ)*I) (v := (δ:ℂ)+(w.2.2:ℂ)*I)
    (z := 1+(w.1:ℂ)*I) (by simp) (by simp) (by simpa using hδ1)
  rw [literalDiagonalSixTerm_eq_zetaProduct_mul_rest (by linarith : 0 < δ/2) ha hb]
  rfl

theorem actualSourceSixDiagonal_eq_MellinEuler {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4) :
    (∑' x : DiagonalSixIndices,
      f (Real.log x.val.1.1/L)*g (Real.log x.val.2.1/L)*
        bblrDiagonalSummand G α x.val.1.1 x.val.2.1 t (diagonalSixQuad x)) =
      (1/(2*π):ℂ)*((L:ℂ)/(2*π))^2*
        ∫ w : ℝ × (ℝ × ℝ), actualTripleMellinEulerKernel G α f g L δ t w
          ∂(volume.prod (volume.prod volume)) :=
  (actualSourceSixDiagonal_MellinEuler_hasSum ht G α hG hf hfs hg hgs hL hδ hδ1 hα).tsum_eq

theorem actualSourceSixDiagonal_norm_summable {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4) :
    Summable (fun x : DiagonalSixIndices =>
      ‖f (Real.log x.val.1.1/L)*g (Real.log x.val.2.1/L)*
        bblrDiagonalSummand G α x.val.1.1 x.val.2.1 t (diagonalSixQuad x)‖) :=
  (actualSourceSixDiagonal_MellinEuler_hasSum ht G α hG hf hfs hg hgs hL hδ hδ1 hα).summable.norm

end
end Sechstmoment
