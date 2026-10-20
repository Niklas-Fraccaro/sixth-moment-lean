import Mathlib.MeasureTheory.Integral.Prod
import Sechstmoment.Numerator.U.Diagonal.ActualSixPowers


namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

def actualProfileTransformLine (f : ℝ → ℂ) (L δ y : ℝ) : ℂ :=
  profileLaplaceTransform f ((L:ℂ)*((δ:ℂ)+(y:ℂ)*I))

theorem actualProfileTransformLine_integrable {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) {L : ℝ} (hL : 0 < L) (δ : ℝ) :
    Integrable (actualProfileTransformLine f L δ) := by
  have hi := profileLaplaceTransform_verticalIntegrable hf hs (L*δ)
  change Integrable (fun y : ℝ => profileLaplaceTransform f ((L*δ:ℝ)+(y:ℂ)*I)) at hi
  have hscale := hi.comp_mul_left' hL.ne'
  convert hscale using 1
  funext y
  unfold actualProfileTransformLine
  congr 1
  push_cast
  ring

theorem literalDiagonalSixTerm_amplifier_factorization (α : MomentShifts)
    (u v z : ℂ) (x : DiagonalSixIndices) :
    literalDiagonalSixTerm (polarMellinLeftTriple α u z) (polarMellinRightTriple α v z) x =
      shiftedPowerArithmetic u x.val.1.1*shiftedPowerArithmetic v x.val.2.1*
        literalDiagonalSixTerm (polarMellinLeftTriple α 0 z) (polarMellinRightTriple α 0 z) x := by
  obtain ⟨hm,_,_,hn,_,_⟩ := diagonalSixIndices_components_ne_zero x
  rw [literalDiagonalSixTerm_eq_sourceDirichlet, literalDiagonalSixTerm_eq_sourceDirichlet]
  simp only [shiftedPowerArithmetic, ArithmeticFunction.coe_mk, hm,hn, ite_false,
    neg_zero, Complex.cpow_zero, one_mul, div_eq_mul_inv]
  ring

theorem literalDiagonalSixTerm_mellin_norm (α : MomentShifts) (δ y w : ℝ)
    (z : ℂ) (x : DiagonalSixIndices) :
    ‖literalDiagonalSixTerm
      (polarMellinLeftTriple α ((δ:ℂ)+(y:ℂ)*I) z)
      (polarMellinRightTriple α ((δ:ℂ)+(w:ℂ)*I) z) x‖ =
      ‖literalDiagonalSixTerm
        (polarMellinLeftTriple (fun j => ((α j).re:ℂ)) (δ:ℂ) (z.re:ℂ))
        (polarMellinRightTriple (fun j => ((α j).re:ℂ)) (δ:ℂ) (z.re:ℂ)) x‖ := by
  have ha : (fun i => ((polarMellinLeftTriple α ((δ:ℂ)+(y:ℂ)*I) z i).re:ℂ)) =
      polarMellinLeftTriple (fun j => ((α j).re:ℂ)) (δ:ℂ) (z.re:ℂ) := by
    funext i
    fin_cases i <;> simp [polarMellinLeftTriple]
  have hb : (fun i => ((polarMellinRightTriple α ((δ:ℂ)+(w:ℂ)*I) z i).re:ℂ)) =
      polarMellinRightTriple (fun j => ((α j).re:ℂ)) (δ:ℂ) (z.re:ℂ) := by
    funext i
    fin_cases i <;> simp [polarMellinRightTriple]
  rw [← ha, ← hb, literalDiagonalSixTerm_re_eq_norm, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _)]

theorem literalDiagonalSixTerm_initial_mellin_majorant_summable {α : MomentShifts}
    {δ : ℝ} {z : ℂ} (hδ : 0 < δ) (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4)
    (hz : δ ≤ z.re) :
    Summable (fun x : DiagonalSixIndices =>
      ‖literalDiagonalSixTerm
        (polarMellinLeftTriple (fun j => ((α j).re:ℂ)) (δ:ℂ) (z.re:ℂ))
        (polarMellinRightTriple (fun j => ((α j).re:ℂ)) (δ:ℂ) (z.re:ℂ)) x‖) := by
  have hα' (j : Fin 4) : ‖((α j).re:ℂ)‖ ≤ δ/4 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (Complex.abs_re_le_norm (α j)).trans (hα j)
  obtain ⟨ha,hb⟩ := polarMellinTriples_initial_re_lower_bound hδ hα'
    (u := (δ:ℂ)) (v := (δ:ℂ)) (z := (z.re:ℂ)) (by simp) (by simp) (by simpa using hz)
  exact literalDiagonalSixTerm_norm_summable (by linarith : 0 < δ/2) ha hb

theorem literalDiagonalSixTerm_mellin_continuous (α : MomentShifts) (δ : ℝ)
    (z : ℂ) (x : DiagonalSixIndices) :
    Continuous (fun y : ℝ × ℝ => literalDiagonalSixTerm
      (polarMellinLeftTriple α ((δ:ℂ)+(y.1:ℂ)*I) z)
      (polarMellinRightTriple α ((δ:ℂ)+(y.2:ℂ)*I) z) x) := by
  have he : (fun y : ℝ × ℝ => literalDiagonalSixTerm
      (polarMellinLeftTriple α ((δ:ℂ)+(y.1:ℂ)*I) z)
      (polarMellinRightTriple α ((δ:ℂ)+(y.2:ℂ)*I) z) x) =
      (fun y : ℝ × ℝ => shiftedPowerArithmetic ((δ:ℂ)+(y.1:ℂ)*I) x.val.1.1*
        shiftedPowerArithmetic ((δ:ℂ)+(y.2:ℂ)*I) x.val.2.1*
        literalDiagonalSixTerm (polarMellinLeftTriple α 0 z) (polarMellinRightTriple α 0 z) x) :=
    funext (fun _ => literalDiagonalSixTerm_amplifier_factorization α _ _ z x)
  rw [he]
  obtain ⟨hm,_,_,hn,_,_⟩ := diagonalSixIndices_components_ne_zero x
  simp only [shiftedPowerArithmetic, ArithmeticFunction.coe_mk, hm,hn, ite_false]
  apply Continuous.mul_const
  apply Continuous.mul
  · apply Continuous.const_cpow (by fun_prop)
    exact Or.inl (by exact_mod_cast hm)
  · apply Continuous.const_cpow (by fun_prop)
    exact Or.inl (by exact_mod_cast hn)

theorem literalDiagonalSixTerm_profile_integral {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L : ℝ} (hL : 0 < L) (α : MomentShifts) (δ : ℝ) (z : ℂ) (x : DiagonalSixIndices) :
    ((L:ℂ)/(2*π))^2 *
      (∫ y : ℝ × ℝ,
        actualProfileTransformLine f L δ y.1*actualProfileTransformLine g L δ y.2*
          literalDiagonalSixTerm
            (polarMellinLeftTriple α ((δ:ℂ)+(y.1:ℂ)*I) z)
            (polarMellinRightTriple α ((δ:ℂ)+(y.2:ℂ)*I) z) x
        ∂(volume.prod volume)) =
      f (Real.log x.val.1.1/L)*g (Real.log x.val.2.1/L)*
        literalDiagonalSixTerm (polarMellinLeftTriple α 0 z) (polarMellinRightTriple α 0 z) x := by
  obtain ⟨hm,_,_,hn,_,_⟩ := diagonalSixIndices_components_ne_zero x
  have hmR : (0:ℝ) < x.val.1.1 := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hnR : (0:ℝ) < x.val.2.1 := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hi : (∫ y : ℝ × ℝ,
      actualProfileTransformLine f L δ y.1*actualProfileTransformLine g L δ y.2*
        literalDiagonalSixTerm
          (polarMellinLeftTriple α ((δ:ℂ)+(y.1:ℂ)*I) z)
          (polarMellinRightTriple α ((δ:ℂ)+(y.2:ℂ)*I) z) x ∂(volume.prod volume)) =
      ((∫ y : ℝ, actualProfileTransformLine f L δ y*
        (x.val.1.1:ℂ)^(-((δ:ℂ)+(y:ℂ)*I)))*
      (∫ w : ℝ, actualProfileTransformLine g L δ w*
        (x.val.2.1:ℂ)^(-((δ:ℂ)+(w:ℂ)*I))))*
      literalDiagonalSixTerm (polarMellinLeftTriple α 0 z) (polarMellinRightTriple α 0 z) x := by
    calc
      _ = ∫ y : ℝ × ℝ,
        (actualProfileTransformLine f L δ y.1*(x.val.1.1:ℂ)^(-((δ:ℂ)+(y.1:ℂ)*I)))*
        (actualProfileTransformLine g L δ y.2*(x.val.2.1:ℂ)^(-((δ:ℂ)+(y.2:ℂ)*I)))*
          literalDiagonalSixTerm (polarMellinLeftTriple α 0 z) (polarMellinRightTriple α 0 z) x
        ∂(volume.prod volume) := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [literalDiagonalSixTerm_amplifier_factorization,
          shiftedPowerArithmetic_apply _ hm, shiftedPowerArithmetic_apply _ hn]
        ring
      _ = _ := by
        rw [integral_mul_const,
          integral_prod_mul
            (fun y : ℝ => actualProfileTransformLine f L δ y*
              (x.val.1.1:ℂ)^(-((δ:ℂ)+(y:ℂ)*I)))
            (fun w : ℝ => actualProfileTransformLine g L δ w*
              (x.val.2.1:ℂ)^(-((δ:ℂ)+(w:ℂ)*I)))]
  rw [hi, profile_log_mellin_inversion hf hfs hL hmR δ,
    profile_log_mellin_inversion hg hgs hL hnR δ]
  unfold actualProfileTransformLine
  simp only [Complex.ofReal_natCast]
  ring

theorem actualProfileSixDirichlet_eq_MellinEuler {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) {α : MomentShifts} {z : ℂ}
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4) (hz : δ ≤ z.re) :
    (∑' x : DiagonalSixIndices,
      f (Real.log x.val.1.1/L)*g (Real.log x.val.2.1/L)*
        literalDiagonalSixTerm (polarMellinLeftTriple α 0 z) (polarMellinRightTriple α 0 z) x) =
      ((L:ℂ)/(2*π))^2 * ∫ y : ℝ × ℝ,
        actualProfileTransformLine f L δ y.1*actualProfileTransformLine g L δ y.2*
          ((∏ ij : Fin 3 × Fin 3, riemannZeta (1+
            polarMellinLeftTriple α ((δ:ℂ)+(y.1:ℂ)*I) z ij.1+
            polarMellinRightTriple α ((δ:ℂ)+(y.2:ℂ)*I) z ij.2))*
            shiftedPolarEulerRest
              (polarMellinLeftTriple α ((δ:ℂ)+(y.1:ℂ)*I) z)
              (polarMellinRightTriple α ((δ:ℂ)+(y.2:ℂ)*I) z))
        ∂(volume.prod volume) := by
  let F : DiagonalSixIndices → ℝ × ℝ → ℂ := fun x y =>
    actualProfileTransformLine f L δ y.1*actualProfileTransformLine g L δ y.2*
      literalDiagonalSixTerm
        (polarMellinLeftTriple α ((δ:ℂ)+(y.1:ℂ)*I) z)
        (polarMellinRightTriple α ((δ:ℂ)+(y.2:ℂ)*I) z) x
  let B : DiagonalSixIndices → ℝ := fun x =>
    ‖literalDiagonalSixTerm
      (polarMellinLeftTriple (fun j => ((α j).re:ℂ)) (δ:ℂ) (z.re:ℂ))
      (polarMellinRightTriple (fun j => ((α j).re:ℂ)) (δ:ℂ) (z.re:ℂ)) x‖
  have hB : Summable B := literalDiagonalSixTerm_initial_mellin_majorant_summable hδ hα hz
  have hprod : Integrable (fun y : ℝ × ℝ =>
      actualProfileTransformLine f L δ y.1*actualProfileTransformLine g L δ y.2)
      (volume.prod volume) :=
    (actualProfileTransformLine_integrable hf hfs hL δ).mul_prod
      (actualProfileTransformLine_integrable hg hgs hL δ)
  have hs : HasSum (fun x : DiagonalSixIndices => ∫ y : ℝ × ℝ, F x y ∂(volume.prod volume))
      (∫ y : ℝ × ℝ,
        actualProfileTransformLine f L δ y.1*actualProfileTransformLine g L δ y.2*
          ∑' x : DiagonalSixIndices, literalDiagonalSixTerm
            (polarMellinLeftTriple α ((δ:ℂ)+(y.1:ℂ)*I) z)
            (polarMellinRightTriple α ((δ:ℂ)+(y.2:ℂ)*I) z) x
        ∂(volume.prod volume)) := by
    apply hasSum_integral_of_dominated_convergence (fun x (y : ℝ × ℝ) =>
      ‖actualProfileTransformLine f L δ y.1‖*‖actualProfileTransformLine g L δ y.2‖*B x)
    · intro x
      exact hprod.aestronglyMeasurable.mul
        (literalDiagonalSixTerm_mellin_continuous α δ z x).aestronglyMeasurable
    · intro x
      filter_upwards [] with y
      dsimp [F]
      rw [norm_mul, norm_mul, literalDiagonalSixTerm_mellin_norm]
    · exact Eventually.of_forall (fun y => hB.mul_left _)
    · simp_rw [tsum_mul_left]
      simpa only [norm_mul] using hprod.norm.mul_const (∑' x, B x)
    · filter_upwards [] with y
      have hraw : Summable (fun x : DiagonalSixIndices =>
          literalDiagonalSixTerm
            (polarMellinLeftTriple α ((δ:ℂ)+(y.1:ℂ)*I) z)
            (polarMellinRightTriple α ((δ:ℂ)+(y.2:ℂ)*I) z) x) := by
        apply Summable.of_norm
        exact hB.congr (fun x => (literalDiagonalSixTerm_mellin_norm α δ y.1 y.2 z x).symm)
      exact hraw.hasSum.mul_left
        (actualProfileTransformLine f L δ y.1*actualProfileTransformLine g L δ y.2)
  calc
    _ = ∑' x : DiagonalSixIndices, ((L:ℂ)/(2*π))^2*
        ∫ y : ℝ × ℝ, F x y ∂(volume.prod volume) := by
      apply tsum_congr
      intro x
      exact (literalDiagonalSixTerm_profile_integral hf hfs hg hgs hL α δ z x).symm
    _ = _ := by
      rw [(hs.mul_left (((L:ℂ)/(2*π))^2)).tsum_eq]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      obtain ⟨ha,hb⟩ := polarMellinTriples_initial_re_lower_bound hδ hα
        (u := (δ:ℂ)+(y.1:ℂ)*I) (v := (δ:ℂ)+(y.2:ℂ)*I) (by simp) (by simp) hz
      rw [literalDiagonalSixTerm_eq_zetaProduct_mul_rest (by linarith : 0 < δ/2) ha hb]

end
end Sechstmoment
