import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Sechstmoment.Numerator.U.MainTerm.PrincipalPolarPointLimit
import Sechstmoment.Numerator.U.MainTerm.ScaledZetaDirichletBound


namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

def principalNormalizedEntangledArguments (α : MomentShifts) (u v : ℂ) : Fin 5 → ℂ :=
  ![u+v,u+α 2,u+α 3,v+α 0,v+α 1]

def principalNormalizedEntangledZetaProduct (L : ℝ) (α : MomentShifts) (u v : ℂ) : ℂ :=
  ∏ i : Fin 5, riemannZeta (1+principalNormalizedEntangledArguments α u v i/(L:ℂ))/(L:ℂ)

def principalNormalizedPureArgument (α : MomentShifts) (ij : Fin 2 × Fin 2) : ℂ :=
  α (purePolarLeft ij.1)+α (purePolarRight ij.2)

def principalNormalizedPureZetaProduct (L : ℝ) (α : MomentShifts) : ℂ :=
  ∏ ij : Fin 2 × Fin 2, riemannZeta (1+principalNormalizedPureArgument α ij/(L:ℂ))/(L:ℂ)

theorem ninePolarZetaFactor_zero_eq_normalized_split
    (L : ℝ) (α : MomentShifts) (u v : ℂ) :
    ninePolarZetaFactor L u v 0 α =
      principalNormalizedEntangledZetaProduct L α u v*principalNormalizedPureZetaProduct L α := by
  simp only [ninePolarZetaFactor,ninePolarArgument,polarLeftArguments,polarRightArguments,
    principalNormalizedEntangledZetaProduct,principalNormalizedEntangledArguments,
    principalNormalizedPureZetaProduct,principalNormalizedPureArgument,purePolarLeft,purePolarRight,
    Fintype.prod_prod_type,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,zero_add]
  simp
  ring

theorem principalNormalizedEntangledArguments_re_lower
    {R c : ℝ} (hR : 0 ≤ R) (hc : R+1 ≤ c) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ R) (y : ℝ × ℝ) (i : Fin 5) :
    1 ≤ (principalNormalizedEntangledArguments α ((c:ℂ)+(y.1:ℂ)*I)
      ((c:ℂ)+(y.2:ℂ)*I) i).re := by
  have hr (j : Fin 4) : -R ≤ (α j).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
  fin_cases i <;> simp [principalNormalizedEntangledArguments] <;>
    linarith [hr 0,hr 1,hr 2,hr 3]

theorem principalNormalizedEntangledZetaProduct_norm_bound
    {L R c : ℝ} (hL : 1 ≤ L) (hR : 0 ≤ R) (hc : R+1 ≤ c)
    (α : MomentShifts) (hα : ∀ j : Fin 4, ‖α j‖ ≤ R) (y : ℝ × ℝ) :
    ‖principalNormalizedEntangledZetaProduct L α ((c:ℂ)+(y.1:ℂ)*I)
      ((c:ℂ)+(y.2:ℂ)*I)‖ ≤ (2:ℝ)^5 := by
  unfold principalNormalizedEntangledZetaProduct
  calc
    _ ≤ ∏ i : Fin 5, ‖riemannZeta (1+
        principalNormalizedEntangledArguments α ((c:ℂ)+(y.1:ℂ)*I)
          ((c:ℂ)+(y.2:ℂ)*I) i/(L:ℂ))/(L:ℂ)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _i : Fin 5, (2:ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      exact scaled_riemannZeta_norm_bound_one hL
        (principalNormalizedEntangledArguments_re_lower hR hc α hα y i)
    _ = _ := by simp

theorem principalNormalizedPureZetaProduct_tendsto (α : MomentShifts)
    (hpair : ∀ ij : Fin 2 × Fin 2, principalNormalizedPureArgument α ij ≠ 0) :
    Tendsto (fun L : ℝ => principalNormalizedPureZetaProduct L α) atTop
      (𝓝 (∏ ij : Fin 2 × Fin 2, 1/principalNormalizedPureArgument α ij)) := by
  apply tendsto_finsetProd
  intro ij _
  exact scaled_riemannZeta_tendsto (hpair ij)

theorem principalNormalizedPureZetaProduct_eventually_bounded (α : MomentShifts)
    (hpair : ∀ ij : Fin 2 × Fin 2, principalNormalizedPureArgument α ij ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ‖principalNormalizedPureZetaProduct L α‖ ≤ C := by
  let p : ℂ := ∏ ij : Fin 2 × Fin 2, 1/principalNormalizedPureArgument α ij
  refine ⟨‖p‖+1,by positivity,?_⟩
  exact ((principalNormalizedPureZetaProduct_tendsto α hpair).norm.eventually
    (eventually_lt_nhds (by simp [p] : ‖p‖ < ‖p‖+1))).mono (fun _ h => h.le)

private theorem actualPrincipalPolar_pair_sep (σ : MomentShifts) (m : Fin 6)
    (hρ : ∀ ij : Fin 2 × Fin 2, normalizedPurePolarRoot σ (m,ij) ≠ 0) :
    ∀ ij : Fin 2 × Fin 2, principalNormalizedPureArgument (bblrSixShifts σ m) ij ≠ 0 := by
  intro ij h
  apply hρ ij
  simp only [normalizedPurePolarRoot,principalNormalizedPureArgument] at h ⊢
  rw [h]
  simp

private theorem actualPrincipalPolar_all_pairings_sep {R c : ℝ}
    (hR : 0 ≤ R) (hc : R+1 ≤ c) (α : MomentShifts)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ R)
    (hpair : ∀ ij : Fin 2 × Fin 2, principalNormalizedPureArgument α ij ≠ 0)
    (y : ℝ × ℝ) :
    ∀ ij : Fin 3 × Fin 3, ninePolarArgument ((c:ℂ)+(y.1:ℂ)*I)
      ((c:ℂ)+(y.2:ℂ)*I) 0 α ij ≠ 0 := by
  intro ij
  rcases ij with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  all_goals simp only [ninePolarArgument,polarLeftArguments,polarRightArguments,
    zero_add]
  · intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith
  · intro he
    have hr := congrArg Complex.re he
    simp at hr
    have hb := (abs_le.mp ((Complex.abs_re_le_norm (α 2)).trans (hα 2))).1
    linarith
  · intro he
    have hr := congrArg Complex.re he
    simp at hr
    have hb := (abs_le.mp ((Complex.abs_re_le_norm (α 3)).trans (hα 3))).1
    linarith
  · intro he
    have hr := congrArg Complex.re he
    simp at hr
    have hb := (abs_le.mp ((Complex.abs_re_le_norm (α 0)).trans (hα 0))).1
    linarith
  · simpa [principalNormalizedPureArgument,purePolarLeft,purePolarRight] using hpair (0,0)
  · simpa [principalNormalizedPureArgument,purePolarLeft,purePolarRight] using hpair (0,1)
  · intro he
    have hr := congrArg Complex.re he
    simp at hr
    have hb := (abs_le.mp ((Complex.abs_re_le_norm (α 1)).trans (hα 1))).1
    linarith
  · simpa [principalNormalizedPureArgument,purePolarLeft,purePolarRight] using hpair (1,0)
  · simpa [principalNormalizedPureArgument,purePolarLeft,purePolarRight] using hpair (1,1)

theorem actualPrincipalProfileRescaledKernel_eventually_dominated
    {R c : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c) (σ : MomentShifts)
    (hσ : ∀ j : Fin 4, ‖σ j‖ ≤ R) (m : Fin 6)
    (hρ : ∀ ij : Fin 2 × Fin 2, normalizedPurePolarRoot σ (m,ij) ≠ 0)
    (f g : ℝ → ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ y : ℝ × ℝ,
      ‖actualPrincipalProfileRescaledKernel T σ m f g (Real.log T) c c y/
        (Real.log T:ℂ)^9‖ ≤
        C*(‖profileLaplaceTransform f ((c:ℂ)+(y.1:ℂ)*I)‖*
          ‖profileLaplaceTransform g ((c:ℂ)+(y.2:ℂ)*I)‖) := by
  let α := bblrSixShifts σ m
  have hα (j : Fin 4) : ‖α j‖ ≤ R := bblrSixShifts_norm_le σ hσ m j
  have hc1 : R+1 ≤ c := by linarith
  have hcp : 0 < c := by linarith
  obtain ⟨B,hB,hpure⟩ := principalNormalizedPureZetaProduct_eventually_bounded α
    (actualPrincipalPolar_pair_sep σ m hρ)
  let A : ℝ := Real.exp (∑' p : {n : ℕ // Nat.Prime n}, shiftedPolarPrimeUniformMajorant (1/8) p)
  have hA : 0 < A := Real.exp_pos _
  refine ⟨A*(2:ℝ)^5*B,by positivity,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hpure,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/32)]
    with T hpure hT hL hraw y
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
      exact mul_le_mul hE (mul_le_mul hZ hpure (norm_nonneg _) (by positivity))
        (by positivity) hA.le
    _ = _ := by dsimp [u,v]; ring

theorem actualPrincipalProfileRescaledIntegral_polar_limit
    {R c : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c) (σ : MomentShifts)
    (hσ : ∀ j : Fin 4, ‖σ j‖ ≤ R) (m : Fin 6)
    (hρ : ∀ ij : Fin 2 × Fin 2, normalizedPurePolarRoot σ (m,ij) ≠ 0)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    Tendsto (fun T : ℝ => ∫ y : ℝ × ℝ,
      actualPrincipalProfileRescaledKernel T σ m f g (Real.log T) c c y/
        (Real.log T:ℂ)^9 ∂(volume.prod volume)) atTop
      (𝓝 (∫ y : ℝ × ℝ, actualPrincipalPolarLimitKernel σ m f g c c y
        ∂(volume.prod volume))) := by
  have hcp : 0 < c := by linarith
  obtain ⟨C,_,hbound⟩ := actualPrincipalProfileRescaledKernel_eventually_dominated hR hc σ hσ m hρ f g
  let B : ℝ × ℝ → ℝ := fun y =>
    C*(‖profileLaplaceTransform f ((c:ℂ)+(y.1:ℂ)*I)‖*
      ‖profileLaplaceTransform g ((c:ℂ)+(y.2:ℂ)*I)‖)
  have hi : Integrable B (volume.prod volume) := by
    have h := ((actualProfileTransformLine_integrable hf hfs (by norm_num : (0:ℝ)<1) c).norm).mul_prod
      ((actualProfileTransformLine_integrable hg hgs (by norm_num : (0:ℝ)<1) c).norm)
    simpa only [B,actualProfileTransformLine,Complex.ofReal_one,one_mul] using h.const_mul C
  refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hi ?_
  · filter_upwards [eventually_gt_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_gt_atTop (4*c))] with T hT hL
    have hLp : 0 < Real.log T := Real.log_pos hT
    have hεp : 0 < c/Real.log T := div_pos hcp hLp
    have hε1 : c/Real.log T < 1/4 := (div_lt_iff₀ hLp).mpr (by linarith)
    have hraw (j : Fin 4) : ‖rawMomentShifts T σ j‖ ≤ (c/Real.log T)/4 := by
      rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_of_nonneg hLp.le]
      have hRc : R ≤ c/4 := by linarith
      calc
        _ ≤ (c/4)/Real.log T := div_le_div_of_nonneg_right ((hσ j).trans hRc) hLp.le
        _ = _ := by ring
    exact (actualPrincipalProfileRescaledKernel_integrable T σ m hf hfs hg hgs
      hLp hεp hε1 hraw le_rfl le_rfl).div_const _ |>.aestronglyMeasurable
  · exact hbound.mono (fun T h => Eventually.of_forall h)
  · apply Eventually.of_forall
    intro y
    exact actualPrincipalProfileRescaledKernel_polar_point_limit σ m f g c c y hρ
      (actualPrincipalPolar_all_pairings_sep hR (by linarith : R+1 ≤ c)
        (bblrSixShifts σ m) (fun j => bblrSixShifts_norm_le σ hσ m j)
        (actualPrincipalPolar_pair_sep σ m hρ) y)

end
end Sechstmoment
