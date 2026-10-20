import SixthMoment.Numerator.U.Replacement.GaussianTailUniform
import SixthMoment.Numerator.U.ZeroModes.Ratio.ResidualBounds


namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeRatioDifferenceZeta_norm_le_root_inverse :
    ∃ C : ℝ,0≤C ∧ ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤1/8) →
      ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0 →
      ‖riemannZeta (a03ZeroModeRatioDifferenceArgument α j 0)‖≤
        C*‖a03ZeroModeRatioRoot α j‖⁻¹ := by
  have hcompact : IsCompact (Metric.closedBall (1:ℂ) 1) := isCompact_closedBall _ _
  have himage := hcompact.image SixthMoment.polarRegularizedZeta_continuous
  obtain ⟨D,hD,hbnd⟩ := himage.isBounded.exists_pos_norm_le
  refine ⟨D/2,by positivity,?_⟩
  intro α hα j hρ
  let z : ℂ := a03ZeroModeRatioDifferenceArgument α j 0
  have hdist : ‖1-z‖=2*‖a03ZeroModeRatioRoot α j‖ := by
    rw [a03ZeroModeRatioDifferenceArgument_norm_distance,zero_sub,norm_neg]
  have hzmem : z∈Metric.closedBall (1:ℂ) 1 := by
    rw [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev,hdist]
    have hr := a03ZeroModeRatioRoot_norm_le (ε := 1) hα j
    norm_num at hr
    linarith
  have hz1 : z≠1 := by
    intro he
    rw [he,sub_self,norm_zero] at hdist
    have hn := norm_pos_iff.mpr hρ
    linarith
  have hb : ‖SixthMoment.polarRegularizedZeta z‖≤D := hbnd _ ⟨z,hzmem,rfl⟩
  rw [SixthMoment.polarRegularizedZeta_of_ne_one hz1,norm_mul,norm_sub_rev,hdist] at hb
  calc
    _ ≤ D/(2*‖a03ZeroModeRatioRoot α j‖) :=
      (le_div_iff₀ (mul_pos (by norm_num) (norm_pos_iff.mpr hρ))).mpr (by nlinarith)
    _ = _ := by rw [div_eq_mul_inv,mul_inv_rev]; norm_num; ring

theorem a03ZeroModeRatioRoot_raw_nonzero {T κ : ℝ} (hT : 1<T) (hκ : 0<κ)
    (σ : MomentShifts) (hρ : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) :
    ∀ j : Fin 2,a03ZeroModeRatioRoot (rawMomentShifts T σ) j≠0 := by
  have hn (k : PurePolarIndex) : purePolarRoot T σ k≠0 := by
    rw [purePolarRoot_normalized]
    exact div_ne_zero (norm_pos_iff.mp (hκ.trans_le (hρ k)))
      (Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne')
  intro j
  fin_cases j
  · change a03ZeroModeRatioRoot (rawMomentShifts T σ) 0≠0
    rw [a03ZeroModeRatioRoot_zero_eq_pure]
    exact neg_ne_zero.mpr (hn _)
  · change a03ZeroModeRatioRoot (rawMomentShifts T σ) 1≠0
    rw [a03ZeroModeRatioRoot_one_eq_pure]
    exact neg_ne_zero.mpr (hn _)

theorem a03ZeroModeRatioRoot_raw_inverse_norm_log_bound {T κ : ℝ}
    (hT : 1<T) (hκ : 0<κ) (σ : MomentShifts)
    (hρ : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) (j : Fin 2) :
    ‖a03ZeroModeRatioRoot (rawMomentShifts T σ) j‖⁻¹≤Real.log T/κ := by
  have hn (k : PurePolarIndex) : ‖purePolarRoot T σ k‖⁻¹≤Real.log T/κ := by
    rw [purePolarRoot_normalized,norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.log_pos hT),inv_div]
    exact div_le_div_of_nonneg_left (Real.log_pos hT).le hκ (hρ k)
  fin_cases j
  · change ‖a03ZeroModeRatioRoot (rawMomentShifts T σ) 0‖⁻¹≤_
    rw [a03ZeroModeRatioRoot_zero_eq_pure,norm_neg]
    exact hn _
  · change ‖a03ZeroModeRatioRoot (rawMomentShifts T σ) 1‖⁻¹≤_
    rw [a03ZeroModeRatioRoot_one_eq_pure,norm_neg]
    exact hn _

theorem a03ZeroModeRatioDifferenceZeta_raw_log_bound {κ : ℝ} (hκ : 0<κ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,1<T → ∀ σ : MomentShifts,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      (∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/8) → ∀ j : Fin 2,
      ‖riemannZeta (a03ZeroModeRatioDifferenceArgument (rawMomentShifts T σ) j 0)‖≤C*Real.log T := by
  obtain ⟨D,hD,hbnd⟩ := a03ZeroModeRatioDifferenceZeta_norm_le_root_inverse
  refine ⟨D/κ,by positivity,?_⟩
  intro T hT σ hρ hα j
  exact ((hbnd _ hα j (a03ZeroModeRatioRoot_raw_nonzero hT hκ σ hρ j)).trans
    (mul_le_mul_of_nonneg_left (a03ZeroModeRatioRoot_raw_inverse_norm_log_bound hT hκ σ hρ j) hD)).trans_eq
      (by ring)

def a03ZeroModeRatioResidual (L M : ℝ) (ε : ℝ) (α : MomentShifts)
    (a b : ℕ) (s : ℂ) : ℂ :=
  a03ZeroModeRatioDoubleIntegral (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioPrimaryLine ε)
    (fun u v => a03ZeroModeRatioWeightedKernel L M α a b u v s)+
  verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioWeightedLeftResidue L M α a b s)+
  verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioWeightedRightResidue L M α a b s)

theorem a03ZeroModeRatioResidual_uniform_log_bound (K : Set MomentShifts) (hK : IsCompact K)
    {κ ε δ : ℝ} (hκ : 0<κ) (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (hρ : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ a b : ℕ,a≠0 → b≠0 →
      ∀ L M : ℝ,∀ s : ℂ,1+ε≤s.re →
      ‖a03ZeroModeRatioResidual L M ε (rawMomentShifts T σ) a b s‖≤
        C*(Real.log T)^8*(a:ℝ)^δ*(b:ℝ)^δ*
          (Real.exp ((L+M)*a03ZeroModeRatioPrimaryLine ε)+
           Real.exp (M*a03ZeroModeRatioSecondaryLine ε)+
           Real.exp (L*a03ZeroModeRatioSecondaryLine ε)) := by
  obtain ⟨D,hD,hDouble⟩ := a03ZeroModeRatioWeightedKernel_double_residual_norm_bound hε hε1 hδ
  obtain ⟨E,hE,hLeft⟩ := a03ZeroModeRatioWeightedLeftResidue_norm_bound hε hε1 hδ
  obtain ⟨F,hF,hRight⟩ := a03ZeroModeRatioWeightedRightResidue_norm_bound hε hε1 hδ
  obtain ⟨Z,hZ,hZeta⟩ := a03ZeroModeRatioDifferenceZeta_raw_log_bound hκ
  let B : ℝ := Real.exp 1*16*(1+1/κ^2)^2
  have hB : 0≤B := by dsimp [B]; positivity
  let C : ℝ := D*B^2+E*Z*B+F*Z*B
  have hC : 0≤C := by dsimp [C]; positivity
  have hDb : 0≤D*B^2 := by positivity
  have hEb : 0≤E*Z*B := by positivity
  have hFb : 0≤F*Z*B := by positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [compactNormalizedShifts_eventually_norm_small K hK (ε/8) (by positivity),
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
      with T hsmall hT hL
  intro σ hσ a b ha hb L M s hs
  have hα := hsmall σ hσ
  have hroots := a03ZeroModeRatioRoot_raw_nonzero hT hκ σ (hρ σ hσ)
  have hGauss := a03ZeroModeRatioGaussianConstant_log_growth hT hL hκ σ (hρ σ hσ)
  have hGauss0 := a03ZeroModeRatioGaussianConstant_nonneg (rawMomentShifts T σ) 1
  have hα1 : ∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/8 := fun j => (hα j).trans (by linarith)
  have hzu := hZeta T hT σ (hρ σ hσ) hα1 0
  have hzv := hZeta T hT σ (hρ σ hσ) hα1 1
  rw [a03ZeroModeRatioDifferenceArgument_zero] at hzu
  rw [a03ZeroModeRatioDifferenceArgument_one] at hzv
  simp only [mul_zero,add_zero] at hzu hzv
  have hlog : (Real.log T)^5≤(Real.log T)^8 := pow_le_pow_right₀ hL (by norm_num : (5:ℕ)≤8)
  have hd := hDouble L M _ hα hroots a b ha hb s hs
  have hl := hLeft L M _ hα hroots a b ha hb s hs
  have hr := hRight L M _ hα hroots a b ha hb s hs
  have hd' : ‖a03ZeroModeRatioDoubleIntegral (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioPrimaryLine ε)
      (fun u v => a03ZeroModeRatioWeightedKernel L M (rawMomentShifts T σ) a b u v s)‖≤
      (D*B^2)*(Real.log T)^8*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp ((L+M)*a03ZeroModeRatioPrimaryLine ε) := by
    apply hd.trans
    calc
      _ ≤ D*(B*(Real.log T)^4)^2*(a:ℝ)^δ*(b:ℝ)^δ*
          Real.exp ((L+M)*a03ZeroModeRatioPrimaryLine ε) := by gcongr
      _ = _ := by ring
  have hl' : ‖verticalIntegral (a03ZeroModeRatioSecondaryLine ε)
      (a03ZeroModeRatioWeightedLeftResidue L M (rawMomentShifts T σ) a b s)‖≤
      (E*Z*B)*(Real.log T)^8*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp (M*a03ZeroModeRatioSecondaryLine ε) := by
    apply hl.trans
    calc
      _ ≤ E*(Z*Real.log T)*(B*(Real.log T)^4)*(a:ℝ)^δ*(b:ℝ)^δ*
          Real.exp (M*a03ZeroModeRatioSecondaryLine ε) := by gcongr
      _ = (E*Z*B)*(Real.log T)^5*(a:ℝ)^δ*(b:ℝ)^δ*
          Real.exp (M*a03ZeroModeRatioSecondaryLine ε) := by ring
      _ ≤ _ := by gcongr
  have hr' : ‖verticalIntegral (a03ZeroModeRatioSecondaryLine ε)
      (a03ZeroModeRatioWeightedRightResidue L M (rawMomentShifts T σ) a b s)‖≤
      (F*Z*B)*(Real.log T)^8*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp (L*a03ZeroModeRatioSecondaryLine ε) := by
    apply hr.trans
    calc
      _ ≤ F*(Z*Real.log T)*(B*(Real.log T)^4)*(a:ℝ)^δ*(b:ℝ)^δ*
          Real.exp (L*a03ZeroModeRatioSecondaryLine ε) := by gcongr
      _ = (F*Z*B)*(Real.log T)^5*(a:ℝ)^δ*(b:ℝ)^δ*
          Real.exp (L*a03ZeroModeRatioSecondaryLine ε) := by ring
      _ ≤ _ := by gcongr
  unfold a03ZeroModeRatioResidual
  let X : ℂ := a03ZeroModeRatioDoubleIntegral (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioPrimaryLine ε)
    (fun u v => a03ZeroModeRatioWeightedKernel L M (rawMomentShifts T σ) a b u v s)
  let Y : ℂ := verticalIntegral (a03ZeroModeRatioSecondaryLine ε)
    (a03ZeroModeRatioWeightedLeftResidue L M (rawMomentShifts T σ) a b s)
  let W : ℂ := verticalIntegral (a03ZeroModeRatioSecondaryLine ε)
    (a03ZeroModeRatioWeightedRightResidue L M (rawMomentShifts T σ) a b s)
  change ‖X+Y+W‖≤_
  have htri : ‖X+Y+W‖≤‖X‖+‖Y‖+‖W‖ :=
    (norm_add_le (X+Y) W).trans (add_le_add (norm_add_le X Y) (le_refl ‖W‖))
  apply htri.trans
  apply (add_le_add (add_le_add hd' hl') hr').trans
  have hcD : D*B^2≤C := by dsimp [C]; linarith
  have hcE : E*Z*B≤C := by dsimp [C]; linarith
  have hcF : F*Z*B≤C := by dsimp [C]; linarith
  calc
    _ ≤ C*(Real.log T)^8*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp ((L+M)*a03ZeroModeRatioPrimaryLine ε)+
        C*(Real.log T)^8*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp (M*a03ZeroModeRatioSecondaryLine ε)+
        C*(Real.log T)^8*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp (L*a03ZeroModeRatioSecondaryLine ε) := by gcongr
    _ = _ := by ring

end
end SixthMoment.Source
