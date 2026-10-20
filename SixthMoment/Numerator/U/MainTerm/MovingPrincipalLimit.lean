import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import SixthMoment.Numerator.U.MainTerm.UniformPrincipalMajorant

namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

def boundedSeparatedPolarShifts (R : ℝ) : Set MomentShifts :=
  {σ | (∀ j : Fin 4, ‖σ j‖ ≤ R) ∧
    ∀ k : PurePolarIndex, normalizedPurePolarRoot σ k ≠ 0}

theorem polarLeftArguments_continuous_shifts (u z : ℂ) :
    Continuous (fun σ : MomentShifts => polarLeftArguments u z σ) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [polarLeftArguments] <;> fun_prop

theorem polarRightArguments_continuous_shifts (v z : ℂ) :
    Continuous (fun σ : MomentShifts => polarRightArguments v z σ) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [polarRightArguments] <;> fun_prop

theorem normalizedPurePolarRoot_moving_eventually_gap
    {ι : Type*} {l : Filter ι} {σ : ι → MomentShifts} {σ₀ : MomentShifts}
    (hσ : Tendsto σ l (𝓝 σ₀))
    (hsep : ∀ k : PurePolarIndex, normalizedPurePolarRoot σ₀ k ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ i in l,
      ∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot (σ i) k‖ := by
  let r : PurePolarIndex → ℝ := fun k => ‖normalizedPurePolarRoot σ₀ k‖/2
  have hr (k : PurePolarIndex) : 0 < r k := by
    dsimp [r]
    exact div_pos (norm_pos_iff.mpr (hsep k)) (by norm_num)
  let κ := Finset.univ.inf' Finset.univ_nonempty r
  have hκ : 0 < κ := by
    obtain ⟨k,_,hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty r
    change 0 < Finset.univ.inf' Finset.univ_nonempty r
    rw [hk]
    exact hr k
  refine ⟨κ,hκ,?_⟩
  have he (k : PurePolarIndex) : ∀ᶠ i in l, r k ≤ ‖normalizedPurePolarRoot (σ i) k‖ := by
    have ht := ((normalizedPurePolarRoot_continuous k).tendsto σ₀ |>.comp hσ).norm
    exact (ht.eventually (eventually_gt_nhds (by
      dsimp [r]
      linarith [norm_pos_iff.mpr (hsep k)]))).mono (fun _ h => h.le)
  filter_upwards [eventually_all.mpr he] with i hi k
  exact (Finset.inf'_le _ (Finset.mem_univ k)).trans (hi k)

theorem actualPrincipalPolar_all_pairings_separated {R c : ℝ}
    (hR : 0 ≤ R) (hc : R+1 ≤ c) (σ : MomentShifts)
    (hσ : ∀ j : Fin 4, ‖σ j‖ ≤ R) (m : Fin 6)
    (hsep : ∀ ij : Fin 2 × Fin 2, normalizedPurePolarRoot σ (m,ij) ≠ 0)
    (y : ℝ × ℝ) :
    ∀ ij : Fin 3 × Fin 3, ninePolarArgument ((c:ℂ)+(y.1:ℂ)*I)
      ((c:ℂ)+(y.2:ℂ)*I) 0 (bblrSixShifts σ m) ij ≠ 0 := by
  let α := bblrSixShifts σ m
  have hα (j : Fin 4) : ‖α j‖ ≤ R := bblrSixShifts_norm_le σ hσ m j
  have hpair (ij : Fin 2 × Fin 2) : principalNormalizedPureArgument α ij ≠ 0 := by
    intro hz
    apply hsep ij
    simp only [normalizedPurePolarRoot, principalNormalizedPureArgument, α] at hz ⊢
    rw [hz]
    simp
  intro ij
  rcases ij with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  all_goals simp only [ninePolarArgument,polarLeftArguments,polarRightArguments,zero_add]
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

theorem actualPrincipalProfileRescaledKernel_moving_polar_point_limit
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} {σ : ι → MomentShifts}
    {σ₀ : MomentShifts} (hT : Tendsto T l atTop) (hσ : Tendsto σ l (𝓝 σ₀))
    (m : Fin 6) (f g : ℝ → ℂ) (c d : ℝ) (y : ℝ × ℝ)
    (hρ : ∀ ij : Fin 2 × Fin 2, normalizedPurePolarRoot σ₀ (m,ij) ≠ 0)
    (hsep : ∀ ij : Fin 3 × Fin 3,
      ninePolarArgument ((c:ℂ)+(y.1:ℂ)*I) ((d:ℂ)+(y.2:ℂ)*I) 0
        (bblrSixShifts σ₀ m) ij ≠ 0) :
    Tendsto (fun i => actualPrincipalProfileRescaledKernel (T i) (σ i) m f g
      (Real.log (T i)) c d y/(Real.log (T i):ℂ)^9) l
      (𝓝 (actualPrincipalPolarLimitKernel σ₀ m f g c d y)) := by
  let u : ℂ := (c:ℂ)+(y.1:ℂ)*I
  let v : ℂ := (d:ℂ)+(y.2:ℂ)*I
  have hα := (bblrSixShifts_continuous m).tendsto σ₀ |>.comp hσ
  have hab := ((polarLeftArguments_continuous_shifts u 0).tendsto _ |>.comp hα).prodMk
    ((polarRightArguments_continuous_shifts v 0).tendsto _ |>.comp hα)
  rw [← nhds_prod_eq] at hab
  have hA := shiftedPolarEulerRest_moving_scaled_tendsto
    (Real.tendsto_log_atTop.comp hT) hab
  have hleft (L : ℝ) (ab : PolarShiftSpace) :
      (scaledPolarShifts L ab).1 = fun j => ab.1 j/(L:ℂ) :=
    funext (scaledPolarShifts_fst L ab)
  have hright (L : ℝ) (ab : PolarShiftSpace) :
      (scaledPolarShifts L ab).2 = fun j => ab.2 j/(L:ℂ) :=
    funext (scaledPolarShifts_snd L ab)
  simp_rw [hleft,hright] at hA
  have hZ := ninePolarZetaFactor_moving_tendsto
    (Real.tendsto_log_atTop.comp hT) hα u v 0 hsep
  have ht := (hA.mul hZ).const_mul
    (profileLaplaceTransform f u*profileLaplaceTransform g v)
  apply ht.congr'
  have he (ij : Fin 2 × Fin 2) :
      ∀ᶠ i in l, normalizedPurePolarRoot (σ i) (m,ij) ≠ 0 :=
    ((normalizedPurePolarRoot_continuous (m,ij)).tendsto σ₀ |>.comp hσ).eventually
      (eventually_ne_nhds (hρ ij))
  filter_upwards [hT.eventually (eventually_gt_atTop (1:ℝ)), eventually_all.mpr he]
    with i hTi hρi
  have hroot (ij : Fin 2 × Fin 2) : purePolarRoot (T i) (σ i) (m,ij) ≠ 0 := by
    rw [purePolarRoot_normalized]
    exact div_ne_zero (hρi ij) (Complex.ofReal_ne_zero.mpr (Real.log_pos hTi).ne')
  dsimp only [Function.comp_def]
  change (profileLaplaceTransform f u*profileLaplaceTransform g v)*
      (shiftedPolarEulerRest _ _*ninePolarZetaFactor (Real.log (T i)) u v 0
        (bblrSixShifts (σ i) m)) =
    ((profileLaplaceTransform f u*profileLaplaceTransform g v)*
      polarMellinRemovedKernel (T i) (σ i) m (u/(Real.log (T i):ℂ))
        (v/(Real.log (T i):ℂ)) 0)/(Real.log (T i):ℂ)^9
  rw [mul_div_assoc,polarMellinRemovedKernel_principal_scaled_identity (T i) (σ i) m _ _ hroot]

theorem actualPrincipalProfileRescaledIntegral_moving_polar_limit
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {T : ι → ℝ} {σ : ι → MomentShifts} {σ₀ : MomentShifts}
    (hT : Tendsto T l atTop) (hσ : Tendsto σ l (𝓝 σ₀))
    {R c : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c)
    (hσb : ∀ᶠ i in l, ∀ j : Fin 4, ‖σ i j‖ ≤ R)
    (hσ₀ : ∀ j : Fin 4, ‖σ₀ j‖ ≤ R)
    (hρ : ∀ k : PurePolarIndex, normalizedPurePolarRoot σ₀ k ≠ 0)
    (m : Fin 6) {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    Tendsto (fun i => ∫ y : ℝ × ℝ,
      actualPrincipalProfileRescaledKernel (T i) (σ i) m f g (Real.log (T i)) c c y/
        (Real.log (T i):ℂ)^9 ∂(volume.prod volume)) l
      (𝓝 (∫ y : ℝ × ℝ, actualPrincipalPolarLimitKernel σ₀ m f g c c y
        ∂(volume.prod volume))) := by
  have hcp : 0 < c := by linarith
  obtain ⟨κ,hκ,hgap⟩ := normalizedPurePolarRoot_moving_eventually_gap hσ hρ
  obtain ⟨C,_,hbound⟩ :=
    actualPrincipalProfileRescaledKernel_uniform_eventually_dominated hR hc hκ f g
  let B : ℝ × ℝ → ℝ := fun y =>
    C*(‖profileLaplaceTransform f ((c:ℂ)+(y.1:ℂ)*I)‖*
      ‖profileLaplaceTransform g ((c:ℂ)+(y.2:ℂ)*I)‖)
  have hi : Integrable B (volume.prod volume) := by
    have h := ((actualProfileTransformLine_integrable hf hfs (by norm_num : (0:ℝ)<1) c).norm).mul_prod
      ((actualProfileTransformLine_integrable hg hgs (by norm_num : (0:ℝ)<1) c).norm)
    simpa only [B,actualProfileTransformLine,Complex.ofReal_one,one_mul] using h.const_mul C
  refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hi ?_
  · filter_upwards [hT.eventually (eventually_gt_atTop (1:ℝ)), hσb,
      (Real.tendsto_log_atTop.comp hT).eventually (eventually_gt_atTop (4*c))]
      with i hTi hσi hL
    change 4*c < Real.log (T i) at hL
    have hLp : 0 < Real.log (T i) := Real.log_pos hTi
    have hεp : 0 < c/Real.log (T i) := div_pos hcp hLp
    have hε1 : c/Real.log (T i) < 1/4 := (div_lt_iff₀ hLp).mpr (by linarith)
    have hraw (j : Fin 4) : ‖rawMomentShifts (T i) (σ i) j‖ ≤
        (c/Real.log (T i))/4 := by
      rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_of_nonneg hLp.le]
      have hRc : R ≤ c/4 := by linarith
      calc
        _ ≤ (c/4)/Real.log (T i) :=
          div_le_div_of_nonneg_right ((hσi j).trans hRc) hLp.le
        _ = _ := by ring
    exact (actualPrincipalProfileRescaledKernel_integrable (T i) (σ i) m hf hfs hg hgs
      hLp hεp hε1 hraw le_rfl le_rfl).div_const _ |>.aestronglyMeasurable
  · filter_upwards [hT.eventually hbound,hσb,hgap] with i hb hσi hgi
    exact Eventually.of_forall (hb (σ i) hσi hgi m)
  · apply Eventually.of_forall
    intro y
    exact actualPrincipalProfileRescaledKernel_moving_polar_point_limit hT hσ m f g c c y
      (fun ij => hρ (m,ij))
      (actualPrincipalPolar_all_pairings_separated hR (by linarith : R+1 ≤ c)
        σ₀ hσ₀ m (fun ij => hρ (m,ij)) y)

theorem actualPrincipalPolarLimitKernel_moving_tendsto
    {ι : Type*} {l : Filter ι} {σ : ι → MomentShifts} {σ₀ : MomentShifts}
    (hσ : Tendsto σ l (𝓝 σ₀)) (m : Fin 6) (f g : ℝ → ℂ)
    (c d : ℝ) (y : ℝ × ℝ)
    (hsep : ∀ ij : Fin 3 × Fin 3,
      ninePolarArgument ((c:ℂ)+(y.1:ℂ)*I) ((d:ℂ)+(y.2:ℂ)*I) 0
        (bblrSixShifts σ₀ m) ij ≠ 0) :
    Tendsto (fun i => actualPrincipalPolarLimitKernel (σ i) m f g c d y) l
      (𝓝 (actualPrincipalPolarLimitKernel σ₀ m f g c d y)) := by
  have hα := (bblrSixShifts_continuous m).tendsto σ₀ |>.comp hσ
  have hr : Tendsto
      (fun i => ninePolarRationalFactor ((c:ℂ)+(y.1:ℂ)*I) ((d:ℂ)+(y.2:ℂ)*I)
        0 (bblrSixShifts (σ i) m)) l
      (𝓝 (ninePolarRationalFactor ((c:ℂ)+(y.1:ℂ)*I) ((d:ℂ)+(y.2:ℂ)*I)
        0 (bblrSixShifts σ₀ m))) := by
    apply tendsto_finsetProd
    intro ij _
    exact tendsto_const_nhds.div
      ((ninePolarArgument_continuous_shifts _ _ _ ij).tendsto _ |>.comp hα) (hsep ij)
  exact tendsto_const_nhds.mul (tendsto_const_nhds.mul hr)

theorem actualPrincipalPolarLimitKernel_measurable (σ : MomentShifts) (m : Fin 6)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : Continuous f)
    (hg : HasCompactSupport g) (hgs : Continuous g) (c d : ℝ) :
    Measurable (actualPrincipalPolarLimitKernel σ m f g c d) := by
  have hfl := (profileLaplaceTransform_differentiable hf hfs).continuous.measurable
  have hgl := (profileLaplaceTransform_differentiable hg hgs).continuous.measurable
  unfold actualPrincipalPolarLimitKernel ninePolarRationalFactor ninePolarArgument
    polarLeftArguments polarRightArguments
  fun_prop

theorem actualPrincipalPolarLimitKernel_norm_le_of_uniform_bound
    {R c κ C : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c) (hκ : 0 < κ)
    (f g : ℝ → ℂ)
    (hbound : ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      (∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖) →
      ∀ (m : Fin 6) (y : ℝ × ℝ),
        ‖actualPrincipalProfileRescaledKernel T σ m f g (Real.log T) c c y/
          (Real.log T:ℂ)^9‖ ≤
        C*(‖profileLaplaceTransform f ((c:ℂ)+(y.1:ℂ)*I)‖*
          ‖profileLaplaceTransform g ((c:ℂ)+(y.2:ℂ)*I)‖))
    (σ : MomentShifts) (hσ : ∀ j : Fin 4, ‖σ j‖ ≤ R)
    (hgap : ∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖)
    (m : Fin 6) (y : ℝ × ℝ) :
    ‖actualPrincipalPolarLimitKernel σ m f g c c y‖ ≤
      C*(‖profileLaplaceTransform f ((c:ℂ)+(y.1:ℂ)*I)‖*
        ‖profileLaplaceTransform g ((c:ℂ)+(y.2:ℂ)*I)‖) := by
  have hρ (k : PurePolarIndex) : normalizedPurePolarRoot σ k ≠ 0 :=
    norm_pos_iff.mp (hκ.trans_le (hgap k))
  have ht := actualPrincipalProfileRescaledKernel_polar_point_limit σ m f g c c y
    (fun ij => hρ (m,ij))
    (actualPrincipalPolar_all_pairings_separated hR (by linarith : R+1 ≤ c)
      σ hσ m (fun ij => hρ (m,ij)) y)
  exact le_of_tendsto ht.norm (hbound.mono (fun _ h => h σ hσ hgap m y))

theorem actualPrincipalPolarLimitIntegral_continuousWithinAt
    {R c : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c)
    (σ₀ : MomentShifts) (hσ₀ : σ₀ ∈ boundedSeparatedPolarShifts R)
    (m : Fin 6) {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    ContinuousWithinAt (fun σ => ∫ y : ℝ × ℝ,
      actualPrincipalPolarLimitKernel σ m f g c c y ∂(volume.prod volume))
      (boundedSeparatedPolarShifts R) σ₀ := by
  have hσ : Tendsto (fun σ : MomentShifts => σ)
      (𝓝[boundedSeparatedPolarShifts R] σ₀) (𝓝 σ₀) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  obtain ⟨κ,hκ,hgap⟩ := normalizedPurePolarRoot_moving_eventually_gap hσ hσ₀.2
  obtain ⟨C,_,hbound⟩ :=
    actualPrincipalProfileRescaledKernel_uniform_eventually_dominated hR hc hκ f g
  let B : ℝ × ℝ → ℝ := fun y =>
    C*(‖profileLaplaceTransform f ((c:ℂ)+(y.1:ℂ)*I)‖*
      ‖profileLaplaceTransform g ((c:ℂ)+(y.2:ℂ)*I)‖)
  have hi : Integrable B (volume.prod volume) := by
    have h := ((actualProfileTransformLine_integrable hf hfs (by norm_num : (0:ℝ)<1) c).norm).mul_prod
      ((actualProfileTransformLine_integrable hg hgs (by norm_num : (0:ℝ)<1) c).norm)
    simpa only [B,actualProfileTransformLine,Complex.ofReal_one,one_mul] using h.const_mul C
  refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hi ?_
  · exact Eventually.of_forall (fun σ =>
      (actualPrincipalPolarLimitKernel_measurable σ m hf hfs.continuous hg hgs.continuous c c).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin,hgap] with σ hσs hgσ
    exact Eventually.of_forall (actualPrincipalPolarLimitKernel_norm_le_of_uniform_bound
      hR hc hκ f g hbound σ hσs.1 hgσ m)
  · exact Eventually.of_forall (fun y =>
      actualPrincipalPolarLimitKernel_moving_tendsto hσ m f g c c y
        (actualPrincipalPolar_all_pairings_separated hR (by linarith : R+1 ≤ c)
          σ₀ hσ₀.1 m (fun ij => hσ₀.2 (m,ij)) y))

theorem actualPrincipalProfileRescaledIntegral_polar_locally_uniform
    {R c : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c) (m : Fin 6)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    TendstoLocallyUniformlyOn
      (fun T : ℝ => fun σ : MomentShifts => ∫ y : ℝ × ℝ,
        actualPrincipalProfileRescaledKernel T σ m f g (Real.log T) c c y/
          (Real.log T:ℂ)^9 ∂(volume.prod volume))
      (fun σ => ∫ y : ℝ × ℝ, actualPrincipalPolarLimitKernel σ m f g c c y
        ∂(volume.prod volume)) atTop (boundedSeparatedPolarShifts R) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro σ₀ hσ₀
  have hs : Tendsto (Prod.snd : ℝ × MomentShifts → MomentShifts)
      (atTop ×ˢ 𝓝[boundedSeparatedPolarShifts R] σ₀) (𝓝 σ₀) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  have hb : ∀ᶠ p : ℝ × MomentShifts in
      atTop ×ˢ 𝓝[boundedSeparatedPolarShifts R] σ₀, ∀ j : Fin 4, ‖p.2 j‖ ≤ R :=
    (tendsto_snd.eventually self_mem_nhdsWithin).mono (fun _ h => h.1)
  have ht := actualPrincipalProfileRescaledIntegral_moving_polar_limit
    (T := Prod.fst) tendsto_fst hs hR hc hb hσ₀.1 hσ₀.2 m hf hfs hg hgs
  have hl := (actualPrincipalPolarLimitIntegral_continuousWithinAt
    hR hc σ₀ hσ₀ m hf hfs hg hgs).tendsto.comp (tendsto_snd (f := (atTop : Filter ℝ)))
  have hh := hl.prodMk ht
  rw [← nhds_prod_eq] at hh
  exact hh.mono_right (nhds_le_uniformity _)

theorem actualPrincipalProfileRescaledIntegral_polar_uniform_on_compact
    {R c : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c) (m : Fin 6)
    {K : Set MomentShifts} (hK : IsCompact K) (hKS : K ⊆ boundedSeparatedPolarShifts R)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    TendstoUniformlyOn
      (fun T : ℝ => fun σ : MomentShifts => ∫ y : ℝ × ℝ,
        actualPrincipalProfileRescaledKernel T σ m f g (Real.log T) c c y/
          (Real.log T:ℂ)^9 ∂(volume.prod volume))
      (fun σ => ∫ y : ℝ × ℝ, actualPrincipalPolarLimitKernel σ m f g c c y
        ∂(volume.prod volume)) atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((actualPrincipalProfileRescaledIntegral_polar_locally_uniform hR hc m hf hfs hg hgs).mono hKS)

end
end SixthMoment
