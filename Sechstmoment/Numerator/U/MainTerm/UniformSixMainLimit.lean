import Sechstmoment.Numerator.U.MainTerm.MovingDyadicPhase
import Sechstmoment.Numerator.U.MainTerm.MovingPrincipalLimit
import Sechstmoment.Numerator.U.MainTerm.SixMainPolarLimit

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem actualSixPrincipalMoment_uniform_eventually_rescaled {R c δ : ℝ}
    (hR : 0 ≤ R) (hc : 4*R+1 ≤ c) (hδ : 0 < δ)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      actualSixPrincipalMoment T σ f g Φ δ = ∑ m : Fin 6,
        (∫ t : ℝ, (Φ (t/T):ℂ)*
          (t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m))*
        ((1/(2*π):ℂ)^2*∫ y : ℝ × ℝ,
          actualPrincipalProfileRescaledKernel T σ m f g (Real.log T) c c y
            ∂(volume.prod volume)) := by
  have hcp : 0 < c := by linarith
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (4*c)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (c/δ))] with T hT hL hLδ σ hσ
  have hLp : 0 < Real.log T := Real.log_pos hT
  have hεp : 0 < c/Real.log T := div_pos hcp hLp
  have hε1 : c/Real.log T < 1/4 := (div_lt_iff₀ hLp).mpr (by linarith)
  have hεδ : c/Real.log T ≤ δ := (div_le_iff₀ hLp).mpr (by
    have h := (div_lt_iff₀ hδ).mp hLδ
    linarith)
  have hraw (j : Fin 4) : ‖rawMomentShifts T σ j‖ ≤ (c/Real.log T)/4 := by
    rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_of_nonneg hLp.le]
    have hRc : R ≤ c/4 := by linarith
    calc
      _ ≤ (c/4)/Real.log T := div_le_div_of_nonneg_right ((hσ j).trans hRc) hLp.le
      _ = _ := by ring
  rw [actualSixPrincipalMoment_eq_time_products (zero_lt_one.trans hT) σ f g Φ hΦ δ]
  apply Finset.sum_congr rfl
  intro m _
  rw [actualPrincipalProfileIntegral_double_shift T σ m hf hfs hg hgs hLp hεp hε1 hraw hεδ,
    actualPrincipalProfileIntegral_log_rescaling T σ m hf hfs hg hgs hLp hεp hε1 hraw le_rfl le_rfl]

theorem actualSixPrincipalMoment_moving_polar_limit
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {T : ι → ℝ} {σ : ι → MomentShifts} {σ₀ : MomentShifts}
    (hT : Tendsto T l atTop) (hσ : Tendsto σ l (𝓝 σ₀))
    {R c δ : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c) (hδ : 0 < δ)
    (hσb : ∀ᶠ i in l, ∀ j : Fin 4, ‖σ i j‖ ≤ R)
    (hσ₀ : ∀ j : Fin 4, ‖σ₀ j‖ ≤ R)
    (hρ : ∀ k : PurePolarIndex, normalizedPurePolarRoot σ₀ k ≠ 0)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun i => actualSixPrincipalMoment (T i) (σ i) f g Φ δ/
      ((T i:ℂ)*(Real.log (T i):ℂ)^9)) l
      (𝓝 (actualSixPrincipalPolarLimit σ₀ f g Φ c)) := by
  have hlim (m : Fin 6) :=
    (bblrSixPhaseWeight_normalized_moving_tendsto hT hσ m Φ hΦ).mul
      ((actualPrincipalProfileRescaledIntegral_moving_polar_limit hT hσ hR hc
        hσb hσ₀ hρ m hf hfs hg hgs).const_mul ((1/(2*π):ℂ)^2))
  have hs := tendsto_finsetSum Finset.univ (fun m _ => hlim m)
  have heq : (∑ m : Fin 6,
      ((∫ x : ℝ, (Φ x:ℂ))*Complex.exp (bblrSixPhaseExponents σ₀ m))*
        ((1/(2*π):ℂ)^2*∫ y : ℝ × ℝ, actualPrincipalPolarLimitKernel σ₀ m f g c c y
          ∂(volume.prod volume))) = actualSixPrincipalPolarLimit σ₀ f g Φ c := by
    unfold actualSixPrincipalPolarLimit
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [heq] at hs
  apply hs.congr'
  filter_upwards [hT.eventually
    (actualSixPrincipalMoment_uniform_eventually_rescaled hR hc hδ hf hfs hg hgs Φ hΦ),
    hσb] with i hTi hσi
  rw [hTi (σ i) hσi,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_div]
  ring

theorem actualSixPrincipalPolarLimit_continuousWithinAt
    {R c : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c)
    (σ₀ : MomentShifts) (hσ₀ : σ₀ ∈ boundedSeparatedPolarShifts R)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) (Φ : ℝ → ℝ) :
    ContinuousWithinAt (fun σ => actualSixPrincipalPolarLimit σ f g Φ c)
      (boundedSeparatedPolarShifts R) σ₀ := by
  unfold actualSixPrincipalPolarLimit
  apply ContinuousWithinAt.const_mul
  apply tendsto_finsetSum
  intro m _
  exact (((bblrSixPhaseExponents_continuous m).cexp.continuousWithinAt).mul
    ((actualPrincipalPolarLimitIntegral_continuousWithinAt hR hc σ₀ hσ₀ m hf hfs hg hgs).const_mul ((1/(2*π):ℂ)^2))).tendsto

theorem actualSmoothSixProfileRemainderMoment_normalized_moving_tendsto
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} {σ : ι → MomentShifts}
    (hT : Tendsto T l atTop) {R δ κ a b : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ) (hab : a+b < 1)
    (hσb : ∀ᶠ i in l, ∀ j : Fin 4, ‖σ i j‖ ≤ R)
    (hgap : ∀ᶠ i in l, ∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot (σ i) k‖)
    {f g : ℝ → ℝ} (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun i => actualSixProfileRemainderMoment (T i) (σ i)
      (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ δ/
      ((T i:ℂ)*(Real.log (T i):ℂ)^9)) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hb := actualSmoothSixProfileRemainderMoment_uniform_eventually_negligible
    hR hδ hδ1 hκ hab hf hg Φ hΦ (ε/2) (by positivity)
  filter_upwards [hT.eventually hb,hσb,hgap,
    hT.eventually (eventually_gt_atTop (1:ℝ)),
    (Real.tendsto_log_atTop.comp hT).eventually (eventually_ge_atTop (1:ℝ))]
    with i hbi hσi hgi hTi hLi
  have hTp : 0 < T i := zero_lt_one.trans hTi
  have hLp : 0 < Real.log (T i) := Real.log_pos hTi
  have hn := hbi (σ i) hσi hgi
  have hp : 1 ≤ (Real.log (T i))^9 := one_le_pow₀ hLi
  rw [dist_zero_right,norm_div,norm_mul,norm_pow]
  simp only [Complex.norm_real,Real.norm_of_nonneg hTp.le,Real.norm_of_nonneg hLp.le]
  calc
    _ ≤ ε/2 := (div_le_iff₀ (by positivity : 0 < T i*(Real.log (T i))^9)).mpr (by
      have hd : T i ≤ T i*(Real.log (T i))^9 := by nlinarith
      exact hn.trans (mul_le_mul_of_nonneg_left hd (by positivity)))
    _ < ε := by linarith

theorem bblrSixMainTerms_moving_separated_polar_limit
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {T : ι → ℝ} {σ : ι → MomentShifts} {σ₀ : MomentShifts}
    (hT : Tendsto T l atTop) (hσ : Tendsto σ l (𝓝 σ₀))
    {R c δ a b : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c)
    (hδ : 0 < δ) (hδ1 : δ < 1/4) (hab : a+b < 1)
    (hσb : ∀ᶠ i in l, ∀ j : Fin 4, ‖σ i j‖ ≤ R)
    (hσ₀ : ∀ j : Fin 4, ‖σ₀ j‖ ≤ R)
    (hρ : ∀ k : PurePolarIndex, normalizedPurePolarRoot σ₀ k ≠ 0)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun i => bblrSixMainTerms (T i) a b (rawMomentShifts (T i) (σ i))
      (polarPoleKiller (T i) (σ i)) f g Φ/((T i:ℂ)*(Real.log (T i):ℂ)^9)) l
      (𝓝 (actualSixPrincipalPolarLimit σ₀ (fun x => (f x:ℂ))
        (fun x => (g x:ℂ)) Φ c)) := by
  obtain ⟨κ,hκ,hgap⟩ := normalizedPurePolarRoot_moving_eventually_gap hσ hρ
  have hp := actualSixPrincipalMoment_moving_polar_limit hT hσ hR hc hδ hσb hσ₀ hρ
    (hf.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hf.1)
    (hg.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hg.1) Φ hΦ
  have he := actualSmoothSixProfileRemainderMoment_normalized_moving_tendsto
    hT hR hδ hδ1 hκ hab hσb hgap hf hg Φ hΦ
  have hs := hp.add he
  simp only [add_zero] at hs
  apply hs.congr'
  obtain ⟨C,_hC,hrest⟩ :=
    actualSmoothSixProfileRemainderMoment_uniform_eventually_integrable_power_bound
      hR hδ hδ1 hκ hab hf hg Φ hΦ
  filter_upwards [hT.eventually hrest,hσb,hgap,
    hT.eventually (eventually_gt_atTop (1:ℝ)),
    hT.eventually (rawMomentShifts_uniform_eventually_small hR (show 0 < δ/4 by positivity))]
    with i hresti hσi hgapi hTi hα
  have hρT (k : PurePolarIndex) : purePolarRoot (T i) (σ i) k ≠ 0 := by
    rw [purePolarRoot_normalized]
    exact div_ne_zero (norm_pos_iff.mp (hκ.trans_le (hgapi k)))
      (Complex.ofReal_ne_zero.mpr (Real.log_pos hTi).ne')
  rw [bblrSixMainTerms_eq_principal_add_actualRemainder hTi hδ hδ1 (σ i)
    (hα (σ i) hσi) hρT f g Φ hf hg hΦ (hresti (σ i) hσi hgapi).1,add_div]
  rfl

theorem bblrSixMainTerms_separated_polar_locally_uniform
    {R c δ a b : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c)
    (hδ : 0 < δ) (hδ1 : δ < 1/4) (hab : a+b < 1)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    TendstoLocallyUniformlyOn
      (fun T : ℝ => fun σ : MomentShifts =>
        bblrSixMainTerms T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ/
          ((T:ℂ)*(Real.log T:ℂ)^9))
      (fun σ => actualSixPrincipalPolarLimit σ (fun x => (f x:ℂ))
        (fun x => (g x:ℂ)) Φ c) atTop (boundedSeparatedPolarShifts R) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro σ₀ hσ₀
  have hs : Tendsto (Prod.snd : ℝ × MomentShifts → MomentShifts)
      (atTop ×ˢ 𝓝[boundedSeparatedPolarShifts R] σ₀) (𝓝 σ₀) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  have hb : ∀ᶠ p : ℝ × MomentShifts in
      atTop ×ˢ 𝓝[boundedSeparatedPolarShifts R] σ₀, ∀ j : Fin 4, ‖p.2 j‖ ≤ R :=
    (tendsto_snd.eventually self_mem_nhdsWithin).mono (fun _ h => h.1)
  have ht := bblrSixMainTerms_moving_separated_polar_limit (T := Prod.fst)
    tendsto_fst hs hR hc hδ hδ1 hab hb hσ₀.1 hσ₀.2 f g Φ hf hg hΦ
  have hl := (actualSixPrincipalPolarLimit_continuousWithinAt hR hc σ₀ hσ₀
    (hf.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hf.1)
    (hg.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hg.1) Φ).tendsto.comp (tendsto_snd (f := (atTop : Filter ℝ)))
  exact (hl.prodMk_nhds ht).mono_right (nhds_le_uniformity _)

theorem bblrSixMainTerms_separated_polar_uniform_on_compact
    {R c δ a b : ℝ} (hR : 0 ≤ R) (hc : 4*R+1 ≤ c)
    (hδ : 0 < δ) (hδ1 : δ < 1/4) (hab : a+b < 1)
    {K : Set MomentShifts} (hK : IsCompact K) (hKS : K ⊆ boundedSeparatedPolarShifts R)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    TendstoUniformlyOn
      (fun T : ℝ => fun σ : MomentShifts =>
        bblrSixMainTerms T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ/
          ((T:ℂ)*(Real.log T:ℂ)^9))
      (fun σ => actualSixPrincipalPolarLimit σ (fun x => (f x:ℂ))
        (fun x => (g x:ℂ)) Φ c) atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((bblrSixMainTerms_separated_polar_locally_uniform hR hc hδ hδ1 hab f g Φ hf hg hΦ).mono hKS)

end
end Sechstmoment
