import Sechstmoment.Numerator.U.ZeroModes.Ratio.InactivePhysicalFar
import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.SevenGridSpectralTail
import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.SourceLinearJoin

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_passive_ratio_inactive_linear_uniform_slack_smaller
    (hinput : SeparatedQuadraticInput) {a b κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
        (∀ i,select i → ¬phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
          (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2) →
        ∀ dual : Bool,
        IntegrableOn (fun v => a03ActualPassiveRatioSourceLinearZeroFinite select dual (fun x => (Φ x:ℂ))
          (rectangularSlack a b/512) T a b s u (rectangularSlack a b/128) v σ α f g)
          (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
        ‖a03ActualPassiveRatioSourceLinearZeroMoment select dual (fun x => (Φ x:ℂ))
          (rectangularSlack a b/512) T a b s u (rectangularSlack a b/128) θ σ α f g‖≤δ*T := by
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 := (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  obtain ⟨S,U,hS,hS2,hScap,hU,hUcap,hsource⟩ :=
    a03_actual_passive_ratio_source_physical_sub_linear_uniform_slack_smaller hinput ha hab hlen
      f g hf hg hΦc hΦs hκ hθ hR
  refine ⟨S,U,hS,hS2,hScap,hU,hUcap,?_⟩
  intro s u hs hss hu huu
  have hs1 : s≤1 := (hss.trans_lt hS2).le.trans (by norm_num)
  obtain ⟨hc,hc1,_he,_hexp⟩ := a03_actual_four_ratio_replacement_slack_budget ha hab hlen
    (hss.trans hScap) (huu.trans hUcap)
  obtain ⟨C,hC,hfar⟩ := a03_actual_ratio_inactive_physical_moment_uniform_rapid
    ha (ha.trans hab) hf hg hΦ hc hc1 hκ hθ hR hs hs1 hu (1:ℝ) (rectangularSlack a b/128)
  have ho : (fun T : ℝ => C*T^(-1:ℝ))=o[atTop] (fun T : ℝ => T) := by
    simpa using (polylog_mul_rpow_isLittleO_id 0 (by norm_num : (-1:ℝ)<1)).const_mul_left C
  intro δ hδ
  filter_upwards [hsource s u hs hss hu huu (δ/2) (by positivity),hfar,ho.bound (by positivity : 0<δ/2),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R)),eventually_gt_atTop (0:ℝ)]
    with T hsource hfar ho hlog hlogR hT
  intro σ α hσ hα hroot select hinactive dual
  have hαquarter : ∀ j,‖α j‖≤1/4 := fun j =>
    (hα j).trans ((div_le_iff₀ (zero_lt_one.trans_le hlog)).mpr (by linarith))
  have hsl := hsource σ α hσ hα hroot dual select
  have hp := hfar σ α hσ hαquarter hroot select hinactive dual
  rw [Real.norm_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hT.le _)),Real.norm_of_nonneg hT.le] at ho
  have hp' : ‖a03ActualPassiveRatioSourceValueMoment select false dual (fun x => (Φ x:ℂ))
      (rectangularSlack a b/512) T a b s u (rectangularSlack a b/128) θ σ α f g‖≤(δ/2)*T :=
    hp.trans ho
  refine ⟨hsl.2.1,?_⟩
  calc
    _ = ‖(a03ActualPassiveRatioSourceLinearZeroMoment select dual (fun x => (Φ x:ℂ))
        (rectangularSlack a b/512) T a b s u (rectangularSlack a b/128) θ σ α f g-
      a03ActualPassiveRatioSourceValueMoment select false dual (fun x => (Φ x:ℂ))
        (rectangularSlack a b/512) T a b s u (rectangularSlack a b/128) θ σ α f g)+
      a03ActualPassiveRatioSourceValueMoment select false dual (fun x => (Φ x:ℂ))
        (rectangularSlack a b/512) T a b s u (rectangularSlack a b/128) θ σ α f g‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ δ*T := by rw [norm_sub_rev]; linarith [hsl.2.2,hp']

theorem a03_actual_passive_ratio_inactive_retained_GCD_uniform_slack_smaller
    (hinput : SeparatedQuadraticInput) {a b κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hκ : 0<κ) (hθ : 0<θ) (hR : 0≤R) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
        (∀ i,select i → ¬phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
          (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2) →
        ∀ dual : Bool,
        ‖a03ActualPassiveRetainedRatioGCDVStarFinite select dual (fun x => (Φ x:ℂ))
          T a b s u (rectangularSlack a b/128) σ α f g‖≤δ*T := by
  obtain ⟨S,U,hS,hS2,hScap,hU,hUcap,hsmall⟩ :=
    a03_actual_passive_ratio_inactive_linear_uniform_slack_smaller hinput ha hab hlen
      f g Φ hf hg hΦ hκ hθ.le hR
  refine ⟨S,U,hS,hS2,hScap,hU,hUcap,?_⟩
  intro s u hs hss hu huu
  have hΦc : Continuous (fun x => (Φ x:ℂ)) := Complex.continuous_ofReal.comp hΦ.1.continuous
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 := (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  obtain ⟨hc,_hc1,_he,_hexp⟩ := a03_actual_four_ratio_replacement_slack_budget ha hab hlen
    (hss.trans hScap) (huu.trans hUcap)
  obtain ⟨C,hC,htail⟩ := a03_actual_passive_ratio_source_linear_core_sub_full_uniform_rapid
    ha (ha.trans hab) hs.le hu f g hf hg hΦc hΦs hc hθ hκ hR (rectangularSlack a b/128) 0
  intro δ hδ
  filter_upwards [hsmall s u hs hss hu huu (δ/2) (by positivity),htail,
    eventually_ge_atTop (2*C/δ),eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R))]
    with T hsmall htail hthreshold hT hlog hlogR
  intro σ α hσ hα hroot select hinactive dual
  have hαquarter : ∀ j,‖α j‖≤1/4 := fun j =>
    (hα j).trans ((div_le_iff₀ (zero_lt_one.trans_le hlog)).mpr (by linarith))
  have hlinear := (hsmall σ α hσ hα hroot select hinactive dual).2
  have hfull := htail σ α hσ hαquarter hα hroot dual select
  simp only [neg_zero,Real.rpow_zero,mul_one] at hfull
  rw [a03_actual_passive_ratio_source_linear_full_moment_eq_retained_GCD select hΦc hΦs
    hT hlog hc hκ σ α hroot hαquarter dual a b s u (rectangularSlack a b/128) f g] at hfull
  have hCδ : C≤(δ/2)*T := by
    have h := (div_le_iff₀ hδ).mp hthreshold
    nlinarith
  have hconst : ‖(1/(2*Real.pi):ℂ)‖≤1 := by
    rw [norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    exact (div_le_one (by positivity : (0:ℝ)<2*Real.pi)).mpr (by linarith [Real.pi_gt_three])
  have hlin : ‖(1/(2*Real.pi):ℂ)*a03ActualPassiveRatioSourceLinearZeroMoment select dual (fun x => (Φ x:ℂ))
      (rectangularSlack a b/512) T a b s u (rectangularSlack a b/128) θ σ α f g‖≤(δ/2)*T := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hconst (norm_nonneg _)).trans
      (by simpa only [one_mul] using hlinear)
  calc
    _ = ‖(a03ActualPassiveRetainedRatioGCDVStarFinite select dual (fun x => (Φ x:ℂ))
        T a b s u (rectangularSlack a b/128) σ α f g-
      (1/(2*Real.pi):ℂ)*a03ActualPassiveRatioSourceLinearZeroMoment select dual (fun x => (Φ x:ℂ))
        (rectangularSlack a b/512) T a b s u (rectangularSlack a b/128) θ σ α f g)+
      (1/(2*Real.pi):ℂ)*a03ActualPassiveRatioSourceLinearZeroMoment select dual (fun x => (Φ x:ℂ))
        (rectangularSlack a b/512) T a b s u (rectangularSlack a b/128) θ σ α f g‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ δ*T := by rw [norm_sub_rev]; linarith [hfull,hlin,hCδ]

end
end Sechstmoment
