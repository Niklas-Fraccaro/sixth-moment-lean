import Sechstmoment.Numerator.U.Bounds.RetainedGCDDiscrepancyReduction
import Sechstmoment.Numerator.U.Sources.ActualUnrestrictedGCDInitialJoin
import Sechstmoment.Numerator.U.ZeroModes.EightEtaFrontMainBudget
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.ActivePassiveComparison
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.PassiveMaskBound

/-! The actual source-only A03 uniform little-o completion. Every native
reconstruction and mask comparison is supplied by a proved theorem;
the final analytic inputs are the unchanged fixed AFE and oriented source inputs. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03EightUnrestricted_eventually_eq_actualEtaFront
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      (∑ dual : Bool,a03ActualFourUnrestrictedRatioGCDVStar dual (fun x => (Φ x:ℂ)) T a b σ f g)=
        a03EightActualEtaFront T a b σ f g Φ := by
  obtain ⟨hη,hηcap,_⟩ := a03ZeroModeRatioResidualAmplifier_exponent_lt_one ha hab hlen
  have hε : 0<rectangularSlack a b/4 := by positivity
  have hε1 : rectangularSlack a b/4<1/8 := by linarith
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc (1:ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  filter_upwards [a03ActualEightUnrestrictedRatioGCDVStar_eventually_eq_etaFront
    hΦc hΦs K hK hκ hε hε1 f g a b] with T hT
  intro σ hσ
  rw [hT σ hσ (hroot σ hσ)]
  unfold a03EightActualEtaFront
  simp only [Finset.mul_sum,a03SourceNormalizedChamber_raw,a03SourceShifts]

/-- Eight actual unrestricted native branches produce the four literal
crossed BBLR main terms, uniformly on the original compact shift domain. -/
theorem a03EightUnrestricted_minus_literal_crossed_uniform_oT
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖(∑ dual : Bool,a03ActualFourUnrestrictedRatioGCDVStar dual (fun x => (Φ x:ℂ)) T a b σ f g)-
        ∑j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
          (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖≤δ*T := by
  intro δ hδ
  filter_upwards [a03EightUnrestricted_eventually_eq_actualEtaFront ha hab hlen K hK hκ hroot f g Φ hΦ,
    a03EightActualEtaFront_minus_literal_crossed_uniform_oT ha hab hlen K hK hκ hroot f g Φ hf hg hΦ δ hδ]
    with T hId hB
  intro σ hσ
  rw [hId σ hσ]
  exact hB σ hσ

private theorem norm_eight_bool_sum_le (F : Bool→Bool→Bool→ℂ) (E : ℝ)
    (hF : ∀ dual m n,‖F dual m n‖≤E) : ‖∑dual : Bool,∑m : Bool,∑n : Bool,F dual m n‖≤8*E := by
  calc
    _≤∑dual : Bool,∑m : Bool,∑n : Bool,‖F dual m n‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro dual _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m _
      exact norm_sum_le _ _
    _≤∑_dual : Bool,∑_m : Bool,∑_n : Bool,E := by
      apply Finset.sum_le_sum
      intro dual _
      apply Finset.sum_le_sum
      intro m _
      exact Finset.sum_le_sum (fun n _ => hF dual m n)
    _=_ := by simp only [Fintype.sum_bool]; ring

/-- The eight retained source branches converge to the eight unrestricted
native branches. The only source input is the unchanged oriented divisor-sum input. -/
theorem a03ActualRetained_minus_unrestricted_uniform_slack_smaller
    (hSource : SeparatedQuadraticInput) {a b : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
        ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ∈K,
          ‖(∑dual : Bool,a03ActualFourRetainedRatioGCDVStarFinite dual (fun x => (Φ x:ℂ))
              T a b s u (rectangularSlack a b/128) σ f g)-
            ∑dual : Bool,a03ActualFourUnrestrictedRatioGCDVStar dual (fun x => (Φ x:ℂ)) T a b σ f g‖≤δ*T := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  have hσR (σ : MomentShifts) (hσ : σ∈K) (j : Fin 4) : ‖σ j‖≤R :=
    ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left _ _)
  obtain ⟨S,U,hS,hS2,hScap,hU,hUcap,hActive⟩ :=
    a03_actual_active_retained_sub_passive_retained_uniform_slack_smaller
      hSource ha hab hlen f g Φ hf hg hΦ hκ hR
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc (1:ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  have hε : 0<rectangularSlack a b/128 := by
    have := (rectangular_slack_bounds hab hlen).1
    positivity
  refine ⟨S,U,hS,hS2,hScap,hU,hUcap,?_⟩
  intro s u hs hsS hu huU δ hδ
  have hsa : s+a<1 := by linarith only [hsS.trans hScap,ha,hab,hlen]
  have hsb : s+b<1 := by linarith only [hsS.trans hScap,ha,hab,hlen]
  obtain ⟨C,hC,hNative⟩ := a03_actual_passive_retained_GCD_sub_unrestricted_uniform_rapid
    hΦc hΦs K hK hκ ha (ha.trans hab) hs (hsS.trans hS2.le) hu hε hsa hsb f g hf hg (0:ℝ)
  filter_upwards [hActive s u hs hsS hu huU (δ/16) (by positivity),hNative,
    compactNormalizedShifts_eventually_norm_small K hK (1/4) (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop (16*C/δ)] with T hAT hNT hsmall hlog hTC
  intro σ hσ
  have hCδ : C≤(δ/16)*T := by
    have hh := (div_le_iff₀ hδ).mp hTC
    nlinarith
  have hsingle (dual m n : Bool) :
      ‖a03ActualRetainedRatioGCDVStarFinite dual (fun x => (Φ x:ℂ)) T a b s u (rectangularSlack a b/128)
          σ (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g-
        a03ActualUnrestrictedRatioGCDVStar dual (fun x => (Φ x:ℂ)) T a b σ
          (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g‖≤(δ/8)*T := by
    let α := a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)
    have hα := a03SourceChamberShifts_norm_le_quarter dual σ (hsmall σ hσ) m n
    have hαR := a03SourceChamberShifts_norm_le_raw_scale (zero_lt_one.trans_le hlog) dual σ (hσR σ hσ) m n
    have hA := hAT σ α (hσR σ hσ) hαR (hroot σ hσ) dual
    have hN := hNT σ hσ (hroot σ hσ) α hα dual
    simp only [neg_zero,Real.rpow_zero,mul_one] at hN
    have he : a03ActualRetainedRatioGCDVStarFinite dual (fun x => (Φ x:ℂ)) T a b s u
        (rectangularSlack a b/128) σ α f g-
        a03ActualUnrestrictedRatioGCDVStar dual (fun x => (Φ x:ℂ)) T a b σ α f g=
      (a03ActualRetainedRatioGCDVStarFinite dual (fun x => (Φ x:ℂ)) T a b s u
        (rectangularSlack a b/128) σ α f g-
        a03ActualPassiveRetainedRatioGCDVStarFinite (fun _ => True) dual (fun x => (Φ x:ℂ))
          T a b s u (rectangularSlack a b/128) σ α f g)+
      (a03ActualPassiveRetainedRatioGCDVStarFinite (fun _ => True) dual (fun x => (Φ x:ℂ))
        T a b s u (rectangularSlack a b/128) σ α f g-
        a03ActualUnrestrictedRatioGCDVStar dual (fun x => (Φ x:ℂ)) T a b σ α f g) := by ring
    change ‖a03ActualRetainedRatioGCDVStarFinite dual (fun x => (Φ x:ℂ)) T a b s u
      (rectangularSlack a b/128) σ α f g-
      a03ActualUnrestrictedRatioGCDVStar dual (fun x => (Φ x:ℂ)) T a b σ α f g‖≤_
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add hA (hN.trans hCδ)).trans_eq (by ring))
  unfold a03ActualFourRetainedRatioGCDVStarFinite a03ActualFourUnrestrictedRatioGCDVStar
  rw [←Finset.sum_sub_distrib]
  simp_rw [←Finset.sum_sub_distrib]
  exact (norm_eight_bool_sum_le _ ((δ/8)*T) hsingle).trans_eq (by ring)

/-- Source-only A03 on the original compact normalized-shift domain.
The smooth functions and the root gap are fixed before T. Both original
paper inputs remain explicit; no reconstruction or final error bound is assumed. -/
theorem a03SourceOnly_uniform_oT
    (hAFE : BBLRv1FixedApproximateFEInput) (hSource : SeparatedQuadraticInput) {a b : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖≤δ*T := by
  obtain ⟨S₀,U₀,hS₀,hS₀2,hS₀cap,hU₀,hU₀cap,hReduction⟩ :=
    a03FinalDiscrepancy_minus_retainedGCDCrossed_uniform_oT hAFE hSource ha hab hlen (by norm_num : (0:ℝ)<1)
      K hK hκ hroot f g Φ hf hg hΦ
  obtain ⟨S₁,U₁,hS₁,hS₁2,hS₁cap,hU₁,hU₁cap,hNative⟩ :=
    a03ActualRetained_minus_unrestricted_uniform_slack_smaller hSource ha hab hlen K hK hκ hroot f g Φ hf hg hΦ
  let s := min S₀ S₁/2
  let u := min U₀ U₁/2
  have hs : 0<s := by dsimp [s]; positivity
  have hu : 0<u := by dsimp [u]; positivity
  have hs₀ : s≤S₀ := by dsimp [s]; linarith [min_le_left S₀ S₁,min_le_right S₀ S₁]
  have hs₁ : s≤S₁ := by dsimp [s]; linarith [min_le_left S₀ S₁,min_le_right S₀ S₁]
  have hu₀ : u≤U₀ := by dsimp [u]; linarith [min_le_left U₀ U₁,min_le_right U₀ U₁]
  have hu₁ : u≤U₁ := by dsimp [u]; linarith [min_le_left U₀ U₁,min_le_right U₀ U₁]
  intro δ hδ
  filter_upwards [hReduction s u hs hs₀ hu hu₀ (δ/3) (by positivity),
    hNative s u hs hs₁ hu hu₁ (δ/3) (by positivity),
    a03EightUnrestricted_minus_literal_crossed_uniform_oT ha hab hlen K hK hκ hroot f g Φ hf hg hΦ
      (δ/3) (by positivity)] with T hR hN hM
  intro σ hσ
  have he : bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ=
      (bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
        a03RetainedGCDCrossedDiscrepancy T a b s u σ f g Φ)+
      ((∑dual : Bool,a03ActualFourRetainedRatioGCDVStarFinite dual (fun x => (Φ x:ℂ))
        T a b s u (rectangularSlack a b/128) σ f g)-
        ∑dual : Bool,a03ActualFourUnrestrictedRatioGCDVStar dual (fun x => (Φ x:ℂ)) T a b σ f g)+
      ((∑dual : Bool,a03ActualFourUnrestrictedRatioGCDVStar dual (fun x => (Φ x:ℂ)) T a b σ f g)-
        ∑j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
          (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ) := by
    unfold a03RetainedGCDCrossedDiscrepancy
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  exact (add_le_add ((norm_add_le _ _).trans (add_le_add (hR σ hσ) (hN σ hσ))) (hM σ hσ)).trans_eq (by ring)

end
end Sechstmoment
