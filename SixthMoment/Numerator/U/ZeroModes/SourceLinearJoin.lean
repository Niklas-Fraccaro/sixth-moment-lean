import SixthMoment.Numerator.U.ZeroModes.Linearization.Measurability
import SixthMoment.Numerator.U.ZeroModes.Linearization.Moment
import SixthMoment.Numerator.U.ZeroModes.SourceReplacementJoin

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_zero_linearization_eq_log_sub_linear
    (f g : ℝ→ℝ) {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c T A B H : ℝ} (hc : 0≤c) (hT : 0<T) (_hA : 0<A) (_hB : 0<B) (_hH : 0<H)
    (σ : MomentShifts) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (k : Fin 4→ℕ) (dual positive : Bool) (v : ℝ) :
    let α := a03SourceShifts dual T σ
    let p := phaseActualNearTensorData T σ α v A B H k positive
    a03EndpointPhysicalSortedZeroMode (a03ZeroModeLinearizationKernel dual Φ c p) T A B H f g k=
      a03EndpointPhysicalSortedZeroMode (a03ZeroModeLeadingKernel dual Φ c p) T A B H f g k-
        a03EndpointPhysicalSortedZeroMode (a03ZeroModeLinearKernel dual Φ c p) T A B H f g k := by
  dsimp only
  let α := a03SourceShifts dual T σ
  let p := phaseActualNearTensorData T σ α v A B H k positive
  let q := phaseActualScales A B H k
  let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
  let m := decide (q'.M₂<q'.M₁)
  let n := decide (q'.N₂<q'.N₁)
  let qs := phasePairSwapScales m n q
  have hα : ∀ j,‖α j‖≤1/4 := by
    rw [show α=bblrSixShifts (rawMomentShifts T σ) (if dual then 1 else 0) from a03SourceShifts_eq_six dual T σ]
    exact bblrSixShifts_norm_le _ hσ _
  have hqM₁ : 0<q.M₁ := boundaryActual_scale_pos _
  have hqM₂ : 0<q.M₂ := boundaryActual_scale_pos _
  have hM₂ : 0<qs.M₂ := by dsimp only [qs,phasePairSwapScales]; split_ifs; exact hqM₁; exact hqM₂
  have hF : ∀ w∈quadraticMainIndexSet qs,IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n qs w x*
      a03ZeroModeLeadingKernel dual Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n qs w x))) (Ioi 0) := by
    intro w hw
    have hw1 (j : Fin 5) : 1≤w j := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
    cases dual
    · exact a03LeadingTensorRawKernel_physical_term_integrable hΦ hΦs hc p hT hα m n qs hM₂ w hw1
    · exact a03LeadingDualTensorRawKernel_physical_term_integrable hΦ hΦs hc p hT hα m n qs hM₂ w hw1
  have hG : ∀ w∈quadraticMainIndexSet qs,IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n qs w x*
      a03ZeroModeLinearKernel dual Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n qs w x))) (Ioi 0) := by
    intro w hw
    have hw1 (j : Fin 5) : 1≤w j := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
    cases dual
    · exact a03LeadingLinearTensorRawKernel_physical_term_integrable hΦ hΦs hc p hT hα m n qs hM₂ w hw1
    · exact a03LeadingLinearDualTensorRawKernel_physical_term_integrable hΦ hΦs hc p hT hα m n qs hM₂ w hw1
  exact a03SixTensorPhysicalZeroMode_sub _ _ m n qs _ _ hF hG

def a03ActualSourceLinearZeroBlock (dual positive : Bool) (Φ : ℝ→ℂ)
    (c T s v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℂ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let α := a03SourceShifts dual T σ
  let p := phaseActualNearTensorData T σ α v A B H i.2 positive
  if phaseActualActiveNearBlock T A B H (T^(s-1)) f g i.2 then
    (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*
      a03EndpointPhysicalSortedZeroMode (a03ZeroModeLinearKernel dual Φ c p) T A B H f g i.2
  else 0

def a03ActualSourceLinearZeroFinite (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s η v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool,∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+η/2)) (T^(2+η)),a03ActualSourceLinearZeroBlock dual positive Φ c T s v σ f g i

def a03ActualSourceLinearZeroMoment (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s η θ : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∫ v in Icc (-θ*Real.log T) (θ*Real.log T),a03ActualSourceLinearZeroFinite dual Φ c T a b s η v σ f g

def a03ActualFiniteLinearZeroMoment (dual : Bool) (c T a b s η θ : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*a03ActualSourceLinearZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s η θ σ f g

theorem a03ActualZeroModeLinearizationFinite_eq_log_sub_linear
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c T : ℝ} (hc : 0≤c) (hT : 0<T) (a b s η v : ℝ) (σ : MomentShifts)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (dual : Bool) (f g : ℝ→ℝ) :
    a03ActualZeroModeLinearizationFinite dual Φ c T a b s η v σ f g=
      a03ActualSourceLeadingZeroFinite dual Φ c T a b s η v σ f g-
        a03ActualSourceLinearZeroFinite dual Φ c T a b s η v σ f g := by
  unfold a03ActualZeroModeLinearizationFinite a03ActualSourceLeadingZeroFinite a03ActualSourceLinearZeroFinite
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro positive _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold a03ActualZeroModeLinearizationBlock a03ActualSourceLeadingZeroBlock a03ActualSourceLinearZeroBlock
  dsimp only
  split_ifs
  · rw [a03_actual_zero_linearization_eq_log_sub_linear f g hΦ hΦs hc hT
      (boundaryActual_scale_pos _) (boundaryActual_scale_pos _) (boundaryActual_scale_pos _) σ hσ i.2 dual positive v]
    ring
  · ring

theorem a03ActualZeroModeLinearizationBlock_mellin_stronglyMeasurable
    (dual positive : Bool) (Φ : ℝ→ℂ) (hΦ : Measurable Φ)
    (c T s : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :
    StronglyMeasurable (fun v : ℝ => a03ActualZeroModeLinearizationBlock dual positive Φ c T s v σ f g i) := by
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let α := a03SourceShifts dual T σ
  let r := H/(B*(rectangularAFESmoothScale (i.2 2)*rectangularAFESmoothScale (i.2 3)))
  let sg := rectangularGapSign positive
  let F := fun v => a03ZeroModeLinearizationKernel dual Φ c (phaseActualNearTensorData T σ α v A B H i.2 positive)
  have hFm : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace => F p.1 p.2) :=
    (a03_zero_leading_kernel_joint_stronglyMeasurable dual Φ hΦ T c r sg σ α).sub
      (a03_zero_linear_kernel_joint_stronglyMeasurable dual Φ hΦ T c r sg σ α)
  have hz := a03EndpointPhysicalSortedZeroMode_mellin_stronglyMeasurable F hFm T A B H f g i.2
  have hscale : StronglyMeasurable (fun v : ℝ => a03SourceMellinScaleFactor c v α i.2) := by
    apply Measurable.stronglyMeasurable
    unfold a03SourceMellinScaleFactor
    apply Finset.measurable_prod
    intro j _
    fun_prop
  unfold a03ActualZeroModeLinearizationBlock
  dsimp only
  split_ifs
  · exact (hscale.const_mul (T:ℂ)).mul hz
  · exact stronglyMeasurable_const

theorem a03_actual_zero_linearization_moment_eventually_integrable
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs : s<1/2)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      IntegrableOn (fun v => a03ActualZeroModeLinearizationFinite dual Φ c T a b s η v σ f g)
        (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  obtain ⟨C,hC,hbnd⟩ := a03_actual_zero_linearization_weighted_block_uniform_bound ha hab hlen hs f g hf hg
    hΦ hΦs hc hc1 hε hκ hθ hR
  filter_upwards [hbnd,eventually_gt_atTop (0:ℝ)] with T hbnd hT
  intro σ hσ hroot dual
  unfold a03ActualZeroModeLinearizationFinite
  apply integrable_finsetSum
  intro positive _
  apply integrable_finsetSum
  intro i hi
  have hnn : 0≤C*T^(2*s+ε)*a03ActualZeroModeBlockMass T s f g i :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hT.le _)) (a03ActualZeroModeBlockMass_nonneg T s f g i)
  apply a03_mellin_integrableOn_Icc_of_bound _
    (a03ActualZeroModeLinearizationBlock_mellin_stronglyMeasurable dual positive Φ hΦ.continuous.measurable c T s σ f g i) hnn
  intro v hv
  exact hbnd σ hσ hroot dual positive v (abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv)) i hi

theorem a03_actual_source_log_zero_sub_linear_uniform_oT
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s<1/2)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hη : 0<η)
    (hexp : (a+b)/2+3*s+η/2+ε<1) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      IntegrableOn (fun v => a03ActualSourceLinearZeroFinite dual Φ c T a b s η v σ f g)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualSourceLeadingZeroMoment dual Φ c T a b s η θ σ f g-
        a03ActualSourceLinearZeroMoment dual Φ c T a b s η θ σ f g‖≤δ*T := by
  intro δ hδ
  filter_upwards [a03_actual_zero_linearization_moment_eventually_integrable ha hab hlen hs f g hf hg hΦ hΦs hc hc1 hε hκ hθ hR,
    a03_actual_zero_linearization_weighted_moment_uniform_oT ha hab hlen hs0 hs f g hf hg hΦ hΦs hc hc1 hε hκ hθ hR hη hexp δ hδ,
    a03_actual_source_Gamma_zero_sub_leading_uniform_oT ha hab hlen hs0 hs f g hf hg hΦ hΦs hc hc1 hε hκ hθ hR hη
      (by linarith : (a+b)/2+s+η/2+ε<1) 1 (by norm_num),
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),eventually_gt_atTop (0:ℝ)]
    with T hi hb hl hsmall hT
  intro σ hσ hroot dual
  have hi := hi σ hσ hroot dual
  have hl := (hl σ hσ hroot dual).2.1
  have he := a03ActualZeroModeLinearizationFinite_eq_log_sub_linear hΦ.continuous hΦs hc.le hT a b s η
  have hlin : IntegrableOn (fun v => a03ActualSourceLinearZeroFinite dual Φ c T a b s η v σ f g)
      (Icc (-θ*Real.log T) (θ*Real.log T)) := by
    apply (hl.sub hi).congr
    exact ae_of_all _ fun v => by
      simp only [Pi.sub_apply]
      rw [he v σ (hsmall σ hσ) dual f g]
      ring
  refine ⟨hlin,?_⟩
  have hem : a03ActualZeroModeLinearizationMoment dual Φ c T a b s η θ σ f g=
      a03ActualSourceLeadingZeroMoment dual Φ c T a b s η θ σ f g-
        a03ActualSourceLinearZeroMoment dual Φ c T a b s η θ σ f g := by
    unfold a03ActualZeroModeLinearizationMoment a03ActualSourceLeadingZeroMoment a03ActualSourceLinearZeroMoment
    simp_rw [he _ σ (hsmall σ hσ) dual f g]
    exact integral_sub hl hlin
  rw [←hem]
  exact hb σ hσ hroot dual

theorem a03_actual_finite_log_zero_sub_linear_uniform_oT
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s<1/2)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hη : 0<η)
    (hexp : (a+b)/2+3*s+η/2+ε<1) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      ‖a03ActualFiniteLeadingZeroMoment dual c T a b s η θ σ f g Φ-
        a03ActualFiniteLinearZeroMoment dual c T a b s η θ σ f g Φ‖≤δ*T := by
  intro δ hδ
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 := (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  filter_upwards [a03_actual_source_log_zero_sub_linear_uniform_oT ha hab hlen hs0 hs f g hf hg
    hΦc hΦs hc hc1 hε hκ hθ hR hη hexp δ hδ] with T hb
  intro σ hσ hroot dual
  have hb := (hb σ hσ hroot dual).2
  have hconst : ‖(1/(2*Real.pi):ℂ)‖≤1 := by
    rw [norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    exact (div_le_one (by positivity : (0:ℝ)<2*Real.pi)).mpr (by linarith [Real.pi_gt_three])
  unfold a03ActualFiniteLeadingZeroMoment a03ActualFiniteLinearZeroMoment
  rw [←mul_sub,norm_mul]
  exact (mul_le_mul hconst hb (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)


theorem a03_actual_finite_Gamma_zero_sub_linear_uniform_oT
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s<1/2)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hη : 0<η)
    (hexp : (a+b)/2+3*s+η/2+ε<1) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      ‖a03ActualFiniteGammaZeroMoment dual c T a b s η θ σ f g Φ-
        a03ActualFiniteLinearZeroMoment dual c T a b s η θ σ f g Φ‖≤δ*T := by
  intro δ hδ
  filter_upwards [a03_actual_finite_Gamma_zero_sub_leading_uniform_oT ha hab hlen hs0 hs f g Φ hf hg hΦ
      hc hc1 hε hκ hθ hR hη (by linarith : (a+b)/2+s+η/2+ε<1) (δ/2) (by positivity),
    a03_actual_finite_log_zero_sub_linear_uniform_oT ha hab hlen hs0 hs f g Φ hf hg hΦ
      hc hc1 hε hκ hθ hR hη hexp (δ/2) (by positivity)] with T hΓ hlin
  intro σ hσ hroot dual
  have hΓ := hΓ σ hσ hroot dual
  have hlin := hlin σ hσ hroot dual
  have hn := norm_sub_le_norm_sub_add_norm_sub
    (a03ActualFiniteGammaZeroMoment dual c T a b s η θ σ f g Φ)
    (a03ActualFiniteLeadingZeroMoment dual c T a b s η θ σ f g Φ)
    (a03ActualFiniteLinearZeroMoment dual c T a b s η θ σ f g Φ)
  exact hn.trans (by linarith)

theorem a03_actual_finite_Gamma_zero_sub_linear_compact_uniform_oT
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s<1/2)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) {c ε θ η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hθ : 0≤θ) (hη : 0<η) (hexp : (a+b)/2+3*s+η/2+ε<1) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ dual : Bool,
      ‖a03ActualFiniteGammaZeroMoment dual c T a b s η θ σ f g Φ-
        a03ActualFiniteLinearZeroMoment dual c T a b s η θ σ f g Φ‖≤δ*T := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  intro δ hδ
  filter_upwards [a03_actual_finite_Gamma_zero_sub_linear_uniform_oT ha hab hlen hs0 hs f g Φ hf hg hΦ
    hc hc1 hε hκ hθ hR hη hexp δ hδ] with T hb
  intro σ hσ dual
  have hσR (j : Fin 4) : ‖σ j‖≤R := ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left _ _)
  exact hb σ hσR (hroot σ hσ) dual


theorem a03_actual_zero_replacement_slack_numerics {a b s η : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs : s≤1/8) (hη : η≤1/8) :
    0<rectangularSlack a b/128 ∧ rectangularSlack a b/128≤1 ∧
      2*(rectangularSlack a b/128)<rectangularSlack a b/32 ∧
      (a+b)/2+3*s+η/2+rectangularSlack a b/32<1 := by
  have hb : 0≤b := ha.trans hab
  dsimp [rectangularSlack]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

theorem a03_actual_finite_Gamma_zero_sub_linear_compact_uniform_oT_slack
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    {a b s η : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (hs0 : 0≤s) (hs : s≤1/8) (hη0 : 0<η) (hη : η≤1/8)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) {θ : ℝ} (hθ : 0≤θ) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ dual : Bool,
      ‖a03ActualFiniteGammaZeroMoment dual (rectangularSlack a b/128) T a b s η θ σ f g Φ-
        a03ActualFiniteLinearZeroMoment dual (rectangularSlack a b/128) T a b s η θ σ f g Φ‖≤δ*T := by
  obtain ⟨hc,hc1,hε,hexp⟩ := a03_actual_zero_replacement_slack_numerics ha hab hlen hs hη
  exact a03_actual_finite_Gamma_zero_sub_linear_compact_uniform_oT K hK hκ hroot ha hab hlen hs0
    (by linarith : s<1/2) f g Φ hf hg hΦ hc hc1 hε hθ hη0 hexp

end
end SixthMoment
