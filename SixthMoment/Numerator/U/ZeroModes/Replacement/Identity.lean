import SixthMoment.Numerator.U.Sources.ActualZeroTermIntegrability
import SixthMoment.Numerator.U.ZeroModes.Replacement.Measurability
import SixthMoment.Numerator.U.ZeroModes.Replacement.Moment

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03SixTensorPhysicalZeroMode_sub (F G : A03SixTensorSpace→ℂ)
    (m n : Bool) (q : QuadraticScales) (α β : ℕ→ℂ)
    (hF : ∀ v∈quadraticMainIndexSet q,IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
      F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) (Ioi 0))
    (hG : ∀ v∈quadraticMainIndexSet q,IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
      G (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) (Ioi 0)) :
    a03SixTensorPhysicalZeroMode (fun y => F y-G y) m n q α β=
      a03SixTensorPhysicalZeroMode F m n q α β-a03SixTensorPhysicalZeroMode G m n q α β := by
  unfold a03PhysicalZeroSmoothMask at hF hG
  unfold a03SixTensorPhysicalZeroMode
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [mul_sub]
  rw [integral_sub (hF v hv) (hG v hv)]
  ring

theorem a03_actual_zero_replacement_eventually_eq_actual_sub_leading
    (f g : ℝ→ℝ) {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ A B H : ℝ,0<A → 0<B → 0<H → ∀ k : Fin 4→ℕ,
      ∀ dual positive : Bool,∀ v : ℝ,|v|≤θ*Real.log T →
      let α := a03SourceShifts dual T σ
      let p := phaseActualNearTensorData T σ α v A B H k positive
      a03EndpointPhysicalSortedZeroMode (a03ZeroModeReplacementKernel dual Φ c p) T A B H
        f g k=
        a03EndpointPhysicalSortedZeroMode (a03SourceRawKernel dual Φ c p) T A B H f g k-
        a03EndpointPhysicalSortedZeroMode (a03ZeroModeLeadingKernel dual Φ c p) T A B H f g k := by
  filter_upwards [a03_replacement_tensor_eventually_eq_actual_sub_leading hΦ hΦs hc hc1 hθ,
    a03_dual_replacement_tensor_eventually_eq_actual_sub_leading hΦ hΦs hc hc1 hκ hθ hR,
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    bblrGamma_logarithmic_strip_large hc.le hc1 hθ,eventually_ge_atTop (10:ℝ)]
    with T hmain hdual hsmall hlarge hT
  intro σ hσ hroot A B H hA hB hH k dual positive v hv
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
    exact bblrSixShifts_norm_le _ (hsmall σ hσ) _
  have hTp : 0<T := by linarith
  have hqM₁ : 0<q.M₁ := boundaryActual_scale_pos _
  have hqM₂ : 0<q.M₂ := boundaryActual_scale_pos _
  have hM₂ : 0<qs.M₂ := by dsimp only [qs,phasePairSwapScales]; split_ifs; exact hqM₁; exact hqM₂
  have hF : ∀ w∈quadraticMainIndexSet qs,IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n qs w x*
      a03SourceRawKernel dual Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n qs w x))) (Ioi 0) := by
    intro w hw
    have hw1 (j : Fin 5) : 1≤w j := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
    cases dual
    · exact a03ActualTensorRawKernel_physical_term_integrable hΦ hΦs hc.le p hT hα (hlarge v hv) m n qs hM₂ w hw1
    · exact a03ActualDualTensorRawKernel_physical_term_integrable hΦ hΦs hc.le p hT hα (hsmall σ hσ) (hlarge v hv) m n qs hM₂ w hw1
  have hG : ∀ w∈quadraticMainIndexSet qs,IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n qs w x*
      a03ZeroModeLeadingKernel dual Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n qs w x))) (Ioi 0) := by
    intro w hw
    have hw1 (j : Fin 5) : 1≤w j := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
    cases dual
    · exact a03LeadingTensorRawKernel_physical_term_integrable hΦ.continuous hΦs hc.le p hTp hα m n qs hM₂ w hw1
    · exact a03LeadingDualTensorRawKernel_physical_term_integrable hΦ.continuous hΦs hc.le p hTp hα m n qs hM₂ w hw1
  have he : a03ZeroModeReplacementKernel dual Φ c p=
      fun y => a03SourceRawKernel dual Φ c p y-a03ZeroModeLeadingKernel dual Φ c p y := by
    funext y
    cases dual
    · exact hmain σ α hα v p.r p.s hv y
    · exact hdual σ α hσ hα hroot v p.r p.s hv y
  rw [he]
  exact a03SixTensorPhysicalZeroMode_sub _ _ m n qs _ _ hF hG


def a03ActualZeroModeGammaReplacementBlock (dual positive : Bool) (Φ : ℝ→ℂ)
    (c T s v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℂ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let α := a03SourceShifts dual T σ
  let p := phaseActualNearTensorData T σ α v A B H i.2 positive
  if phaseActualActiveNearBlock T A B H (T^(s-1)) f g i.2 then
    (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*
      (a03EndpointPhysicalSortedZeroMode (a03SourceRawKernel dual Φ c p) T A B H f g i.2-
        a03EndpointPhysicalSortedZeroMode (a03ZeroModeLeadingKernel dual Φ c p) T A B H f g i.2)
  else 0

def a03ActualZeroModeGammaReplacementFinite (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s η v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool, ∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+η/2)) (T^(2+η)),a03ActualZeroModeGammaReplacementBlock dual positive Φ c T s v σ f g i

def a03ActualZeroModeGammaReplacementMoment (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s η θ : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∫ v in Icc (-θ*Real.log T) (θ*Real.log T),a03ActualZeroModeGammaReplacementFinite dual Φ c T a b s η v σ f g

theorem a03_actual_gamma_zero_replacement_moment_eventually_eq_symbol
    (f g : ℝ→ℝ) {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (a b s η : ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      (∀ v∈Icc (-θ*Real.log T) (θ*Real.log T),
        a03ActualZeroModeGammaReplacementFinite dual Φ c T a b s η v σ f g=
          a03ActualZeroModeReplacementFinite dual Φ c T a b s η v σ f g) ∧
      a03ActualZeroModeGammaReplacementMoment dual Φ c T a b s η θ σ f g=
        a03ActualZeroModeReplacementMoment dual Φ c T a b s η θ σ f g := by
  filter_upwards [a03_actual_zero_replacement_eventually_eq_actual_sub_leading f g hΦ hΦs hc hc1 hκ hθ hR]
    with T he
  intro σ hσ hroot dual
  have hpoint (v : ℝ) (hv : v∈Icc (-θ*Real.log T) (θ*Real.log T)) :
      a03ActualZeroModeGammaReplacementFinite dual Φ c T a b s η v σ f g=
        a03ActualZeroModeReplacementFinite dual Φ c T a b s η v σ f g := by
    unfold a03ActualZeroModeGammaReplacementFinite a03ActualZeroModeReplacementFinite
    apply Finset.sum_congr rfl
    intro positive _
    apply Finset.sum_congr rfl
    intro i _
    unfold a03ActualZeroModeGammaReplacementBlock a03ActualZeroModeReplacementBlock
    dsimp only
    split_ifs
    · rw [he σ hσ hroot _ _ _ (boundaryActual_scale_pos _) (boundaryActual_scale_pos _)
        (boundaryActual_scale_pos _) i.2 dual positive v (abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv))]
    · rfl
  refine ⟨hpoint,?_⟩
  apply setIntegral_congr_fun measurableSet_Icc hpoint

theorem a03ActualZeroModeReplacementBlock_mellin_stronglyMeasurable
    (dual positive : Bool) {c : ℝ} (hc : 0<c) (Φ : ℝ→ℂ) (hΦ : Continuous Φ)
    (T s : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :
    StronglyMeasurable (fun v : ℝ => a03ActualZeroModeReplacementBlock dual positive Φ c T s v σ f g i) := by
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let α := a03SourceShifts dual T σ
  have hα : ∀ j,‖α j‖≤1/4 := by
    rw [show α=bblrSixShifts (rawMomentShifts T σ) (if dual then 1 else 0) from a03SourceShifts_eq_six dual T σ]
    exact bblrSixShifts_norm_le _ hσ _
  let F := fun v => a03ZeroModeReplacementKernel dual Φ c (phaseActualNearTensorData T σ α v A B H i.2 positive)
  have hFm : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace => F p.1 p.2) :=
    a03_zero_replacement_kernel_joint_stronglyMeasurable dual hc Φ hΦ T
      (H/(B*(rectangularAFESmoothScale (i.2 2)*rectangularAFESmoothScale (i.2 3))))
      (rectangularGapSign positive) σ α hα hσ
  have hz := a03EndpointPhysicalSortedZeroMode_mellin_stronglyMeasurable F hFm T A B H f g i.2
  have hscale : StronglyMeasurable (fun v : ℝ => a03SourceMellinScaleFactor c v α i.2) := by
    apply Measurable.stronglyMeasurable
    unfold a03SourceMellinScaleFactor
    apply Finset.measurable_prod
    intro j _
    fun_prop
  unfold a03ActualZeroModeReplacementBlock
  dsimp only
  split_ifs
  · exact (hscale.const_mul (T:ℂ)).mul hz
  · exact stronglyMeasurable_const

theorem a03_actual_zero_replacement_moment_eventually_integrable
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs : s<1/2)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      IntegrableOn (fun v => a03ActualZeroModeReplacementFinite dual Φ c T a b s η v σ f g)
        (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  obtain ⟨C,hC,hbnd⟩ := a03_actual_zero_replacement_weighted_block_uniform_bound ha hab hlen hs f g hf hg
    hΦ hΦs hc hc1 hε hκ hθ hR
  filter_upwards [hbnd,rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    eventually_gt_atTop (0:ℝ)] with T hbnd hsmall hT
  intro σ hσ hroot dual
  unfold a03ActualZeroModeReplacementFinite
  apply integrable_finsetSum
  intro positive _
  apply integrable_finsetSum
  intro i hi
  have hnn : 0≤C*T^ε*a03ActualZeroModeBlockMass T s f g i :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hT.le ε)) (a03ActualZeroModeBlockMass_nonneg T s f g i)
  apply a03_mellin_integrableOn_Icc_of_bound _
    (a03ActualZeroModeReplacementBlock_mellin_stronglyMeasurable dual positive hc Φ hΦ.continuous T s σ f g (hsmall σ hσ) i) hnn
  intro v hv
  exact hbnd σ hσ hroot dual positive v (abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv)) i hi

theorem a03_actual_gamma_zero_replacement_uniform_oT
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s<1/2)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hη : 0<η)
    (hexp : (a+b)/2+s+η/2+ε<1) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      IntegrableOn (fun v => a03ActualZeroModeGammaReplacementFinite dual Φ c T a b s η v σ f g)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualZeroModeGammaReplacementMoment dual Φ c T a b s η θ σ f g‖≤δ*T := by
  intro δ hδ
  filter_upwards [a03_actual_gamma_zero_replacement_moment_eventually_eq_symbol f g hΦ hΦs hc hc1 hκ hθ hR a b s η,
    a03_actual_zero_replacement_moment_eventually_integrable ha hab hlen hs f g hf hg hΦ hΦs hc hc1 hε hκ hθ hR,
    a03_actual_zero_replacement_weighted_moment_uniform_oT ha hab hlen hs0 hs f g hf hg hΦ hΦs hc hc1 hε hκ hθ hR hη hexp δ hδ]
    with T he hi hb
  intro σ hσ hroot dual
  have he := he σ hσ hroot dual
  refine ⟨?_,?_⟩
  · apply (hi σ hσ hroot dual).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (he.1 v hv).symm
  · rw [he.2]
    exact hb σ hσ hroot dual

end
end SixthMoment
