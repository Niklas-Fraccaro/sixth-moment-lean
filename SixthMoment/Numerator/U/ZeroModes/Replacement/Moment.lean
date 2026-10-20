import SixthMoment.Numerator.U.ZeroModes.PhysicalReplacement

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03SourceShifts_eq_six (dual : Bool) (T : ℝ) (σ : MomentShifts) :
    a03SourceShifts dual T σ=bblrSixShifts (rawMomentShifts T σ) (if dual then 1 else 0) := by
  cases dual <;> simp [a03SourceShifts,bblrSixShifts]

def a03ActualZeroModeReplacementBlock (dual positive : Bool) (Φ : ℝ→ℂ)
    (c T s v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℂ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let α := a03SourceShifts dual T σ
  let p := phaseActualNearTensorData T σ α v A B H i.2 positive
  if phaseActualActiveNearBlock T A B H (T^(s-1)) f g i.2 then
    (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*
      a03EndpointPhysicalSortedZeroMode (a03ZeroModeReplacementKernel dual Φ c p) T A B H f g i.2
  else 0

def a03ActualZeroModeReplacementFinite (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s η v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool, ∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+η/2)) (T^(2+η)),a03ActualZeroModeReplacementBlock dual positive Φ c T s v σ f g i

def a03ActualZeroModeReplacementMoment (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s η θ : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∫ v in Icc (-θ*Real.log T) (θ*Real.log T),a03ActualZeroModeReplacementFinite dual Φ c T a b s η v σ f g

theorem a03_actual_zero_replacement_moment_bound
    {T a b s η ε θ C : ℝ} (hT : 1≤T) (hθ : 0≤θ)
    (dual : Bool) (Φ : ℝ→ℂ) (c : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ)
    (hblock : ∀ v : ℝ,|v|≤θ*Real.log T → ∀ positive : Bool,
      ∀ i∈a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+η/2)) (T^(2+η)),
        ‖a03ActualZeroModeReplacementBlock dual positive Φ c T s v σ f g i‖≤
          C*T^ε*a03ActualZeroModeBlockMass T s f g i) :
    ‖a03ActualZeroModeReplacementMoment dual Φ c T a b s η θ σ f g‖≤
      C*T^ε*a03ActualZeroModeGlobalMass T a b s η θ f g := by
  let grid := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+η/2)) (T^(2+η))
  have hfinite (v : ℝ) (hv : |v|≤θ*Real.log T) :
      ‖a03ActualZeroModeReplacementFinite dual Φ c T a b s η v σ f g‖≤
        2*(C*T^ε*a03ActualZeroModeFiniteMass T a b s η f g) := by
    unfold a03ActualZeroModeReplacementFinite
    calc
      _≤∑ positive : Bool,‖∑ i∈grid,a03ActualZeroModeReplacementBlock dual positive Φ c T s v σ f g i‖ := norm_sum_le _ _
      _≤∑ _positive : Bool,C*T^ε*a03ActualZeroModeFiniteMass T a b s η f g := by
        apply Finset.sum_le_sum
        intro positive _
        calc
          _≤∑ i∈grid,‖a03ActualZeroModeReplacementBlock dual positive Φ c T s v σ f g i‖ := norm_sum_le _ _
          _≤∑ i∈grid,C*T^ε*a03ActualZeroModeBlockMass T s f g i := Finset.sum_le_sum (hblock v hv positive)
          _=_ := by simp only [a03ActualZeroModeFiniteMass,grid,Finset.mul_sum]
      _=_ := by simp [two_mul]
  have hb := norm_setIntegral_le_of_norm_le_const_ae'
    (measure_Icc_lt_top : volume (Icc (-θ*Real.log T) (θ*Real.log T))<⊤)
    (ae_of_all volume fun v hv => hfinite v (abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv)))
  unfold a03ActualZeroModeReplacementMoment
  apply hb.trans_eq
  rw [Real.volume_real_Icc,max_eq_left (by nlinarith [Real.log_nonneg hT])]
  unfold a03ActualZeroModeGlobalMass
  ring

theorem a03_actual_zero_replacement_weighted_block_uniform_bound
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs : s<1/2)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ dual positive : Bool,∀ v : ℝ,|v|≤θ*Real.log T →
      ∀ i∈a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+η/2)) (T^(2+η)),
        ‖a03ActualZeroModeReplacementBlock dual positive Φ c T s v σ f g i‖≤
          C*T^ε*a03ActualZeroModeBlockMass T s f g i := by
  obtain ⟨C,hC,hbnd⟩ := a03_zero_replacement_native_zero_uniform_mass_bound f g hf hg hΦ hΦs hc hc1 hε hκ hθ hR
  refine ⟨C,hC,?_⟩
  filter_upwards [hbnd,phase_actual_source_near_double_unit_blocks_excluded ha hab hlen hs f g hf hg]
    with T hbnd hunit
  intro σ hσ hroot dual positive v hv i hi
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  have hA : 0<A := boundaryActual_scale_pos _
  have hB : 0<B := boundaryActual_scale_pos _
  have hH : 0<H := boundaryActual_scale_pos _
  unfold a03ActualZeroModeReplacementBlock a03ActualZeroModeBlockMass
  dsimp only
  split_ifs with hactive
  · have hidx : ∀ j,i.2 j≠1 := by
      obtain ⟨u,w,h,n,positive,hu,hw,hω,hh,hrel,hnear⟩ := hactive
      exact boundaryActual_active_indices i.2 n hω
    have hu := hunit A B H hA hB hH i.2 hactive
    have hb := hbnd σ hσ hroot (if dual then 1 else 0) A B H hA hB hH i.2
      (Finset.mem_product.mp hi).2 hidx hu.1 hu.2 v hv dual positive
    simpa only [←a03SourceShifts_eq_six dual T σ] using hb
  · simp

theorem a03_actual_zero_replacement_weighted_moment_uniform_bound
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs : s<1/2)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      ‖a03ActualZeroModeReplacementMoment dual Φ c T a b s η θ σ f g‖≤
        C*T^ε*a03ActualZeroModeGlobalMass T a b s η θ f g := by
  obtain ⟨C,hC,hbnd⟩ := a03_actual_zero_replacement_weighted_block_uniform_bound ha hab hlen hs f g hf hg
    hΦ hΦs hc hc1 hε hκ hθ hR
  refine ⟨C,hC,?_⟩
  filter_upwards [hbnd,eventually_ge_atTop (1:ℝ)] with T hbnd hT
  intro σ hσ hroot dual
  exact a03_actual_zero_replacement_moment_bound hT hθ dual Φ c σ f g
    (fun v hv positive => hbnd σ hσ hroot dual positive v hv)

theorem a03_actual_zero_replacement_weighted_moment_uniform_oT
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s<1/2)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hη : 0<η)
    (hexp : (a+b)/2+s+η/2+ε<1) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      ‖a03ActualZeroModeReplacementMoment dual Φ c T a b s η θ σ f g‖≤δ*T := by
  obtain ⟨C,hC,hbnd⟩ := a03_actual_zero_replacement_weighted_moment_uniform_bound ha hab hlen hs f g hf hg
    hΦ hΦs hc hc1 hε hκ hθ hR
  have ho := (a03_actual_zero_mode_weighted_global_mass_isLittleO ha (ha.trans hab) hs0 hη hθ hexp f g hf hg).const_mul_left C
  intro δ hδ
  filter_upwards [hbnd,ho.bound hδ,eventually_ge_atTop (1:ℝ),
    (a03_actual_zero_mode_global_mass_uniform_bound ha (ha.trans hab) hs0 hη hθ f g hf hg).choose_spec.2]
    with T hbnd ho hT hmass
  intro σ hσ hroot dual
  have hmass0 := hmass.1
  have hnn : 0≤C*(T^ε*a03ActualZeroModeGlobalMass T a b s η θ f g) := by positivity
  rw [Real.norm_of_nonneg hnn,Real.norm_of_nonneg (zero_le_one.trans hT)] at ho
  exact (hbnd σ hσ hroot dual).trans (by simpa only [mul_assoc] using ho)

end
end SixthMoment
