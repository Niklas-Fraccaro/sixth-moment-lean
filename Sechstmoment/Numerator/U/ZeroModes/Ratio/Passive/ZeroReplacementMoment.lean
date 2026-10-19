import Sechstmoment.Numerator.U.ZeroModes.PassiveZeroModeUnsortedActualMass
import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.SourceMomentJoin
import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.ZeroReplacementBound

/-! The complete genuine ratio-weighted source Gamma zero is replaced by
the leading linear zero on the literal seven-grid and Mellin interval. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 300000

def a03ActualPassiveRatioSourceLinearZeroBlock (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (dual positive : Bool) (Φ : ℝ→ℂ)
    (c T s εsource v : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℂ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let q := phaseActualScales A B H i.2
  let p := phaseActualNearTensorData T σ α v A B H i.2 positive
  if select i ∧ a03ActualPassiveRatioSourceGoodBlock T s εsource f g i then
    (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*
      a03EndpointPhysicalUnsortedZeroMode
        (a03RatioSourceLinearRawFamilyKernel dual Φ c (Real.log (q.M₁/q.M₂)) (Real.log (q.N₁/q.N₂)) p)
        T A B H f g i.2
  else 0

def a03ActualPassiveRatioSourceLinearZeroFinite (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s u εsource v : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool,∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+u/2)) (T^(2+u)),a03ActualPassiveRatioSourceLinearZeroBlock select dual positive Φ c T s εsource v σ α f g i

def a03ActualPassiveRatioSourceLinearZeroMoment (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s u εsource θ : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∫v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualPassiveRatioSourceLinearZeroFinite select dual Φ c T a b s u εsource v σ α f g

theorem a03ActualPassiveRatioSourceLinearZeroBlock_integrableOn (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop)
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c κ : ℝ} (hT : 1<T) (hlog : 1≤Real.log T) (hc : 0<c) (hκ : 0<κ)
    (σ α : MomentShifts) (hroot : ∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (hα : ∀j,‖α j‖≤1/4) (dual positive : Bool) (s εsource θ : ℝ)
    (f g : ℝ→ℝ) (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :
    IntegrableOn (fun v => a03ActualPassiveRatioSourceLinearZeroBlock select dual positive Φ c T s εsource v σ α f g i)
      (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let q := phaseActualScales A B H i.2
  let r := H/(B*(rectangularAFESmoothScale (i.2 2)*rectangularAFESmoothScale (i.2 3)))
  have hM₂ : 0<q.M₂ := boundaryActual_scale_pos _
  have hq : ∀j,0<a03ZeroModeQuadScales (phasePairSwapScales false false q) j := by
    intro j
    fin_cases j <;> simp [q,phasePairSwapScales,a03ZeroModeQuadScales,phaseActualScales] <;>
      exact boundaryActual_scale_pos _
  have hi := a03SourceSpectralActualRatioLinearZero_set_integrable hΦ hΦs hT hlog hc hκ σ α hroot hα dual
    (Real.log (q.M₁/q.M₂)) (Real.log (q.N₁/q.N₂)) r (rectangularGapSign positive)
    false false q hM₂ hq (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
    (Icc (-θ*Real.log T) (θ*Real.log T))
  unfold a03ActualPassiveRatioSourceLinearZeroBlock
  dsimp only
  split_ifs
  · apply (hi.const_mul (T:ℂ)).congr
    apply ae_of_all
    intro v
    dsimp only
    have hscale : a03ZeroModeMellinScaleFactor (phasePairSwapScales false false q) α ((c:ℂ)+(v:ℂ)*I)=
        a03SourceMellinScaleFactor c v α i.2 := by
      simpa only [q,phasePairSwapScales,Bool.false_eq_true,ite_false] using
        a03ZeroModeMellinScaleFactor_pair_actual false false A B H c v α i.2
    unfold a03SourceSpectralActualRatioLinearZero a03EndpointPhysicalUnsortedZeroMode
      a03RatioSourceLinearRawFamilyKernel
    dsimp only [phaseActualNearTensorData]
    rw [hscale]
    ring
  · exact integrable_zero _ _ _

theorem a03ActualPassiveRatioSourceLinearZeroFinite_integrableOn (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop)
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c κ : ℝ} (hT : 1<T) (hlog : 1≤Real.log T) (hc : 0<c) (hκ : 0<κ)
    (σ α : MomentShifts) (hroot : ∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (hα : ∀j,‖α j‖≤1/4) (dual : Bool) (a b s u εsource θ : ℝ) (f g : ℝ→ℝ) :
    IntegrableOn (fun v => a03ActualPassiveRatioSourceLinearZeroFinite select dual Φ c T a b s u εsource v σ α f g)
      (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  unfold a03ActualPassiveRatioSourceLinearZeroFinite
  apply integrable_finsetSum
  intro positive _
  exact integrable_finsetSum _ (fun i _ =>
    a03ActualPassiveRatioSourceLinearZeroBlock_integrableOn select hΦ hΦs hT hlog hc hκ σ α hroot hα dual positive s εsource θ f g i)

theorem a03_actual_passive_ratio_source_zero_block_replacement_uniform_bound
    {a b s : ℝ} (hs0 : 0≤s) (hs : s<1) (f g : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R u : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (εsource : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀j,‖σ j‖≤R) → (∀j,‖α j‖≤1/4) → (∀j,‖α j‖≤R/Real.log T) →
      (∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ v : ℝ,|v|≤θ*Real.log T →
      ∀ dual positive : Bool,∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,∀ i∈a03ActualSourceBlockGrid (T^a) (T^b)
        (8*T^((a+b)/2+s+u/2)) (T^(2+u)),
      ‖a03ActualPassiveRatioSourceBlockValue select true dual positive Φ c T s εsource v σ α f g i-
          a03ActualPassiveRatioSourceLinearZeroBlock select dual positive Φ c T s εsource v σ α f g i‖≤
        C*(Real.log T)^8*T^(2*s+ε)*a03ActualPassiveUnsortedZeroModeBlockMass T s f g i := by
  obtain ⟨C,hC,hbound⟩ := a03_actual_passive_ratio_Gamma_zero_sub_linear_uniform_mass_bound
    (η:=u) hs0 hs f g hf hg hΦ hΦs hc hc1 hε hκ hθ hR
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with T hbound hT
  intro σ α hσ hα hαnorm hroot v hv dual positive select i hi
  unfold a03ActualPassiveRatioSourceBlockValue a03ActualPassiveRatioSourceLinearZeroBlock a03ActualPassiveUnsortedZeroModeBlockMass
  dsimp only
  by_cases hg : select i ∧ a03ActualPassiveRatioSourceGoodBlock T s εsource f g i
  · rw [ite_eq_left hg,ite_eq_left hg,ite_eq_left hg.2.1]
    simp only [ite_true]
    rw [←mul_sub]
    exact hbound σ α hσ hα hαnorm hroot _ _ _ (boundaryActual_scale_pos _) (boundaryActual_scale_pos _)
      (boundaryActual_scale_pos _) i.2 (Finset.mem_product.mp hi).2 hg.2.2.2.2.1 hg.2.2.2.2.2 hg.2.1 v hv dual positive _ _
  · simp only [hg,ite_false,sub_self,norm_zero]
    change 0≤C*(Real.log T)^8*T^(2*s+ε)*a03ActualPassiveUnsortedZeroModeBlockMass T s f g i
    exact mul_nonneg (by positivity) (a03ActualPassiveUnsortedZeroModeBlockMass_nonneg T s f g i)

theorem a03_actual_passive_unsorted_ratio_zero_weighted_global_mass_isLittleO {a b s u θ e : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hs : 0≤s) (hu : 0<u) (hθ : 0≤θ)
    (hexp : (a+b)/2+s+u/2+e<1)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    (fun T : ℝ => (Real.log T)^8*T^e*a03ActualPassiveUnsortedZeroModeGlobalMass T a b s u θ f g)=o[atTop] (fun T : ℝ => T) := by
  obtain ⟨C,hC,hbound⟩ := a03_actual_passive_unsorted_zero_mode_global_mass_uniform_bound ha hb hs hu hθ f g hf hg
  have ho := (polylog_mul_rpow_isLittleO_id 20 hexp).const_mul_left (4096*C)
  have ho' : (fun T : ℝ => (4096*C)*(Real.log T)^20*T^((a+b)/2+s+u/2+e))=o[atTop] (fun T : ℝ => T) := by
    simpa only [mul_assoc] using ho
  apply (show (fun T : ℝ => (Real.log T)^8*T^e*a03ActualPassiveUnsortedZeroModeGlobalMass T a b s u θ f g)=O[atTop]
    (fun T : ℝ => (4096*C)*(Real.log T)^20*T^((a+b)/2+s+u/2+e)) from ?_).trans_isLittleO ho'
  apply Eventually.isBigO
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hbound hT hlog
  have hmass0 := hbound.1
  rw [Real.norm_of_nonneg (show 0≤(Real.log T)^8*T^e*a03ActualPassiveUnsortedZeroModeGlobalMass T a b s u θ f g by positivity)]
  have hl : (1+Real.log T)^12≤4096*(Real.log T)^12 := by
    have h := pow_le_pow_left₀ (by linarith : 0≤1+Real.log T) (by linarith : 1+Real.log T≤2*Real.log T) 12
    simpa only [mul_pow,show (2:ℝ)^12=4096 by norm_num] using h
  have hp : T^e*T^((a+b)/2+s+u/2)=T^((a+b)/2+s+u/2+e) := by
    rw [←Real.rpow_add (zero_lt_one.trans_le hT)]
    congr 1
    ring
  calc
    _≤(Real.log T)^8*T^e*(C*(1+Real.log T)^12*T^((a+b)/2+s+u/2)) :=
      mul_le_mul_of_nonneg_left hbound.2 (by positivity)
    _≤(Real.log T)^8*T^e*(C*(4096*(Real.log T)^12)*T^((a+b)/2+s+u/2)) := by gcongr
    _=(4096*C)*((Real.log T)^8*(Real.log T)^12)*(T^e*T^((a+b)/2+s+u/2)) := by ring
    _=_ := by rw [←pow_add,hp]

theorem a03_actual_passive_ratio_source_Gamma_zero_sub_linear_uniform_oT
    {a b s : ℝ} (ha : 0≤a) (hb : 0≤b) (hs0 : 0≤s) (hs : s<1)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R u : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hu : 0<u)
    (hexp : (a+b)/2+3*s+u/2+ε<1) (εsource : ℝ) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀j,‖σ j‖≤R) → (∀j,‖α j‖≤1/4) → (∀j,‖α j‖≤R/Real.log T) →
      (∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
      IntegrableOn (fun v => a03ActualPassiveRatioSourceLinearZeroFinite select dual Φ c T a b s u εsource v σ α f g)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualPassiveRatioSourceValueMoment select true dual Φ c T a b s u εsource θ σ α f g-
          a03ActualPassiveRatioSourceLinearZeroMoment select dual Φ c T a b s u εsource θ σ α f g‖≤δ*T := by
  obtain ⟨C,hC,hblock⟩ := a03_actual_passive_ratio_source_zero_block_replacement_uniform_bound
    (u:=u) hs0 hs f g hf hg hΦ hΦs hc hc1 hε hκ hθ hR εsource
  have hexp' : (a+b)/2+s+u/2+(2*s+ε)<1 := by linarith
  have ho := (a03_actual_passive_unsorted_ratio_zero_weighted_global_mass_isLittleO (e:=2*s+ε) ha hb hs0 hu hθ hexp' f g hf hg).const_mul_left C
  intro δ hδ
  filter_upwards [hblock,ho.bound hδ,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    (a03_actual_passive_ratio_source_finite_values_integrableOn false hΦ hΦs hc hc1
      (e:=12*c+1) (by linarith) hκ hθ hR hs a b u εsource f g),
    (a03_actual_passive_ratio_source_finite_values_integrableOn true hΦ hΦs hc hc1
      (e:=12*c+1) (by linarith) hκ hθ hR hs a b u εsource f g),
    (a03_actual_passive_unsorted_zero_mode_global_mass_uniform_bound ha hb hs0 hu hθ f g hf hg).choose_spec.2]
    with T hblock ho hT hlog hΓfalse hΓtrue hmass
  intro σ α hσ hα hαnorm hroot dual select
  have hi := a03ActualPassiveRatioSourceLinearZeroFinite_integrableOn select hΦ.continuous hΦs hT hlog hc hκ σ α hroot hα dual a b s u εsource θ f g
  refine ⟨hi,?_⟩
  have hΓ' : IntegrableOn (fun v => a03ActualPassiveRatioSourceFiniteValue select true dual Φ c T a b s u εsource v σ α f g)
      (Icc (-θ*Real.log T) (θ*Real.log T)) := by
    cases dual
    · exact hΓfalse σ α hσ hα hroot select true
    · exact hΓtrue σ α hσ hα hroot select true
  unfold a03ActualPassiveRatioSourceValueMoment a03ActualPassiveRatioSourceLinearZeroMoment
  rw [←integral_sub hΓ' hi]
  let grid := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  have hfinite (v : ℝ) (hv : |v|≤θ*Real.log T) :
      ‖a03ActualPassiveRatioSourceFiniteValue select true dual Φ c T a b s u εsource v σ α f g-
          a03ActualPassiveRatioSourceLinearZeroFinite select dual Φ c T a b s u εsource v σ α f g‖≤
        2*(C*(Real.log T)^8*T^(2*s+ε)*a03ActualPassiveUnsortedZeroModeFiniteMass T a b s u f g) := by
    unfold a03ActualPassiveRatioSourceFiniteValue a03ActualPassiveRatioSourceLinearZeroFinite
    rw [←Finset.sum_sub_distrib]
    calc
      _≤∑positive : Bool,‖∑i∈grid,
        (a03ActualPassiveRatioSourceBlockValue select true dual positive Φ c T s εsource v σ α f g i-
          a03ActualPassiveRatioSourceLinearZeroBlock select dual positive Φ c T s εsource v σ α f g i)‖ := by
        simpa only [Finset.sum_sub_distrib,grid] using norm_sum_le Finset.univ (fun positive : Bool =>
          (∑i∈grid,a03ActualPassiveRatioSourceBlockValue select true dual positive Φ c T s εsource v σ α f g i)-
            (∑i∈grid,a03ActualPassiveRatioSourceLinearZeroBlock select dual positive Φ c T s εsource v σ α f g i))
      _≤∑_positive : Bool,C*(Real.log T)^8*T^(2*s+ε)*a03ActualPassiveUnsortedZeroModeFiniteMass T a b s u f g := by
        apply Finset.sum_le_sum
        intro positive _
        calc
          _≤∑i∈grid,‖a03ActualPassiveRatioSourceBlockValue select true dual positive Φ c T s εsource v σ α f g i-
            a03ActualPassiveRatioSourceLinearZeroBlock select dual positive Φ c T s εsource v σ α f g i‖ := norm_sum_le _ _
          _≤∑i∈grid,C*(Real.log T)^8*T^(2*s+ε)*a03ActualPassiveUnsortedZeroModeBlockMass T s f g i :=
            Finset.sum_le_sum (hblock σ α hσ hα hαnorm hroot v hv dual positive select)
          _=_ := by simp only [a03ActualPassiveUnsortedZeroModeFiniteMass,grid,Finset.mul_sum]
      _=_ := by simp [two_mul]
  have hn := norm_setIntegral_le_of_norm_le_const_ae'
    (measure_Icc_lt_top : volume (Icc (-θ*Real.log T) (θ*Real.log T))<⊤)
    (ae_of_all volume fun v hv => hfinite v (abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv)))
  have hn' : ‖∫v in Icc (-θ*Real.log T) (θ*Real.log T),
      (a03ActualPassiveRatioSourceFiniteValue select true dual Φ c T a b s u εsource v σ α f g-
        a03ActualPassiveRatioSourceLinearZeroFinite select dual Φ c T a b s u εsource v σ α f g)‖≤
      C*(Real.log T)^8*T^(2*s+ε)*a03ActualPassiveUnsortedZeroModeGlobalMass T a b s u θ f g := by
    apply hn.trans_eq
    rw [Real.volume_real_Icc,max_eq_left (by nlinarith [Real.log_nonneg hT.le])]
    unfold a03ActualPassiveUnsortedZeroModeGlobalMass
    ring
  have hmass0 := hmass.1
  have hnn : 0≤C*((Real.log T)^8*T^(2*s+ε)*a03ActualPassiveUnsortedZeroModeGlobalMass T a b s u θ f g) := by positivity
  rw [Real.norm_of_nonneg hnn,Real.norm_of_nonneg (zero_lt_one.trans hT).le] at ho
  exact hn'.trans (by simpa only [mul_assoc] using ho)

end
end Sechstmoment
