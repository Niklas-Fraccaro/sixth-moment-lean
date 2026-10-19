import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.FiniteGCDVStarJoin
import Sechstmoment.Numerator.U.ZeroModes.Ratio.SevenGridSpectralTail

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_passive_ratio_source_linear_block_spectral_tail_uniform_bound
    {a b : ℝ} (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c θ κ R u : ℝ} (hc : 0<c) (hθ : 0<θ) (hκ : 0<κ) (hR : 0≤R)
    (s εsource N : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀j,‖σ j‖≤R) → (∀j,‖α j‖≤1/4) → (∀j,‖α j‖≤R/Real.log T) →
      (∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual positive : Bool,∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
      ∀ i∈a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)),
      ‖(1/(2*Real.pi):ℂ)*∫v : ℝ in {v : ℝ | θ*Real.log T < |v|},
        a03ActualPassiveRatioSourceLinearZeroBlock select dual positive Φ c T s εsource v σ α f g i‖≤
        C*T^(1-N)*a03ActualPassiveUnsortedZeroModeBlockMass T s f g i := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨C,hC,hbound⟩ := a03_actual_ratio_native_spectral_tail_uniform_mass_bound
    (u:=u) hΦ hSupp hc hθ hκ hR N
  refine ⟨F*G*C,by positivity,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ)] with T hbound hT
  intro σ α hσ hα hαnorm hroot dual positive select i hi
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let q := phaseActualScales A B H i.2
  have hTp : 0<T := zero_lt_one.trans hT
  have hA : 0<A := boundaryActual_scale_pos _
  have hB : 0<B := boundaryActual_scale_pos _
  have hH : 0<H := boundaryActual_scale_pos _
  have hq : ∀j,0<q.size j := boundaryActual_scales_pos A B H i.2 hA hB hH
  simp_rw [a03ActualPassiveRatioSourceLinearZeroBlock_eq_spectral select]
  unfold a03ActualPassiveUnsortedZeroModeBlockMass
  dsimp only
  by_cases hgood : select i ∧ a03ActualPassiveRatioSourceGoodBlock T s εsource f g i
  · simp only [hgood,and_self,ite_true,hgood.2.1,integral_const_mul]
    have hM₂ : 1≤q.M₂ := rectangular_AFE_smooth_scale_ge_one (by have := hgood.2.2.2.2.1; omega)
    have hN₂ : 1≤q.N₂ := rectangular_AFE_smooth_scale_ge_one (by have := hgood.2.2.2.2.2; omega)
    have hprod : q.M*q.N≤T^(2+u) := by
      simpa [q,phaseActualScales,QuadraticScales.M,QuadraticScales.N,Fin.prod_univ_four,mul_assoc]
        using (Finset.mem_filter.mp (Finset.mem_product.mp hi).2).2
    have hb := hbound σ α hσ hα hαnorm hroot dual
      (Real.log (q.M₁/q.M₂)) (Real.log (q.N₁/q.N₂)) (q.H/(q.B*(q.N₁*q.N₂)))
      (rectangularGapSign positive) false false q hq hM₂ hN₂ hprod
      (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B) F G hF hG
      (fun j hj => phaseActualAmplifierCoefficient_norm_le_reciprocal_sqrt T A f hF hfb hj)
      (fun j hj => phaseActualAmplifierCoefficient_norm_le_reciprocal_sqrt T B g hG hgb hj)
    rw [show (1/(2*Real.pi):ℂ)*((T:ℂ)*∫v : ℝ in {v : ℝ | θ*Real.log T < |v|},_)=
      (T:ℂ)*((1/(2*Real.pi):ℂ)*∫v : ℝ in {v : ℝ | θ*Real.log T < |v|},_) by ring,
      norm_mul,Complex.norm_real,Real.norm_of_nonneg hTp.le]
    apply (mul_le_mul_of_nonneg_left hb hTp.le).trans_eq
    have hp : T*T^(-N)=T^(1-N) := by
      calc
        _=T^(1:ℝ)*T^(-N) := by rw [Real.rpow_one]
        _=T^(1+(-N)) := (Real.rpow_add hTp _ _).symm
        _=_ := rfl
    rw [show T*(F*G*C*T^(-N)*a03ZeroModeLiteralMass q)=
      F*G*C*(T*T^(-N))*a03ZeroModeLiteralMass q by ring,hp]
  · simp only [hgood,ite_false,integral_zero,mul_zero,norm_zero]
    have hmass := a03ZeroModeLiteralMass_nonneg q
    split_ifs <;> positivity

theorem a03_actual_passive_ratio_source_linear_spectral_tail_uniform_rapid
    {a b s u : ℝ} (ha : 0≤a) (hb : 0≤b) (hs : 0≤s) (hu : 0<u)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c θ κ R : ℝ} (hc : 0<c) (hθ : 0<θ) (hκ : 0<κ) (hR : 0≤R)
    (εsource N : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀j,‖σ j‖≤R) → (∀j,‖α j‖≤1/4) → (∀j,‖α j‖≤R/Real.log T) →
      (∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
      ‖(1/(2*Real.pi):ℂ)*∫v : ℝ in {v : ℝ | θ*Real.log T < |v|},
        a03ActualPassiveRatioSourceLinearZeroFinite select dual Φ c T a b s u εsource v σ α f g‖≤C*T^(-N) := by
  let h := (a+b)/2+s+u/2
  obtain ⟨C,hC,hblock⟩ := a03_actual_passive_ratio_source_linear_block_spectral_tail_uniform_bound
    (u:=u) f g hf hg hΦ hSupp hc hθ hκ hR s εsource (N+h+2)
  obtain ⟨D,hD,hmass⟩ := a03_actual_passive_unsorted_zero_mode_finite_mass_uniform_bound ha hb hs hu f g hf hg
  have hlog : ∀ᶠ T : ℝ in atTop,(1+Real.log T)^11≤2048*T := by
    have hl := (log_pow_isLittleO_rpow 11 (δ:=1) zero_lt_one).bound zero_lt_one
    filter_upwards [hl,eventually_gt_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hl hT hL
    have hh : (Real.log T)^11≤T := by
      simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hT),
        abs_of_nonneg (by positivity : 0≤(Real.log T)^11),one_mul] using hl
    calc
      _≤(2*Real.log T)^11 := pow_le_pow_left₀ (by linarith) (by linarith) _
      _=2048*(Real.log T)^11 := by rw [mul_pow]; norm_num
      _≤_ := mul_le_mul_of_nonneg_left hh (by norm_num)
  refine ⟨4096*C*D,by positivity,?_⟩
  filter_upwards [hblock,hmass,hlog,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hblock hmass hlog hT hL
  intro σ α hσ hα hαnorm hroot dual select
  have hi (positive : Bool) (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :=
    (a03ActualPassiveRatioSourceLinearZeroBlock_integrable_full select hΦ hSupp hT hL hc hκ σ α hroot hα dual positive s εsource f g i).restrict (s := {v : ℝ | θ*Real.log T < |v|})
  unfold a03ActualPassiveRatioSourceLinearZeroFinite
  rw [integral_finsetSum _ (fun positive _ => integrable_finsetSum _ (fun i _ => hi positive i)),Finset.mul_sum]
  have hsign (positive : Bool) :
      ‖(1/(2*Real.pi):ℂ)*∫v : ℝ in {v : ℝ | θ*Real.log T < |v|},
        ∑i∈a03ActualSourceBlockGrid (T^a) (T^b) (8*T^h) (T^(2+u)),
          a03ActualPassiveRatioSourceLinearZeroBlock select dual positive Φ c T s εsource v σ α f g i‖≤
      C*T^(1-(N+h+2))*a03ActualPassiveUnsortedZeroModeFiniteMass T a b s u f g := by
    rw [integral_finsetSum _ (fun i _ => hi positive i),Finset.mul_sum]
    exact ((norm_sum_le _ _).trans (Finset.sum_le_sum
      (hblock σ α hσ hα hαnorm hroot dual positive select))).trans_eq
        (by simp only [a03ActualPassiveUnsortedZeroModeFiniteMass,h,Finset.mul_sum])
  calc
    _≤∑_positive : Bool,C*T^(1-(N+h+2))*a03ActualPassiveUnsortedZeroModeFiniteMass T a b s u f g :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun positive _ => hsign positive))
    _=2*(C*T^(1-(N+h+2))*a03ActualPassiveUnsortedZeroModeFiniteMass T a b s u f g) := by simp [two_mul]
    _≤2*(C*T^(1-(N+h+2))*(D*(1+Real.log T)^11*T^h)) := by gcongr; exact hmass.2
    _≤2*(C*T^(1-(N+h+2))*(D*(2048*T)*T^h)) := by gcongr
    _=_ := by
      have hp : T^(1-(N+h+2))*T*T^h=T^(-N) := by
        calc
          _=T^(1-(N+h+2))*T^(1:ℝ)*T^h := by rw [Real.rpow_one]
          _=T^((1-(N+h+2))+1+h) := by rw [←Real.rpow_add (zero_lt_one.trans hT),←Real.rpow_add (zero_lt_one.trans hT)]
          _=_ := by congr 1; ring
      rw [show 2*(C*T^(1-(N+h+2))*(D*(2048*T)*T^h))=
        (4096*C*D)*(T^(1-(N+h+2))*T*T^h) by ring,hp]

theorem a03_actual_passive_ratio_source_linear_core_sub_full_uniform_rapid
    {a b s u : ℝ} (ha : 0≤a) (hb : 0≤b) (hs : 0≤s) (hu : 0<u)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c θ κ R : ℝ} (hc : 0<c) (hθ : 0<θ) (hκ : 0<κ) (hR : 0≤R)
    (εsource N : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀j,‖σ j‖≤R) → (∀j,‖α j‖≤1/4) → (∀j,‖α j‖≤R/Real.log T) →
      (∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
      ‖(1/(2*Real.pi):ℂ)*a03ActualPassiveRatioSourceLinearZeroMoment select dual Φ c T a b s u εsource θ σ α f g-
        a03ActualPassiveRatioSourceLinearZeroFullMoment select dual Φ c T a b s u εsource σ α f g‖≤C*T^(-N) := by
  obtain ⟨C,hC,hbound⟩ := a03_actual_passive_ratio_source_linear_spectral_tail_uniform_rapid
    ha hb hs hu f g hf hg hΦ hSupp hc hθ hκ hR εsource N
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hbound hT hL
  intro σ α hσ hα hαnorm hroot dual select
  have hi := a03ActualPassiveRatioSourceLinearZeroFinite_integrable_full select hΦ hSupp hT hL hc hκ σ α hroot hα dual a b s u εsource f g
  have ht : MeasurableSet {v : ℝ | θ*Real.log T < |v|} := (isOpen_lt continuous_const continuous_abs).measurableSet
  have he := integral_add_compl ht hi
  have hset : {v : ℝ | θ*Real.log T < |v|}ᶜ=Icc (-θ*Real.log T) (θ*Real.log T) := by
    ext v
    simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_lt,Set.mem_Icc,neg_mul]
    exact abs_le
  rw [hset] at he
  unfold a03ActualPassiveRatioSourceLinearZeroMoment a03ActualPassiveRatioSourceLinearZeroFullMoment
  rw [←he,show (1/(2*Real.pi):ℂ)*(∫v : ℝ in Icc (-θ*Real.log T) (θ*Real.log T),_)-
      (1/(2*Real.pi):ℂ)*((∫v : ℝ in {v : ℝ | θ*Real.log T < |v|},_)+
        (∫v : ℝ in Icc (-θ*Real.log T) (θ*Real.log T),_))=
      -((1/(2*Real.pi):ℂ)*∫v : ℝ in {v : ℝ | θ*Real.log T < |v|},_) by ring,norm_neg]
  exact hbound σ α hσ hα hαnorm hroot dual select


end
end Sechstmoment
