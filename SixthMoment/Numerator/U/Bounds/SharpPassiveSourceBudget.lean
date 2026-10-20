import SixthMoment.Numerator.U.ZeroModes.GCDMasks.ActivePassiveComparison

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_sharp_passive_physical_sub_Gamma_mass_budget_smaller (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource e c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+e<rectangularSlack a b) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
      ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
        IntegrableOn (fun v => a03ActualPassiveRatioSourceFiniteValue select false dual Φ c T a b s u εsource v σ α f g)
          (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
        IntegrableOn (fun v => a03ActualPassiveRatioSourceFiniteValue select true dual Φ c T a b s u εsource v σ α f g)
          (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
        ‖a03ActualPassiveRatioSourceValueMoment select false dual Φ c T a b s u εsource θ σ α f g-
          a03ActualPassiveRatioSourceValueMoment select true dual Φ c T a b s u εsource θ σ α f g‖≤
            C*T^e*a03ActualPassiveSoftSourceGlobalMajorant T a b s u εsource θ f g := by
  obtain ⟨S,U,C,hS,hS2,hScap,hU,hUcap,_hlossS,_hlossU,hC,hphysical⟩ :=
    a03_actual_ratio_tensor_passive_soft_source_physical_bound dual hinput ha hab hlen hεsource
      f g hf hg hΦ hΦs hc hc1 he hκ hθ hR hloss
  refine ⟨S,U,hS,hS2,hScap,hU,hUcap,?_⟩
  intro s u hs hss hu huu
  have hs2 : s<1/2 := hss.trans_lt hS2
  let D := C*a03SourceMellinBound R u
  have hD : 0≤D := by dsimp [D,a03SourceMellinBound]; positivity
  have hbound : ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
      ‖a03ActualPassiveRatioSourceErrorMoment select dual Φ c e T a b s u εsource θ σ α f g‖≤
        D*T^e*a03ActualPassiveSoftSourceGlobalMajorant T a b s u εsource θ f g := by
    filter_upwards [hphysical,eventually_ge_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R))] with T hphysical hT hlog hlogR
    intro σ α hσ hα hroot select
    have hL : 0<Real.log T := zero_lt_one.trans_le hlog
    have hαsmall : ∀ j,‖α j‖≤1/4 := fun j =>
      (hα j).trans ((div_le_iff₀ hL).mpr (by linarith))
    apply a03_actual_passive_ratio_source_error_moment_bound select hT hθ dual Φ c σ α f g
    intro v hv positive i hi
    have hk := (Finset.mem_product.mp hi).2
    apply a03_actual_passive_ratio_source_restored_block_bound select (zero_lt_one.trans_le hT) hlog hR hc.le hc1 hC
      dual positive Φ σ α hα v f g i hk
    intro hgood
    rcases hgood with ⟨hactive,hmsoft,hnsoft,hk1,hk3⟩
    obtain ⟨hk0,hactive0⟩ := a03_actual_passive_source_restricted_domain hT hss huu f g i.2 hk hactive
    exact hphysical _ _ _ (boundaryActual_scale_ge_two_thirds (i.1 0))
      (boundaryActual_scale_ge_two_thirds (i.1 1)) (boundaryActual_scale_ge_two_thirds (i.1 2))
      i.2 hk0 hactive0 hmsoft hnsoft hk1 hk3 σ α hσ hαsmall hroot v hv positive _ _
  refine ⟨D,hD,?_⟩
  filter_upwards [hbound,
    a03_actual_passive_ratio_source_finite_values_integrableOn dual hΦ hΦs hc hc1 he hκ hθ hR
      (hs2.trans (by norm_num)) a b u εsource f g,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R)),
    eventually_ge_atTop (1:ℝ)] with T hb hi hlog hlogR hT
  intro σ α hσ hα hroot select
  have hL : 0<Real.log T := zero_lt_one.trans_le hlog
  have hαsmall : ∀ j,‖α j‖≤1/4 := fun j =>
    (hα j).trans ((div_le_iff₀ hL).mpr (by linarith))
  have hip := hi σ α hσ hαsmall hroot select false
  have hiz := hi σ α hσ hαsmall hroot select true
  refine ⟨hip,hiz,?_⟩
  rw [←a03ActualPassiveRatioSourceErrorMoment_eq_physical_sub_zero select (zero_lt_one.trans_le hT)
    dual Φ c e a b s u εsource θ σ α f g hip hiz]
  exact hb σ α hσ hα hroot select


theorem a03_sharp_passive_Gamma_sub_linear_mass_budget
    {a b s : ℝ} (hs0 : 0≤s) (hs : s<1)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R u : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (εsource : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀j,‖σ j‖≤R) → (∀j,‖α j‖≤1/4) → (∀j,‖α j‖≤R/Real.log T) →
      (∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      ∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
      IntegrableOn (fun v => a03ActualPassiveRatioSourceLinearZeroFinite select dual Φ c T a b s u εsource v σ α f g)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualPassiveRatioSourceValueMoment select true dual Φ c T a b s u εsource θ σ α f g-
          a03ActualPassiveRatioSourceLinearZeroMoment select dual Φ c T a b s u εsource θ σ α f g‖≤
        C*(Real.log T)^8*T^(2*s+ε)*a03ActualPassiveUnsortedZeroModeGlobalMass T a b s u θ f g := by
  obtain ⟨C,hC,hblock⟩ := a03_actual_passive_ratio_source_zero_block_replacement_uniform_bound
    (u:=u) hs0 hs f g hf hg hΦ hΦs hc hc1 hε hκ hθ hR εsource
  refine ⟨C,hC,?_⟩
  filter_upwards [hblock,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    (a03_actual_passive_ratio_source_finite_values_integrableOn false hΦ hΦs hc hc1
      (e:=12*c+1) (by linarith) hκ hθ hR hs a b u εsource f g),
    (a03_actual_passive_ratio_source_finite_values_integrableOn true hΦ hΦs hc hc1
      (e:=12*c+1) (by linarith) hκ hθ hR hs a b u εsource f g)]
    with T hblock hT hlog hΓfalse hΓtrue
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
  exact hn'


theorem a03_sharp_passive_source_global_mass_uniform_power
    {a b s u θ η ε : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (hs0 : 0≤s) (hs : s≤1/8) (hu0 : 0<u) (hu : u≤1/8) (hθ : 0≤θ)
    (hη : 0<η) (hηε : η≤ε) (hsη : s≤η/128) (huη : u≤η/128)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ D : ℝ,0≤D ∧ ∀ᶠ T : ℝ in atTop,
      T^(η/8)*a03ActualPassiveSoftSourceGlobalMajorant T a b s u (η/1024) θ f g≤
        D*(T^(rectangularFirstExponent a b ε)+T^(rectangularSecondExponent a b ε)) := by
  obtain ⟨C,hC,hbound⟩ := a03_actual_passive_soft_source_global_majorant_bound
    ha hab hlen hs0 hs hu0 hu (by positivity : 0≤η/1024) hθ f g hf hg
  let L : ℝ := ((8:ℕ).factorial:ℝ)/(η/8)^8*Real.exp (η/8)
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨C*L,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with T hb hT
  have ht : 0<T := zero_lt_one.trans_le hT
  have hl : (1+Real.log T)^8≤L*T^(η/8) := logarithmic_power_le_rpow (by positivity) hT 8
  have hfirst : 1/2+a+b+s/2+4*(η/1024)+η/4≤rectangularFirstExponent a b ε := by
    unfold rectangularFirstExponent
    linarith only [hsη,hηε,hη]
  have hsecond : 3/4+3*a/8+5*b/8+3*s/4+u/4+4*(η/1024)+η/4≤rectangularSecondExponent a b ε := by
    unfold rectangularSecondExponent
    linarith only [hsη,huη,hηε,hη]
  calc
    _≤T^(η/8)*(C*(1+Real.log T)^8*
      (T^(1/2+a+b+s/2+4*(η/1024))+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*(η/1024)))) :=
        mul_le_mul_of_nonneg_left hb.2 (Real.rpow_nonneg ht.le _)
    _≤T^(η/8)*(C*(L*T^(η/8))*
      (T^(1/2+a+b+s/2+4*(η/1024))+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*(η/1024)))) := by gcongr
    _=(C*L)*(T^(1/2+a+b+s/2+4*(η/1024)+η/4)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*(η/1024)+η/4)) := by
      rw [show T^(η/8)*(C*(L*T^(η/8))*(T^(1/2+a+b+s/2+4*(η/1024))+
        T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*(η/1024))))=
        (C*L)*((T^(η/8)*T^(η/8))*T^(1/2+a+b+s/2+4*(η/1024))+
          (T^(η/8)*T^(η/8))*T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*(η/1024))) by ring]
      rw [←Real.rpow_add ht,←Real.rpow_add ht,←Real.rpow_add ht]
      congr 2 <;> congr 1 <;> ring
    _≤_ := mul_le_mul_of_nonneg_left (add_le_add
      (Real.rpow_le_rpow_of_exponent_le hT hfirst)
      (Real.rpow_le_rpow_of_exponent_le hT hsecond)) (mul_nonneg hC hL)

theorem a03_sharp_passive_Gamma_global_mass_uniform_power
    {a b s u θ η ε : ℝ} (ha : 0≤a) (hb : 0≤b) (hs : 0≤s) (hu : 0<u) (hθ : 0≤θ)
    (hη : 0<η) (hηε : η≤ε) (hsη : s≤η/128) (huη : u≤η/128)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ D : ℝ,0≤D ∧ ∀ᶠ T : ℝ in atTop,
      (Real.log T)^8*T^(2*s+η/16)*a03ActualPassiveUnsortedZeroModeGlobalMass T a b s u θ f g≤
        D*T^(rectangularFirstExponent a b ε) := by
  obtain ⟨C,hC,hbound⟩ := a03_actual_passive_unsorted_zero_mode_global_mass_uniform_bound
    ha hb hs hu hθ f g hf hg
  let L : ℝ := ((20:ℕ).factorial:ℝ)/(η/8)^20*Real.exp (η/8)
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨C*L,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with T hmt hT
  have ht : 0<T := zero_lt_one.trans_le hT
  have hl : (1+Real.log T)^20≤L*T^(η/8) := logarithmic_power_le_rpow (by positivity) hT 20
  have hl8 : (Real.log T)^8≤(1+Real.log T)^8 :=
    pow_le_pow_left₀ (Real.log_nonneg hT) (by linarith) 8
  have he : (a+b)/2+3*s+u/2+η/16+η/8≤rectangularFirstExponent a b ε := by
    unfold rectangularFirstExponent
    linarith only [ha,hb,hsη,huη,hηε,hη]
  calc
    _≤(Real.log T)^8*T^(2*s+η/16)*(C*(1+Real.log T)^12*T^((a+b)/2+s+u/2)) :=
      mul_le_mul_of_nonneg_left hmt.2 (by positivity)
    _≤(1+Real.log T)^8*T^(2*s+η/16)*(C*(1+Real.log T)^12*T^((a+b)/2+s+u/2)) := by gcongr
    _=C*(1+Real.log T)^20*T^((a+b)/2+3*s+u/2+η/16) := by
      have hp : T^(2*s+η/16)*T^((a+b)/2+s+u/2)=T^((a+b)/2+3*s+u/2+η/16) := by
        rw [←Real.rpow_add ht]
        congr 1
        ring
      rw [show (1+Real.log T)^8*T^(2*s+η/16)*(C*(1+Real.log T)^12*T^((a+b)/2+s+u/2))=
        C*((1+Real.log T)^8*(1+Real.log T)^12)*(T^(2*s+η/16)*T^((a+b)/2+s+u/2)) by ring,
        ←pow_add,hp]
    _≤C*(L*T^(η/8))*T^((a+b)/2+3*s+u/2+η/16) := by gcongr
    _=(C*L)*T^((a+b)/2+3*s+u/2+η/16+η/8) := by
      rw [show C*(L*T^(η/8))*T^((a+b)/2+3*s+u/2+η/16)=
        (C*L)*(T^(η/8)*T^((a+b)/2+3*s+u/2+η/16)) by ring,←Real.rpow_add ht]
      congr 1
      congr 1
      ring
    _≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT he) (mul_nonneg hC hL)

end
end SixthMoment
