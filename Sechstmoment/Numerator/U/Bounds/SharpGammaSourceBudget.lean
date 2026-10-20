import Sechstmoment.Numerator.U.ZeroModes.Ratio.SevenGridSpectralTail

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_ratio_native_sub_Gamma_mass_budget_smaller (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource e c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+e<rectangularSlack a b)
    (Smax Umax : ℝ) (hSm : 0<Smax) (hUm : 0<Umax) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ S≤Smax ∧ 0<U ∧ U≤1/8 ∧ U≤Umax ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U → ∃ D : ℝ,0≤D ∧
      ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ‖a03ActualRatioSourceValueMoment false dual Φ c T a b s u εsource θ σ α f g-
          a03ActualRatioSourceValueMoment true dual Φ c T a b s u εsource θ σ α f g‖≤
            D*T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g := by
  obtain ⟨S0,U0,C,hS0,hS02,hScap,hU0,hUcap,_hLoss1,_hLoss2,hC,hphysical⟩ :=
    a03_actual_ratio_tensor_soft_source_physical_bound dual hinput ha hab hlen hεsource
      f g hf hg hΦ hΦs hc hc1 he hκ hθ hR hloss
  let S := min S0 Smax
  let U := min U0 Umax
  have hSS : S≤S0 := min_le_left _ _
  have hUU : U≤U0 := min_le_left _ _
  refine ⟨S,U,lt_min hS0 hSm,hSS.trans_lt hS02,hSS.trans hScap,min_le_right _ _,
    lt_min hU0 hUm,hUU.trans hUcap,min_le_right _ _,?_⟩
  intro s u hs hsS hu huU
  have hss : s≤S0 := hsS.trans hSS
  have huu : u≤U0 := huU.trans hUU
  have hs2 : s<1/2 := hss.trans_lt hS02
  let D := C*a03SourceMellinBound R u
  have hD : 0≤D := by dsimp [D,a03SourceMellinBound]; positivity
  refine ⟨D,hD,?_⟩
  filter_upwards [hphysical,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R)),
    a03_actual_ratio_source_finite_values_integrableOn dual hΦ hΦs hc hc1 he hκ hθ hR
      (hs2.trans (by norm_num)) a b u εsource f g] with T hphysical hT hlog hlogR hi
  intro σ α hσ hα hroot
  have hL : 0<Real.log T := zero_lt_one.trans_le hlog
  have hαsmall : ∀ j,‖α j‖≤1/4 := fun j =>
    (hα j).trans ((div_le_iff₀ hL).mpr (by linarith))
  have hip := hi σ α hσ hαsmall hroot false
  have hiz := hi σ α hσ hαsmall hroot true
  rw [←a03ActualRatioSourceErrorMoment_eq_physical_sub_zero (zero_lt_one.trans_le hT)
    dual Φ c e a b s u εsource θ σ α f g hip hiz]
  apply a03_actual_ratio_source_error_moment_bound hT hθ dual Φ c σ α f g
  intro v hv positive i hi
  have hk := (Finset.mem_product.mp hi).2
  apply a03_actual_ratio_source_restored_block_bound (zero_lt_one.trans_le hT) hlog hR hc.le hc1 hC
    dual positive Φ σ α hα v f g i hk
  intro hgood
  rcases hgood with ⟨hactive,hmsoft,hnsoft,hk1,hk3⟩
  obtain ⟨hk0,hactive0⟩ := a03_actual_source_restricted_domain hT hss huu f g i.2 hk hactive
  exact hphysical _ _ _ (boundaryActual_scale_ge_two_thirds (i.1 0))
    (boundaryActual_scale_ge_two_thirds (i.1 1)) (boundaryActual_scale_ge_two_thirds (i.1 2))
    i.2 hk0 hactive0 hmsoft hnsoft hk1 hk3 σ α hσ hαsmall hroot v hv positive _ _

theorem a03_actual_ratio_Gamma_zero_sub_linear_uniform_mass_budget
    {a b s : ℝ} (_ha : 0≤a) (_hb : 0≤b) (hs0 : 0≤s) (hs : s<1)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R u : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (_hu : 0<u) (εsource : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀j,‖σ j‖≤R) → (∀j,‖α j‖≤1/4) → (∀j,‖α j‖≤R/Real.log T) →
      (∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      ‖a03ActualRatioSourceValueMoment true dual Φ c T a b s u εsource θ σ α f g-
        a03ActualRatioSourceLinearZeroMoment dual Φ c T a b s u εsource θ σ α f g‖≤
          C*(Real.log T)^8*T^(2*s+ε)*a03ActualUnsortedZeroModeGlobalMass T a b s u θ f g := by
  obtain ⟨C,hC,hblock⟩ := a03_actual_ratio_source_zero_block_replacement_uniform_bound
    (u:=u) hs0 hs f g hf hg hΦ hΦs hc hc1 hε hκ hθ hR εsource
  refine ⟨C,hC,?_⟩
  filter_upwards [hblock,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    (a03_actual_ratio_source_finite_values_integrableOn false hΦ hΦs hc hc1
      (e:=12*c+1) (by linarith) hκ hθ hR hs a b u εsource f g),
    (a03_actual_ratio_source_finite_values_integrableOn true hΦ hΦs hc hc1
      (e:=12*c+1) (by linarith) hκ hθ hR hs a b u εsource f g)]
    with T hblock hT hlog hΓfalse hΓtrue
  intro σ α hσ hα hαnorm hroot dual
  have hi := a03ActualRatioSourceLinearZeroFinite_integrableOn hΦ.continuous hΦs hT hlog hc hκ σ α hroot hα
    dual a b s u εsource θ f g
  have hΓ' : IntegrableOn (fun v => a03ActualRatioSourceFiniteValue true dual Φ c T a b s u εsource v σ α f g)
      (Icc (-θ*Real.log T) (θ*Real.log T)) := by
    cases dual
    · exact hΓfalse σ α hσ hα hroot true
    · exact hΓtrue σ α hσ hα hroot true
  unfold a03ActualRatioSourceValueMoment a03ActualRatioSourceLinearZeroMoment
  rw [←integral_sub hΓ' hi]
  let grid := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  have hfinite (v : ℝ) (hv : |v|≤θ*Real.log T) :
      ‖a03ActualRatioSourceFiniteValue true dual Φ c T a b s u εsource v σ α f g-
        a03ActualRatioSourceLinearZeroFinite dual Φ c T a b s u εsource v σ α f g‖≤
      2*(C*(Real.log T)^8*T^(2*s+ε)*a03ActualUnsortedZeroModeFiniteMass T a b s u f g) := by
    unfold a03ActualRatioSourceFiniteValue a03ActualRatioSourceLinearZeroFinite
    rw [←Finset.sum_sub_distrib]
    calc
      _≤∑positive : Bool,‖∑i∈grid,
        (a03ActualRatioSourceBlockValue true dual positive Φ c T s εsource v σ α f g i-
          a03ActualRatioSourceLinearZeroBlock dual positive Φ c T s εsource v σ α f g i)‖ := by
        simpa only [Finset.sum_sub_distrib,grid] using norm_sum_le Finset.univ (fun positive : Bool =>
          (∑i∈grid,a03ActualRatioSourceBlockValue true dual positive Φ c T s εsource v σ α f g i)-
            (∑i∈grid,a03ActualRatioSourceLinearZeroBlock dual positive Φ c T s εsource v σ α f g i))
      _≤∑_positive : Bool,C*(Real.log T)^8*T^(2*s+ε)*a03ActualUnsortedZeroModeFiniteMass T a b s u f g := by
        apply Finset.sum_le_sum
        intro positive _hp
        calc
          _≤∑i∈grid,‖a03ActualRatioSourceBlockValue true dual positive Φ c T s εsource v σ α f g i-
            a03ActualRatioSourceLinearZeroBlock dual positive Φ c T s εsource v σ α f g i‖ := norm_sum_le _ _
          _≤∑i∈grid,C*(Real.log T)^8*T^(2*s+ε)*a03ActualUnsortedZeroModeBlockMass T s f g i :=
            Finset.sum_le_sum (hblock σ α hσ hα hαnorm hroot v hv dual positive)
          _=_ := by simp only [a03ActualUnsortedZeroModeFiniteMass,grid,Finset.mul_sum]
      _=_ := by simp [two_mul]
  have hn := norm_setIntegral_le_of_norm_le_const_ae'
    (measure_Icc_lt_top : volume (Icc (-θ*Real.log T) (θ*Real.log T))<⊤)
    (ae_of_all volume fun v hv => hfinite v (abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv)))
  apply hn.trans_eq
  rw [Real.volume_real_Icc,max_eq_left (by nlinarith [Real.log_nonneg hT.le])]
  unfold a03ActualUnsortedZeroModeGlobalMass
  ring

theorem a03_actual_soft_source_restored_sharp_power
    {a b s u εsource e θ δ P Q : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s≤1/8)
    (hu : 0<u) (hu1 : u≤1/8) (hεsource : 0≤εsource) (hθ : 0≤θ) (hδ : 0<δ)
    (hP : 1/2+a+b+s/2+4*εsource+e+δ≤P)
    (hQ : 3/4+3*a/8+5*b/8+3*s/4+u/4+4*εsource+e+δ≤Q)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,
      T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g≤C*(T^P+T^Q) := by
  obtain ⟨C,hC,hbound⟩ := a03_actual_soft_source_global_majorant_bound
    ha hab hlen hs0 hs hu hu1 hεsource hθ f g hf hg
  let L : ℝ := (Nat.factorial 8:ℝ)/δ^8*Real.exp δ
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨C*L,mul_nonneg hC hL,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with T hb hT
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hlog : (1+Real.log T)^8≤L*T^δ := logarithmic_power_le_rpow hδ hT 8
  have he1 : T^e*T^δ*T^(1/2+a+b+s/2+4*εsource)=T^(1/2+a+b+s/2+4*εsource+e+δ) := by
    rw [←Real.rpow_add hTp,←Real.rpow_add hTp]
    congr 1
    ring
  have he2 : T^e*T^δ*T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*εsource)=
      T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*εsource+e+δ) := by
    rw [←Real.rpow_add hTp,←Real.rpow_add hTp]
    congr 1
    ring
  calc
    _≤T^e*(C*(1+Real.log T)^8*(T^(1/2+a+b+s/2+4*εsource)+
      T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*εsource))) :=
        mul_le_mul_of_nonneg_left hb.2 (Real.rpow_nonneg hTp.le e)
    _≤T^e*(C*(L*T^δ)*(T^(1/2+a+b+s/2+4*εsource)+
      T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*εsource))) := by gcongr
    _=(C*L)*(T^(1/2+a+b+s/2+4*εsource+e+δ)+
      T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*εsource+e+δ)) := by
        calc
          _=(C*L)*(T^e*T^δ*T^(1/2+a+b+s/2+4*εsource)+
            T^e*T^δ*T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*εsource)) := by ring
          _=_ := by rw [he1,he2]
    _≤_ := mul_le_mul_of_nonneg_left
      (add_le_add (Real.rpow_le_rpow_of_exponent_le hT hP) (Real.rpow_le_rpow_of_exponent_le hT hQ))
        (mul_nonneg hC hL)

theorem a03_actual_ratio_Gamma_zero_sub_linear_uniform_power
    {a b s : ℝ} (ha : 0≤a) (hb : 0≤b) (hs0 : 0≤s) (hs : s<1)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R u δ P : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hu : 0<u) (hδ : 0<δ)
    (hexp : (a+b)/2+3*s+u/2+ε+δ≤P) (εsource : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀j,‖σ j‖≤R) → (∀j,‖α j‖≤1/4) → (∀j,‖α j‖≤R/Real.log T) →
      (∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      ‖a03ActualRatioSourceValueMoment true dual Φ c T a b s u εsource θ σ α f g-
        a03ActualRatioSourceLinearZeroMoment dual Φ c T a b s u εsource θ σ α f g‖≤C*T^P := by
  obtain ⟨C,hC,hGamma⟩ := a03_actual_ratio_Gamma_zero_sub_linear_uniform_mass_budget
    ha hb hs0 hs f g hf hg hΦ hΦs hc hc1 hε hκ hθ hR hu εsource
  obtain ⟨D,hD,hMass⟩ := a03_actual_unsorted_zero_mode_global_mass_uniform_bound ha hb hs0 hu hθ f g hf hg
  let L : ℝ := (Nat.factorial 20:ℝ)/δ^20*Real.exp δ
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨C*D*L,by positivity,?_⟩
  filter_upwards [hGamma,hMass,eventually_ge_atTop (1:ℝ)] with T hΓ hm hT
  intro σ α hσ hα hαnorm hroot dual
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hlog0 := Real.log_nonneg hT
  have hpoly : (Real.log T)^8*(1+Real.log T)^12≤L*T^δ := by
    calc
      _≤(1+Real.log T)^8*(1+Real.log T)^12 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlog0 (by linarith) 8) (by positivity)
      _=(1+Real.log T)^20 := by rw [←pow_add]
      _≤_ := logarithmic_power_le_rpow hδ hT 20
  have hpow : T^(2*s+ε)*T^((a+b)/2+s+u/2)*T^δ=T^((a+b)/2+3*s+u/2+ε+δ) := by
    rw [←Real.rpow_add hTp,←Real.rpow_add hTp]
    congr 1
    ring
  calc
    _≤C*(Real.log T)^8*T^(2*s+ε)*a03ActualUnsortedZeroModeGlobalMass T a b s u θ f g :=
      hΓ σ α hσ hα hαnorm hroot dual
    _≤C*(Real.log T)^8*T^(2*s+ε)*(D*(1+Real.log T)^12*T^((a+b)/2+s+u/2)) :=
      mul_le_mul_of_nonneg_left hm.2 (by positivity)
    _=(C*D)*((Real.log T)^8*(1+Real.log T)^12)*(T^(2*s+ε)*T^((a+b)/2+s+u/2)) := by ring
    _≤(C*D)*(L*T^δ)*(T^(2*s+ε)*T^((a+b)/2+s+u/2)) := by gcongr
    _=(C*D*L)*T^((a+b)/2+3*s+u/2+ε+δ) := by
      calc
        _=(C*D*L)*(T^(2*s+ε)*T^((a+b)/2+s+u/2)*T^δ) := by ring
        _=_ := by rw [hpow]
    _≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT hexp) (by positivity)

end
end Sechstmoment
