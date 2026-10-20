import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.HighFrequencyAggregate

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000

theorem a03NativeGCD_bounded_high_frequency_mask_uniform_rapid
    {a b s κ : ℝ} (hs : 0<s) (hκ : 0<κ)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) (M : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀α : MomentShifts,(∀j : Fin 4,‖α j‖≤1/4) →∀dual : Bool,
      ∀ mask : Bool→ℕ→ℕ→((ℕ×ℕ)×ℕ)→ℝ→ℝ,
      (∀positive z v p X,0<X →|mask positive z v p X|≤1) →
      (∀positive z v p X,0<X →mask positive z v p X≠0 →
        f (Real.log (z+1:ℝ)/Real.log T)≠0 →g (Real.log (v+1:ℝ)/Real.log T)≠0 →
        T^(s-1)*X≤(Nat.gcd ((z+1)*(p.1.1+1)) ((v+1)*(p.1.2+1)):ℝ)*(p.2+1)) →
      ‖a03NativeGCDMaskedPhysicalSum mask dual Φ T a b σ α f g‖≤C*T^(-M) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  let Q : ℝ := M+2+a+b+(1+a+b)*(9/2:ℝ)
  obtain ⟨Cf,hCf,hFour⟩ := a03VStarActualBranchTimeFourier_highFrequency_uniform_rapid
    hΦ hSupp K hK hκ hs Q
  obtain ⟨Dm,hDm,hMass⟩ := a03NativeGCDAbsoluteMajorant_summable_bound hκ
  let D : ℝ := F*G*Cf*Dm
  let L : ℝ := (Nat.factorial 56:ℝ)*Real.exp 1
  refine ⟨2*D*L,by dsimp [D,L]; positivity,?_⟩
  filter_upwards [hFour,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hFour hT hlog
  intro σ hσ hroot α hα dual mask hmask hgap
  have ht : 0<T := zero_lt_one.trans hT
  have hlog0 : 0≤Real.log T := by linarith
  have hD : 0≤D := by dsimp [D]; positivity
  let A : ℝ := F*G*Cf*T^(-Q)*(Real.log T)^48
  have hA : 0≤A := by dsimp [A]; positivity
  have hpoint (positive : Bool) (z v : ℕ) (X : ℝ) (hX : 0<X) :
      ‖∑'p : (ℕ×ℕ)×ℕ,(mask positive z v p X:ℂ)*
        a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X‖≤
      (D*T^(-Q)*(Real.log T)^56/((z+1:ℝ)*(v+1:ℝ)*T^2))*
        ((X^(5/2:ℝ)+X^(7/2:ℝ))*a03NativeGCDSpatialEnvelope (T*Real.sqrt ((z+1:ℝ)*(v+1:ℝ))) X) := by
    let Y : ℝ := T*Real.sqrt ((z+1:ℝ)*(v+1:ℝ))
    let Z : ((ℕ×ℕ)×ℕ)→ℝ := a03NativeGCDAbsoluteMajorant T σ (z+1) (v+1) Y X
    have hY : 0<Y := by dsimp [Y]; positivity
    obtain ⟨hZS,hZB⟩ := hMass T hT hlog σ hroot (z+1) (v+1) (by positivity) (by positivity) Y X hX
    have hp (p : (ℕ×ℕ)×ℕ) :
        ‖(mask positive z v p X:ℂ)*a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X‖≤A*Z p := by
      by_cases hm0 : mask positive z v p X=0
      · simp only [hm0,Complex.ofReal_zero,zero_mul,norm_zero]
        exact mul_nonneg hA (a03NativeGCDAbsoluteMajorant_nonneg _ _ _ _ _ _ hX p)
      by_cases hf0 : f (Real.log (z+1:ℝ)/Real.log T)=0
      · simp [a03UnrestrictedRatioGCDVStarIntegrand,hf0]
        exact mul_nonneg hA (a03NativeGCDAbsoluteMajorant_nonneg _ _ _ _ _ _ hX p)
      by_cases hg0 : g (Real.log (v+1:ℝ)/Real.log T)=0
      · simp [a03UnrestrictedRatioGCDVStarIntegrand,hg0]
        exact mul_nonneg hA (a03NativeGCDAbsoluteMajorant_nonneg _ _ _ _ _ _ hX p)
      have hξ := a03NativeGCD_high_gap_frequency ht hX positive z v p.1.1 p.1.2 p.2
        (hgap positive z v p X hX hm0 hf0 hg0)
      have hFour' := hFour σ hσ hroot dual Y X
        (-(T*rectangularGapSign positive*(Nat.gcd ((z+1)*(p.1.1+1)) ((v+1)*(p.1.2+1)):ℝ)*(p.2+1)/X)) hY hX hξ
      have hb := a03UnrestrictedRatioGCDVStarIntegrand_norm_le_majorant ht hX
        (by positivity : 0≤Cf*T^(-Q)*(Real.log T)^48) σ α hα dual positive Φ f g z v p.1.1 p.1.2 p.2 hFour'
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply (mul_le_of_le_one_left (norm_nonneg _) (hmask positive z v p X hX)).trans
      apply hb.trans
      apply mul_le_mul_of_nonneg_right _ (a03NativeGCDAbsoluteMajorant_nonneg _ _ _ _ _ _ hX p)
      have hfg : |f (Real.log (z+1:ℝ)/Real.log T)| *|g (Real.log (v+1:ℝ)/Real.log T)|≤F*G :=
        mul_le_mul (by simpa only [Real.norm_eq_abs] using hfb _)
          (by simpa only [Real.norm_eq_abs] using hgb _) (abs_nonneg _) hF
      simpa only [A,mul_assoc] using mul_le_mul_of_nonneg_right hfg
        (by positivity : 0≤Cf*T^(-Q)*(Real.log T)^48)
    have hNS := (hZS.mul_left A).of_nonneg_of_le (fun _ => norm_nonneg _) hp
    calc
      _≤∑'p : (ℕ×ℕ)×ℕ,‖(mask positive z v p X:ℂ)*a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X‖ :=
        norm_tsum_le_tsum_norm hNS
      _≤∑'p : (ℕ×ℕ)×ℕ,A*Z p := hNS.tsum_le_tsum hp (hZS.mul_left A)
      _=A*(∑'p : (ℕ×ℕ)×ℕ,Z p) := tsum_mul_left
      _≤A*((Dm*(Real.log T)^8/((z+1:ℝ)*(v+1:ℝ)*T^2))*
        ((X^(5/2:ℝ)+X^(7/2:ℝ))*a03NativeGCDSpatialEnvelope Y X)) :=
        mul_le_mul_of_nonneg_left (by
          simpa only [Z,Nat.cast_add,Nat.cast_one] using hZB) hA
      _=_ := by dsimp [A,D,Y]; rw [show (Real.log T)^56=(Real.log T)^48*(Real.log T)^8 by rw [←pow_add]]; ring
  have hmain := a03NativeGCD_masked_physical_sum_norm_le_of_point_bound (a:=a) (b:=b) hT.le hD 56
    mask dual Φ σ α f g (fun positive z _hz v _hv X hX => hpoint positive z v X hX)
  have hlogpow : (Real.log T)^56≤L*T := by
    apply (pow_le_pow_left₀ hlog0 (by linarith : Real.log T≤1+Real.log T) 56).trans
    simpa only [Real.rpow_one,one_pow,div_one] using
      logarithmic_power_le_rpow (by norm_num : (0:ℝ)<1) hT.le 56
  have hexp : 1+a+b+(1+a+b)*(9/2:ℝ)-Q=-(M+1) := by dsimp [Q]; ring
  rw [hexp] at hmain
  calc
    _≤2*D*T^(-(M+1))*(Real.log T)^56 := hmain
    _≤2*D*T^(-(M+1))*(L*T) := mul_le_mul_of_nonneg_left hlogpow (by positivity)
    _=(2*D*L)*T^(-M) := by
      have he : T^(-(M+1))*T=T^(-M) := by
        calc
          _=T^(-(M+1))*T^(1:ℝ) := by rw [Real.rpow_one]
          _=T^(-M) := by rw [←Real.rpow_add ht]; congr 1; ring
      rw [show 2*D*T^(-(M+1))*(L*T)=(2*D*L)*(T^(-(M+1))*T) by ring,he]

end
end Sechstmoment
