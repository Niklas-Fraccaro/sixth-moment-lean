import Sechstmoment.Numerator.U.ZeroModes.Ratio.BadSourceFiniteBudget
import Sechstmoment.Numerator.U.ZeroModes.Ratio.BadSourceGeometry

/-! Broad bounds for the literal ratio source complement, including the
actual finite coefficient grids and the full logarithmic Mellin interval. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_ratio_bad_source_finite_uniform_rapid_of_ratio_lower
    {a b s u εsource c κ θ R γ A : ℝ} (ha : 0≤a) (hb : 0≤b) (hs : 0≤s) (hu : 0<u)
    {f g Φ : ℝ→ℝ} (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hγ : 0<γ) (hA : 0<A)
    (hgeo : ∀ᶠ T : ℝ in atTop,∀ i : (Fin 3→ℕ)×(Fin 4→ℕ),
      phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
        (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2 →
      ¬a03ActualRatioSourceGoodBlock T s εsource f g i →
      ∀ n : Fin 4→ℕ,rectangularAFESmoothWeight i.2 n≠0 →
        A*T^γ≤(n 0+1:ℝ)/(n 1+1) ∨ A*T^γ≤(n 2+1:ℝ)/(n 3+1)) (M : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j,‖α j‖≤1/4) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ dual : Bool,
      ‖a03ActualRatioBadSourceTimeFinite dual c T a b s u εsource v σ α f g Φ‖≤C*T^(-M) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (M+a+b+7+u)
  obtain ⟨Cr,hCr,hratio⟩ := a03_actual_ratio_pair_weight_uniform_rapid hκ hγ hA N
  obtain ⟨Cp,hCp,hkernel⟩ := a03_actual_amplified_time_kernel_uniform_polynomial hf hg hΦ hc hc1 hκ hθ hR
  obtain ⟨D,hD,hcard⟩ := a03_actual_source_block_grid_uniform_log_card ha hb
    (by positivity : 0≤(a+b)/2+s+u/2) hu
  let L := (Nat.factorial 7:ℝ)*Real.exp 1
  let C := 32*D*L*Cr*Cp
  refine ⟨C,by dsimp [C,L]; positivity,?_⟩
  filter_upwards [hratio,hkernel,hcard,hgeo,eventually_ge_atTop (1:ℝ)] with T hr hk hcard hg0 hT
  intro σ α hσ hα hroot v hv dual
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hL : 0≤L := by dsimp [L]; positivity
  have hlog : (1+Real.log T)^7≤L*T := by
    simpa only [Real.rpow_one,one_pow,div_one] using logarithmic_power_le_rpow (by norm_num : (0:ℝ)<1) hT 7
  have hbox := a03ActualRatioBadSourceTimeFinite_norm_le_card (a:=a) (b:=b) (u:=u) hTp.le
    (mul_nonneg hCr (Real.rpow_nonneg hTp.le _)) (mul_nonneg hCp (Real.rpow_nonneg hTp.le _))
    σ α f g Φ dual (B:=Cr*T^(-(N:ℝ))) (L:=Cp*T^(4:ℝ)) (by
      intro i _hi hactive hbad n hn
      have hlarge := hg0 i hactive hbad n hn
      simpa only [a03ZeroModeRatioFourWeight,Bool.false_eq_true,ite_false] using
        hr σ hroot ((n 0+1:ℝ)/(n 1+1)) ((n 2+1:ℝ)/(n 3+1)) (by positivity) (by positivity) hlarge)
    (fun _positive u w n => hk σ α hσ hα hroot v hv dual u w n)
  let grid := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  have hcbd : 2*(grid.card:ℝ)≤2*(D*(L*T)) :=
    mul_le_mul_of_nonneg_left (hcard.trans (mul_le_mul_of_nonneg_left hlog hD)) (by norm_num)
  have hβ : 0≤(Cr*T^(-(N:ℝ)))*(Cp*T^(4:ℝ)) := by positivity
  have h1 := mul_le_mul_of_nonneg_right hcbd hβ
  have h2 := mul_le_mul h1 (Nat.floor_le (Real.rpow_nonneg hTp.le a))
    (Nat.cast_nonneg ⌊T^a⌋₊) (mul_nonneg (by positivity : 0≤2*(D*(L*T))) hβ)
  have h3 := mul_le_mul h2 (Nat.floor_le (Real.rpow_nonneg hTp.le b))
    (Nat.cast_nonneg ⌊T^b⌋₊) (by positivity : 0≤2*(D*(L*T))*((Cr*T^(-(N:ℝ)))*(Cp*T^(4:ℝ)))*T^a)
  have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : 0≤16*T^(2+u))
  have hpow : T*(T^(-(N:ℝ))*T^(4:ℝ))*T^a*T^b*T^(2+u)=T^(a+b+7+u-(N:ℝ)) := by
    calc
      _=T^(1:ℝ)*(T^(-(N:ℝ))*T^(4:ℝ))*T^a*T^b*T^(2+u) := by rw [Real.rpow_one]
      _=_ := by
        rw [←Real.rpow_add hTp,←Real.rpow_add hTp,←Real.rpow_add hTp,←Real.rpow_add hTp,←Real.rpow_add hTp]
        congr 1
        ring
  calc
    _≤2*(D*(L*T))*((Cr*T^(-(N:ℝ)))*(Cp*T^(4:ℝ)))*T^a*T^b*(16*T^(2+u)) := hbox.trans h4
    _=C*(T*(T^(-(N:ℝ))*T^(4:ℝ))*T^a*T^b*T^(2+u)) := by dsimp [C]; ring
    _=C*T^(a+b+7+u-(N:ℝ)) := by rw [hpow]
    _≤C*T^(-M) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT (by linarith))
      (by dsimp [C]; positivity)

theorem a03ActualRatioBadSourceTimeFinite_Mellin_continuous
    {c T : ℝ} (hc : 0<c) (hT : T≠0) (dual : Bool)
    (a b s u εsource : ℝ) (σ α : MomentShifts) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (hα : ∀ j,‖α j‖≤1/4) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) :
    Continuous (fun v : ℝ => a03ActualRatioBadSourceTimeFinite dual c T a b s u εsource v σ α f g Φ) := by
  unfold a03ActualRatioBadSourceTimeFinite
  apply continuous_finsetSum
  intro positive _
  apply continuous_finsetSum
  intro i _
  unfold a03ActualRatioBadSourceTimeBlock
  split_ifs
  · exact continuous_const
  · exact a03ActualRatioTimeBlock_Mellin_continuous hc hT false false dual positive _
      a b s σ α f g Φ hΦ hα hσ i.1 i.2

theorem a03_actual_ratio_bad_source_moment_uniform_rapid_of_ratio_lower
    {a b s u εsource c κ θ R γ A : ℝ} (ha : 0≤a) (hb : 0≤b) (hs : 0≤s) (hu : 0<u)
    {f g Φ : ℝ→ℝ} (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hγ : 0<γ) (hA : 0<A)
    (hgeo : ∀ᶠ T : ℝ in atTop,∀ i : (Fin 3→ℕ)×(Fin 4→ℕ),
      phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
        (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2 →
      ¬a03ActualRatioSourceGoodBlock T s εsource f g i →
      ∀ n : Fin 4→ℕ,rectangularAFESmoothWeight i.2 n≠0 →
        A*T^γ≤(n 0+1:ℝ)/(n 1+1) ∨ A*T^γ≤(n 2+1:ℝ)/(n 3+1)) (M : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j,‖α j‖≤1/4) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      IntegrableOn (fun v => a03ActualRatioBadSourceTimeFinite dual c T a b s u εsource v σ α f g Φ)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualRatioBadSourceTimeMoment dual c T a b s u εsource θ σ α f g Φ‖≤C*T^(-M) := by
  obtain ⟨C,hC,hbound⟩ := a03_actual_ratio_bad_source_finite_uniform_rapid_of_ratio_lower
    ha hb hs hu hf hg hΦ hc hc1 hκ hθ hR hγ hA hgeo (M+1)
  refine ⟨2*θ*C,by positivity,?_⟩
  filter_upwards [hbound,rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    eventually_ge_atTop (1:ℝ)] with T hb hraw hT
  intro σ α hσ hα hroot dual
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hcont := a03ActualRatioBadSourceTimeFinite_Mellin_continuous hc hTp.ne' dual
    a b s u εsource σ α f g Φ hΦ hα (hraw σ hσ)
  refine ⟨hcont.continuousOn.integrableOn_Icc,?_⟩
  have hint := norm_setIntegral_le_of_norm_le_const (measure_Icc_lt_top : volume (Icc (-θ*Real.log T) (θ*Real.log T))<⊤)
    (fun v hv => hb σ α hσ hα hroot v (abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv)) dual)
  rw [Real.volume_real_Icc,max_eq_left (by nlinarith [Real.log_nonneg hT])] at hint
  unfold a03ActualRatioBadSourceTimeMoment
  calc
    _≤C*T^(-(M+1))*(θ*Real.log T-(-θ*Real.log T)) := hint
    _≤C*T^(-(M+1))*(2*θ*T) := mul_le_mul_of_nonneg_left
      (by nlinarith [Real.log_le_self hTp.le]) (by positivity)
    _=(2*θ*C)*T^(-M) := by
      have hp : T^(-(M+1))*T=T^(-M) := by
        calc
          _=T^(-(M+1))*T^(1:ℝ) := by rw [Real.rpow_one]
          _=T^(-(M+1)+1) := (Real.rpow_add hTp _ _).symm
          _=T^(-M) := by congr 1; ring
      rw [show C*T^(-(M+1))*(2*θ*T)=(2*θ*C)*(T^(-(M+1))*T) by ring,hp]

/-- The genuine discarded unit and soft-order blocks have an arbitrary
power saving after the actual time integral, scale sums and Mellin contour.
Every ratio threshold is proved from the actual supported near witness. -/
theorem a03_actual_ratio_bad_source_moment_uniform_rapid
    {a b s u εsource c κ θ R : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (hs0 : 0≤s) (hs : s≤1/2) (hu : 0<u) (hεsource : 0<εsource)
    {f g Φ : ℝ→ℝ} (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (M : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j,‖α j‖≤1/4) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      IntegrableOn (fun v => a03ActualRatioBadSourceTimeFinite dual c T a b s u εsource v σ α f g Φ)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualRatioBadSourceTimeMoment dual c T a b s u εsource θ σ α f g Φ‖≤C*T^(-M) := by
  obtain ⟨γ,A,hγ,hA,hgeo⟩ := a03_actual_ratio_bad_source_geometric_power ha hab hlen hs0 hs hεsource f g hf hg
  exact a03_actual_ratio_bad_source_moment_uniform_rapid_of_ratio_lower
    ha (ha.trans hab) hs0 hu hf hg hΦ hc hc1 hκ hθ hR hγ hA hgeo M

end
end Sechstmoment
