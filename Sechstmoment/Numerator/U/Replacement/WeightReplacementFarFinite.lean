import Sechstmoment.Numerator.U.Replacement.TimeGammaErrorFourier
import Sechstmoment.Numerator.U.Separation.TimeFarFiniteBudget

namespace Sechstmoment
open Complex Source Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03ActualWeightReplacementNearSelection (T ρ : ℝ) (u w : ℕ)
    (n : Fin 4→ℕ) : Prop :=
  |((u+1)*(n 0+1)*(n 1+1):ℕ)-( ((w+1)*(n 2+1)*(n 3+1):ℕ):ℝ)| ≤
    T^(ρ-1)*Real.sqrt ((u+1:ℝ)*(w+1)*(n 0+1)*(n 1+1)*(n 2+1)*(n 3+1))

theorem a03_actual_weight_replacement_all_far_kernel_uniform_rapid
    {Φ : ℝ→ℝ} (hΦ : SmoothDyadicWeight Φ)
    {c κ θ ρ : ℝ} (hc : 0<c) (hc1 : c≤1) (hκ : 0<κ)
    (hθ : 0≤θ) (hρ : 0<ρ) (hρ1 : ρ≤1) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ f g : ℝ→ℝ, ∀ positive : Bool,
      ∀ u w : ℕ, ∀ n : Fin 4→ℕ,
      a03ActualFarSelection T ρ positive u w n →
      ‖∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
        rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤
        ‖a03ActualMellinStaticFactor T f g α u w n ((c:ℂ)+(v:ℂ)*I)‖*C*T^(-M) := by
  let e : ℝ := 2*c+1
  obtain ⟨N,hN⟩ := exists_nat_gt ((M+e)/ρ)
  have hexp : e-ρ*(N:ℝ)≤-M := by
    have h := (div_lt_iff₀ hρ).mp hN
    nlinarith
  obtain ⟨C,hC,hCd⟩ := rectangular_weight_replacement_actual_time_uniform_schwartz_bound
    hΦ hc hc1 (show 2*c<e by dsimp [e]; linarith) hκ hθ
  refine ⟨C N*8^N,mul_nonneg (hC N) (by positivity),?_⟩
  filter_upwards [hCd,eventually_ge_atTop (1:ℝ)] with T hbT hT
  intro σ α hα hroot v hv f g positive u w n hs
  have hTp : 0<T := zero_lt_one.trans_le hT
  let ℓ : ℝ := Real.log (phaseActualProductRatio (u+1) (w+1) n)
  have hη : 0≤T^(ρ-1) := Real.rpow_nonneg hTp.le _
  have hη1 : T^(ρ-1)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by linarith)
  have hlog : T^(ρ-1)/8≤|ℓ| :=
    phase_actual_selected_far_log_lower positive (by omega) (by omega) n hs.1 hη hη1 (by simpa only [Nat.cast_add,Nat.cast_one] using hs.2)
  have hfreq : T^ρ/8≤|-T*ℓ| := by
    have hm := mul_le_mul_of_nonneg_left hlog hTp.le
    have he : T*T^(ρ-1)=T^ρ := by
      calc
        _=T^(1:ℝ)*T^(ρ-1) := by rw [Real.rpow_one]
        _=T^ρ := by rw [← Real.rpow_add hTp]; congr 1; ring
    rw [abs_mul,abs_neg,abs_of_pos hTp]
    nlinarith
  have hbase : 0<T^ρ/8 := by positivity
  have hpow : 0<(T^ρ/8)^N := pow_pos hbase N
  let D := ‖a03ActualMellinStaticFactor T f g α u w n ((c:ℂ)+(v:ℂ)*I)‖
  let E := ‖∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
    rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖
  have hD : 0≤D := norm_nonneg _
  have hE : 0≤E := norm_nonneg _
  have hF : (1+|-T*ℓ|)^N*E≤D*C N*T^e := hbT σ α hα hroot v hv f g u w n N
  have hFp : (T^ρ/8)^N*E≤D*C N*T^e :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbase.le (by linarith [hfreq,abs_nonneg (-T*ℓ)]) N) hE).trans hF
  have hnorm : E≤(D*C N*T^e)/(T^ρ/8)^N := (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hFp)
  change E≤D*(C N*8^N)*T^(-M)
  calc
    _≤(D*C N*T^e)/(T^ρ/8)^N := hnorm
    _=(D*(C N*8^N))*T^(e-ρ*(N:ℝ)) := by
      rw [div_pow,← Real.rpow_natCast,← Real.rpow_mul hTp.le,Real.rpow_sub hTp]
      field_simp
    _≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT hexp)
      (mul_nonneg hD (mul_nonneg (hC N) (by positivity)))

def a03ActualWeightReplacementFarSelection (T ρ : ℝ) (positive : Bool)
    (u w : ℕ) (n : Fin 4→ℕ) : Prop :=
  ¬a03ActualWeightReplacementNearSelection T ρ u w n ∧
    a03ActualFarSelection T ρ positive u w n

def a03ActualWeightReplacementFarFiniteMellinGrid (positive : Bool)
    (c T a b η ρ v : ℝ) (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
      if a03ActualWeightReplacementFarSelection T ρ positive u w n then
        (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
          rectangularMomentPairWeight T f g Φ u w t*
          rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I))
      else 0

theorem a03_actual_weight_replacement_far_finite_grid_uniform_rapid
    {a b c η κ θ ρ : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (hη : 0<η)
    (hκ : 0<κ) (hθ : 0≤θ) (hρ : 0<ρ) (hρ1 : ρ≤1) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
      ‖a03ActualWeightReplacementFarFiniteMellinGrid positive c T a b η ρ v f g Φ σ α‖≤C*T^(-M) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  let Q : ℝ := M+a+b+3+η
  obtain ⟨C,hC,hb⟩ := a03_actual_weight_replacement_all_far_kernel_uniform_rapid hΦ hc hc1 hκ hθ hρ hρ1 Q
  obtain ⟨D,hD,hcard⟩ := rectangular_small_contour_grid_uniform_polynomial_card hη
  let L : ℝ := F*G*C
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨L*D,mul_nonneg hL hD,?_⟩
  filter_upwards [hb,hcard,eventually_ge_atTop (1:ℝ)] with T hb hcard hT
  intro σ α hα hroot v hv positive
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hkernel (u w : ℕ) (n : Fin 4→ℕ) (hs : a03ActualFarSelection T ρ positive u w n) :
      ‖∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
        rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤L*T^(-Q) := by
    have hstatic := a03ActualMellinStaticFactor_norm_le hF hG hc.le T f g hfb hgb α hα u w n v
    exact (hb σ α hα hroot v hv f g positive u w n hs).trans (by
      dsimp [L]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstatic hC) (by positivity))
  let q := fun (u w : ℕ) (k n : Fin 4→ℕ) =>
    if a03ActualWeightReplacementFarSelection T ρ positive u w n then
      (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
        rectangularMomentPairWeight T f g Φ u w t*
        rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0
  have hq (u w : ℕ) (k n : Fin 4→ℕ) : ‖q u w k n‖≤L*T^(-Q) := by
    dsimp only [q]
    by_cases hs : a03ActualWeightReplacementFarSelection T ρ positive u w n
    · rw [ite_eq_left hs,norm_mul,Complex.norm_real,Real.norm_of_nonneg (rectangular_AFE_smooth_weight_nonneg k n)]
      calc
        _≤rectangularAFESmoothWeight k n*(L*T^(-Q)) := mul_le_mul_of_nonneg_left
          (hkernel u w n hs.2) (rectangular_AFE_smooth_weight_nonneg k n)
        _≤L*T^(-Q) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (rectangular_small_contour_smooth_weight_le_one k n) (by positivity : 0≤L*T^(-Q))
    · rw [ite_eq_right hs,norm_zero]
      positivity
  change ‖∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
      q u w k n‖≤(L*D)*T^(-M)
  calc
    _≤(L*T^(-Q))*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*
        (∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ((rectangularAFESmoothBox k).card:ℝ)) :=
      a03_finite_amplifier_grid_norm_le_card T a b η q (by positivity) hq
    _≤(L*T^(-Q))*T^a*T^b*(D*T^(3+η)) := by
      have hna : (⌊T^a⌋₊:ℝ)≤T^a := Nat.floor_le (Real.rpow_nonneg hTp.le _)
      have hnb : (⌊T^b⌋₊:ℝ)≤T^b := Nat.floor_le (Real.rpow_nonneg hTp.le _)
      have hp : 0≤L*T^(-Q) := mul_nonneg hL (Real.rpow_nonneg hTp.le _)
      have hpa : (L*T^(-Q))*(⌊T^a⌋₊:ℝ)≤(L*T^(-Q))*T^a := mul_le_mul_of_nonneg_left hna hp
      have hpab := mul_le_mul hpa hnb (Nat.cast_nonneg ⌊T^b⌋₊) (mul_nonneg hp (Real.rpow_nonneg hTp.le a))
      exact mul_le_mul hpab hcard (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg hp (Real.rpow_nonneg hTp.le a)) (Real.rpow_nonneg hTp.le b))
    _=(L*D)*T^((-Q+a+b)+(3+η)) := by
      rw [Real.rpow_add hTp (-Q+a+b) (3+η),Real.rpow_add hTp (-Q+a) b,Real.rpow_add hTp (-Q) a]
      ring
    _=_ := by congr 2; dsimp [Q]; ring

end
end Sechstmoment
