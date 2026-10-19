import Sechstmoment.Numerator.U.Separation.TimeFarContourBudget
import Sechstmoment.Numerator.U.Sources.NearPartition

/-! The omitted weight of the actual active-block partition is supported
on genuine far tuples and has a proved complete finite contour budget. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualFiniteOffdiagonalMellinGrid (dual positive : Bool) (c T a b u v : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  ∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,
      if (if positive then rectangularPositiveQuadGap (p+1) (q+1) n
        else rectangularNegativeQuadGap (p+1) (q+1) n) then
        (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
          rectangularMomentPairWeight T f g Φ p q t*
          (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0

def a03ActualNearBlockFiniteMellinGrid (dual positive : Bool) (c T a b s u v : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  ∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,
      if (if positive then rectangularPositiveQuadGap (p+1) (q+1) n
        else rectangularNegativeQuadGap (p+1) (q+1) n) then
        (a03ActualSourceNearPartition T a b s u f g k (p+1) (q+1)
          (rectangularAFEGap positive (p+1) (q+1) n):ℂ)*
        (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
          rectangularMomentPairWeight T f g Φ p q t*
          (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0

def a03ActualSourceFarResidualMellinGrid (dual positive : Bool) (c T a b s u v : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  a03ActualFiniteOffdiagonalMellinGrid dual positive c T a b u v f g Φ σ α-
    a03ActualNearBlockFiniteMellinGrid dual positive c T a b s u v f g Φ σ α

theorem a03_actual_source_far_residual_eq_sum (dual positive : Bool) (c T a b s u v : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) :
    a03ActualSourceFarResidualMellinGrid dual positive c T a b s u v f g Φ σ α=
  ∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,
      if (if positive then rectangularPositiveQuadGap (p+1) (q+1) n
        else rectangularNegativeQuadGap (p+1) (q+1) n) then
        ((1-a03ActualSourceNearPartition T a b s u f g k (p+1) (q+1)
          (rectangularAFEGap positive (p+1) (q+1) n):ℝ):ℂ)*
        (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
          rectangularMomentPairWeight T f g Φ p q t*
          (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0 := by
  unfold a03ActualSourceFarResidualMellinGrid a03ActualFiniteOffdiagonalMellinGrid
    a03ActualNearBlockFiniteMellinGrid
  simp_rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> push_cast <;> ring

theorem a03_actual_source_far_residual_grid_uniform_rapid
    {a b c u κ θ R s : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (hu : 0<u)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : 0<s) (hs1 : s≤1) (M : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ dual positive : Bool,
      ‖a03ActualSourceFarResidualMellinGrid dual positive c T a b s u v f g Φ σ α‖≤C*T^(-M) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  let Q : ℝ := M+a+b+3+u
  obtain ⟨C₀,hC₀,hb₀⟩ := a03_actual_amplified_all_far_kernel_uniform_rapid
    hΦ hc hc1 (show 2*c<2*c+1 by linarith) hκ hθ (show (0:ℝ)≤1/4 by norm_num) hs hs1 Q
  obtain ⟨C₁,hC₁,hb₁⟩ := a03_actual_amplified_all_far_dual_kernel_uniform_rapid
    hΦ hc hc1 (show 2*c<2*c+1 by linarith) hκ hθ (show (0:ℝ)≤1/4 by norm_num) hR hs hs1 Q
  obtain ⟨D,hD,hcard⟩ := rectangular_small_contour_grid_uniform_polynomial_card hu
  let L : ℝ := F*G*(C₀+C₁)
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨L*D,mul_nonneg hL hD,?_⟩
  filter_upwards [hb₀,hb₁,hcard,eventually_ge_atTop (1:ℝ)] with T hb₀ hb₁ hcard hT
  intro σ α hσ hα hroot v hv dual positive
  have hTp : 0<T := zero_lt_one.trans_le hT
  let K (p q : ℕ) (n : Fin 4→ℕ) : ℂ := ∫ t : ℝ,
    rectangularMomentPairWeight T f g Φ p q t*
      (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
      rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)
  have hkernel (p q : ℕ) (n : Fin 4→ℕ) (hfar : a03ActualFarSelection T s positive p q n) :
      ‖K p q n‖≤L*T^(-Q) := by
    have hstatic := a03ActualMellinStaticFactor_norm_le hF hG hc.le T f g hfb hgb α hα p q n v
    have hb : ‖a03ActualMellinStaticFactor T f g α p q n ((c:ℂ)+(v:ℂ)*I)‖*
        (C₀+C₁)*T^(-Q)≤L*T^(-Q) := by
      dsimp [L]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstatic (by positivity)) (by positivity)
    dsimp only [K]
    cases dual
    · simp only [Bool.false_eq_true,ite_false,mul_one]
      exact (hb₀ σ α hα hroot v hv f g positive p q n hfar.1 hfar.2).trans
        ((by gcongr; linarith : ‖a03ActualMellinStaticFactor T f g α p q n ((c:ℂ)+(v:ℂ)*I)‖*C₀*T^(-Q)≤
          ‖a03ActualMellinStaticFactor T f g α p q n ((c:ℂ)+(v:ℂ)*I)‖*(C₀+C₁)*T^(-Q)).trans hb)
    · simp only [ite_true]
      exact (hb₁ σ α hσ hα hroot v hv f g positive p q n hfar.1 hfar.2).trans
        ((by gcongr; linarith : ‖a03ActualMellinStaticFactor T f g α p q n ((c:ℂ)+(v:ℂ)*I)‖*C₁*T^(-Q)≤
          ‖a03ActualMellinStaticFactor T f g α p q n ((c:ℂ)+(v:ℂ)*I)‖*(C₀+C₁)*T^(-Q)).trans hb)
  let term (p q : ℕ) (k n : Fin 4→ℕ) : ℂ :=
    if (if positive then rectangularPositiveQuadGap (p+1) (q+1) n else rectangularNegativeQuadGap (p+1) (q+1) n) then
      ((1-a03ActualSourceNearPartition T a b s u f g k (p+1) (q+1)
        (rectangularAFEGap positive (p+1) (q+1) n):ℝ):ℂ)*(rectangularAFESmoothWeight k n:ℂ)*K p q n else 0
  have hterm (p : ℕ) (hp : p∈Finset.range ⌊T^a⌋₊) (q : ℕ) (hq : q∈Finset.range ⌊T^b⌋₊)
      (k : Fin 4→ℕ) (hk : k∈rectangularAFEProductScaleGrid (T^(2+u))) (n : Fin 4→ℕ) :
      ‖term p q k n‖≤L*T^(-Q) := by
    dsimp only [term]
    by_cases hselected : if positive then rectangularPositiveQuadGap (p+1) (q+1) n else rectangularNegativeQuadGap (p+1) (q+1) n
    · rw [ite_eq_left hselected]
      by_cases hw0 : rectangularAFESmoothWeight k n=0
      · simp [hw0]; positivity
      by_cases hf0 : f (Real.log (p+1:ℝ)/Real.log T)=0
      · have hK : K p q n=0 := by simp [K,rectangularMomentPairWeight,hf0]
        rw [hK,mul_zero,norm_zero]; positivity
      by_cases hg0 : g (Real.log (q+1:ℝ)/Real.log T)=0
      · have hK : K p q n=0 := by simp [K,rectangularMomentPairWeight,hg0]
        rw [hK,mul_zero,norm_zero]; positivity
      let gap := rectangularAFEGap positive (p+1) (q+1) n
      have hgap : 1≤gap := by dsimp [gap]; exact Nat.succ_le_iff.mpr (rectangular_AFE_gap_pos positive _ _ n hselected)
      have hpCap : (p+1:ℝ)≤T^a := (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hp) : (p+1:ℝ)≤⌊T^a⌋₊).trans
        (Nat.floor_le (Real.rpow_nonneg hTp.le _))
      have hqCap : (q+1:ℝ)≤T^b := (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hq) : (q+1:ℝ)≤⌊T^b⌋₊).trans
        (Nat.floor_le (Real.rpow_nonneg hTp.le _))
      by_cases hnear : rectangularNearRelation (T^(s-1)) (rectangularAFESourceTuple (p+1) (q+1) n gap)
      · have he := a03ActualSourceNearPartition_eq_one hTp f g k n (by omega) (by omega) hgap
          (by simpa only [Nat.cast_add,Nat.cast_one] using hpCap) (by simpa only [Nat.cast_add,Nat.cast_one] using hqCap)
          (a03_actual_near_tuple_gap_cap hTp k n hk hw0 (by simpa only [Nat.cast_add,Nat.cast_one] using hpCap)
            (by simpa only [Nat.cast_add,Nat.cast_one] using hqCap) hnear)
          (by simpa only [Nat.cast_add,Nat.cast_one] using hf0) (by simpa only [Nat.cast_add,Nat.cast_one] using hg0)
          hw0 positive (rectangular_AFE_gap_source_relation positive _ _ n hselected) hnear
        simp only [gap] at he
        rw [he,sub_self,Complex.ofReal_zero,zero_mul,zero_mul,norm_zero]; positivity
      · have hfar : a03ActualFarSelection T s positive p q n := by
          refine ⟨hselected,?_⟩
          apply le_of_lt
          simpa [rectangularNearRelation,rectangularAFESourceTuple,gap] using (not_le.mp hnear)
        have hb := a03ActualSourceNearPartition_bounds T a b s u f g k
          (p:=p+1) (q:=q+1) (h:=gap) (by omega) (by omega) hgap
        rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr hb.2),
          Complex.norm_real,Real.norm_of_nonneg (rectangular_AFE_smooth_weight_nonneg k n)]
        calc
          _≤(1-a03ActualSourceNearPartition T a b s u f g k (p+1) (q+1) gap)*rectangularAFESmoothWeight k n*(L*T^(-Q)) :=
            mul_le_mul_of_nonneg_left (hkernel p q n hfar) (mul_nonneg (sub_nonneg.mpr hb.2) (rectangular_AFE_smooth_weight_nonneg k n))
          _≤L*T^(-Q) := by
            have hcoef : (1-a03ActualSourceNearPartition T a b s u f g k (p+1) (q+1) gap)*rectangularAFESmoothWeight k n≤1 := by
              have h := mul_le_mul (show 1-a03ActualSourceNearPartition T a b s u f g k (p+1) (q+1) gap≤1 by linarith [hb.1])
                (rectangular_small_contour_smooth_weight_le_one k n) (rectangular_AFE_smooth_weight_nonneg k n) zero_le_one
              simpa using h
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (mul_nonneg hL (Real.rpow_nonneg hTp.le _))
    · rw [ite_eq_right hselected,norm_zero]; positivity
  rw [a03_actual_source_far_residual_eq_sum]
  change ‖∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,term p q k n‖≤(L*D)*T^(-M)
  let masked (p q : ℕ) (k n : Fin 4→ℕ) : ℂ :=
    if p∈Finset.range ⌊T^a⌋₊ ∧ q∈Finset.range ⌊T^b⌋₊ ∧
      k∈rectangularAFEProductScaleGrid (T^(2+u)) then term p q k n else 0
  have hmasked (p q : ℕ) (k n : Fin 4→ℕ) : ‖masked p q k n‖≤L*T^(-Q) := by
    dsimp only [masked]
    split_ifs with hmem
    · exact hterm p hmem.1 q hmem.2.1 k hmem.2.2 n
    · rw [norm_zero]; positivity
  have heq : (∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
      ∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,term p q k n)=
      ∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
      ∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,masked p q k n := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro n _
    simp only [masked,hp,hq,hk,and_self,ite_true]
  have hsum := a03_finite_amplifier_grid_norm_le_card T a b u masked
    (mul_nonneg hL (Real.rpow_nonneg hTp.le _)) hmasked
  rw [←heq] at hsum
  calc
    _≤(L*T^(-Q))*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*
      (∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),((rectangularAFESmoothBox k).card:ℝ)) := hsum
    _≤(L*T^(-Q))*T^a*T^b*(D*T^(3+u)) := by
      have hna : (⌊T^a⌋₊:ℝ)≤T^a := Nat.floor_le (Real.rpow_nonneg hTp.le _)
      have hnb : (⌊T^b⌋₊:ℝ)≤T^b := Nat.floor_le (Real.rpow_nonneg hTp.le _)
      have hp0 : 0≤L*T^(-Q) := mul_nonneg hL (Real.rpow_nonneg hTp.le _)
      have hpa := mul_le_mul_of_nonneg_left hna hp0
      have hpab := mul_le_mul hpa hnb (Nat.cast_nonneg ⌊T^b⌋₊)
        (mul_nonneg hp0 (Real.rpow_nonneg hTp.le a))
      exact mul_le_mul hpab hcard (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg hp0 (Real.rpow_nonneg hTp.le a)) (Real.rpow_nonneg hTp.le b))
    _=(L*D)*T^((-Q+a+b)+(3+u)) := by
      rw [Real.rpow_add hTp (-Q+a+b) (3+u),Real.rpow_add hTp (-Q+a) b,Real.rpow_add hTp (-Q) a]
      ring
    _=(L*D)*T^(-M) := by congr 2; dsimp [Q]; ring

def a03ActualSourceFarResidualContour (dual positive : Bool) (c T a b s u θ : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualSourceFarResidualMellinGrid dual positive c T a b s u v f g Φ σ α

theorem a03ActualSourceFarResidualMellinGrid_frequency_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T a b s u : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j,‖α j‖≤1/4) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (dual positive : Bool) :
    StronglyMeasurable (fun v : ℝ => a03ActualSourceFarResidualMellinGrid dual positive c T a b s u v f g Φ σ α) := by
  let F (p q : ℕ) (k n : Fin 4→ℕ) (v : ℝ) : ℂ :=
    if (if positive then rectangularPositiveQuadGap (p+1) (q+1) n else rectangularNegativeQuadGap (p+1) (q+1) n) then
      ((1-a03ActualSourceNearPartition T a b s u f g k (p+1) (q+1)
        (rectangularAFEGap positive (p+1) (q+1) n):ℝ):ℂ)*(rectangularAFESmoothWeight k n:ℂ)*
      ∫ t : ℝ,rectangularMomentPairWeight T f g Φ p q t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
        rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I) else 0
  have he : (fun v : ℝ => a03ActualSourceFarResidualMellinGrid dual positive c T a b s u v f g Φ σ α)=
      ∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,F p q k n := by
    funext v
    simp only [Finset.sum_apply,F,a03_actual_source_far_residual_eq_sum]
  rw [he]
  apply Finset.stronglyMeasurable_sum
  intro p _
  apply Finset.stronglyMeasurable_sum
  intro q _
  apply Finset.stronglyMeasurable_sum
  intro k _
  apply Finset.stronglyMeasurable_sum
  intro n _
  dsimp only [F]
  by_cases hselected : if positive then rectangularPositiveQuadGap (p+1) (q+1) n else rectangularNegativeQuadGap (p+1) (q+1) n
  · simp only [hselected,ite_true]
    exact (a03_actual_far_time_kernel_frequency_stronglyMeasurable hc T f g Φ hΦ σ α hα hσ dual p q n).const_mul _
  · simp only [hselected,ite_false]
    exact stronglyMeasurable_const

theorem a03_actual_source_far_residual_contour_uniform_rapid
    {a b c u κ θ R s : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (hu : 0<u)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : 0<s) (hs1 : s≤1) (M : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual positive : Bool,
      IntegrableOn (fun v : ℝ => a03ActualSourceFarResidualMellinGrid dual positive c T a b s u v f g Φ σ α)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualSourceFarResidualContour dual positive c T a b s u θ f g Φ σ α‖≤C*T^(-M) := by
  obtain ⟨C₀,hC₀,hb⟩ := a03_actual_source_far_residual_grid_uniform_rapid hf hg hΦ hc hc1 hu hκ hθ hR hs hs1 (M+1)
  refine ⟨(1/(2*Real.pi))*C₀*(2*θ),by positivity,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℝ),
    rawMomentShifts_uniform_eventually_small hR (show (0:ℝ)<1/4 by norm_num)] with T hb hT hraw
  intro σ α hσ hα hroot dual positive
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hvbound (v : ℝ) (hv : v∈Icc (-θ*Real.log T) (θ*Real.log T)) :
      ‖a03ActualSourceFarResidualMellinGrid dual positive c T a b s u v f g Φ σ α‖≤C₀*T^(-(M+1)) :=
    hb σ α hσ hα hroot v (abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv)) dual positive
  have hsm := a03ActualSourceFarResidualMellinGrid_frequency_stronglyMeasurable hc T a b s u f g Φ hΦ
    σ α hα (hraw σ hσ) dual positive
  have hsfinite : volume (Icc (-θ*Real.log T) (θ*Real.log T))<⊤ := isCompact_Icc.measure_lt_top
  constructor
  · apply IntegrableOn.of_bound hsfinite hsm.aestronglyMeasurable (C₀*T^(-(M+1)))
    exact ae_restrict_of_forall_mem measurableSet_Icc hvbound
  · have hint := norm_setIntegral_le_of_norm_le_const hsfinite hvbound
    have hmeasure : volume.real (Icc (-θ*Real.log T) (θ*Real.log T))=2*θ*Real.log T := by
      rw [Real.volume_real_Icc,max_eq_left (by nlinarith [Real.log_nonneg hT])]
      ring
    rw [hmeasure] at hint
    have hconst : ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) := by
      rw [show (1/(2*Real.pi):ℂ)=((1/(2*Real.pi):ℝ):ℂ) by push_cast; rfl,
        Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    unfold a03ActualSourceFarResidualContour
    rw [norm_mul,hconst]
    calc
      _≤(1/(2*Real.pi))*(C₀*T^(-(M+1))*(2*θ*Real.log T)) := mul_le_mul_of_nonneg_left hint (by positivity)
      _≤(1/(2*Real.pi))*(C₀*T^(-(M+1))*(2*θ*T)) := by gcongr; exact Real.log_le_self hTp.le
      _=_ := by
        rw [show -M=-(M+1)+1 by ring,Real.rpow_add hTp,Real.rpow_one]
        ring

end
end Sechstmoment
