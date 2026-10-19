import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Sechstmoment.Numerator.U.Replacement.WeightReplacementFarFinite
import Sechstmoment.Numerator.U.Separation.TimeFarContourBudget

/-! Genuine frequency measurability, finite near/far decomposition and Mellin
integration for the actual amplified weight replacement error. -/
namespace Sechstmoment
open Complex Source Real MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03ActualWeightReplacementFiniteMellinGrid (c T a b η v : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
      (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
        rectangularMomentPairWeight T f g Φ u w t*
        rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I))

def a03ActualWeightReplacementNearFiniteMellinGrid (c T a b η ρ v : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
      if a03ActualWeightReplacementNearSelection T ρ u w n then
        (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
          rectangularMomentPairWeight T f g Φ u w t*
          rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I))
      else 0

def a03ActualWeightReplacementFarFiniteContour (positive : Bool) (c T a b η ρ θ : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualWeightReplacementFarFiniteMellinGrid positive c T a b η ρ v f g Φ σ α

def a03ActualWeightReplacementFiniteContour (c T a b η θ : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualWeightReplacementFiniteMellinGrid c T a b η v f g Φ σ α

def a03ActualWeightReplacementNearFiniteContour (c T a b η ρ θ : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ α

theorem rectangular_weight_replacement_Mellin_kernel_joint_measurable
    {c : ℝ} (hc : 0<c) (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (n : Fin 4→ℕ) :
    Measurable (fun p : ℝ×ℝ => rectangularWeightReplacementMellinKernel
      (polarPoleKiller T σ) α p.2 n ((c:ℂ)+(p.1:ℂ)*I)) := by
  have hz : Continuous (fun p : ℝ×ℝ => (c:ℂ)+(p.1:ℂ)*I) := by fun_prop
  have hG := (polarPoleKiller_differentiable T σ).continuous.comp hz
  have hQ := a03_small_positive_Gamma_quotient_joint_continuous hc α hα
  have hP : Measurable (fun p : ℝ×ℝ => (p.2/2:ℂ)^(2*((c:ℂ)+(p.1:ℂ)*I))) := by
    simp_rw [Complex.cpow_def]
    apply Measurable.ite (by measurability)
    · exact Measurable.ite (by measurability) measurable_const measurable_const
    · fun_prop
  have hπ : Continuous (fun p : ℝ×ℝ => (Real.pi:ℂ)^(-2*((c:ℂ)+(p.1:ℂ)*I))) := by
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hosc : Continuous (fun p : ℝ×ℝ => rectangularAFEOscillation p.2 n) := by
    unfold rectangularAFEOscillation
    apply Continuous.const_cpow
    · fun_prop
    · apply Or.inl
      have h₁ : (((n 0+1)*(n 1+1):ℕ):ℂ)≠0 := by
        exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 0)) (Nat.succ_ne_zero (n 1))
      have h₂ : (((n 2+1)*(n 3+1):ℕ):ℂ)≠0 := by
        exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 2)) (Nat.succ_ne_zero (n 3))
      exact div_ne_zero h₁ h₂
  have hden : Continuous (fun p : ℝ×ℝ =>
      ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+((c:ℂ)+(p.1:ℂ)*I))) := by
    apply continuous_finsetProd
    intro j _
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (by exact_mod_cast Nat.succ_ne_zero (n j))
  unfold rectangularWeightReplacementMellinKernel
  exact (((((hG.measurable.div hz.measurable).mul (hQ.measurable.sub hP)).mul
    hπ.measurable).mul hosc.measurable).div hden.measurable)

theorem rectangular_weight_replacement_time_kernel_frequency_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (u w : ℕ) (n : Fin 4→ℕ) :
    StronglyMeasurable (fun v : ℝ => ∫ t : ℝ,
      rectangularMomentPairWeight T f g Φ u w t*
      rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) := by
  have hm : Continuous (fun p : ℝ×ℝ => rectangularMomentPairWeight T f g Φ u w p.2) :=
    (rectangular_moment_pair_weight_continuous T f g Φ hΦ u w).comp continuous_snd
  have hk := rectangular_weight_replacement_Mellin_kernel_joint_measurable hc T σ α hα n
  exact (hm.measurable.mul hk).stronglyMeasurable.integral_prod_right'

private theorem weight_replacement_selected_grid_frequency_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T a b η : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (P : ℕ→ℕ→(Fin 4→ℕ)→Prop) :
    StronglyMeasurable (fun v : ℝ =>
      ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
          if P u w n then (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
            rectangularMomentPairWeight T f g Φ u w t*
            rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0) := by
  have he : (fun v : ℝ =>
      ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
          if P u w n then (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
            rectangularMomentPairWeight T f g Φ u w t*
            rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0)=
      ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
          fun v : ℝ => if P u w n then (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
            rectangularMomentPairWeight T f g Φ u w t*
            rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0 := by
    funext v
    simp only [Finset.sum_apply]
  rw [he]
  apply Finset.stronglyMeasurable_sum
  intro u _
  apply Finset.stronglyMeasurable_sum
  intro w _
  apply Finset.stronglyMeasurable_sum
  intro k _
  apply Finset.stronglyMeasurable_sum
  intro n _
  by_cases hs : P u w n
  · simp only [hs,ite_true]
    exact (rectangular_weight_replacement_time_kernel_frequency_stronglyMeasurable hc T f g Φ hΦ σ α hα u w n).const_mul _
  · simp only [hs,ite_false]
    exact stronglyMeasurable_const

theorem a03ActualWeightReplacementFarFiniteMellinGrid_frequency_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T a b η ρ : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (positive : Bool) :
    StronglyMeasurable (fun v : ℝ =>
      a03ActualWeightReplacementFarFiniteMellinGrid positive c T a b η ρ v f g Φ σ α) :=
  weight_replacement_selected_grid_frequency_stronglyMeasurable hc T a b η f g Φ hΦ σ α hα
    (a03ActualWeightReplacementFarSelection T ρ positive)

theorem a03ActualWeightReplacementNearFiniteMellinGrid_frequency_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T a b η ρ : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
    StronglyMeasurable (fun v : ℝ =>
      a03ActualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ α) :=
  weight_replacement_selected_grid_frequency_stronglyMeasurable hc T a b η f g Φ hΦ σ α hα
    (a03ActualWeightReplacementNearSelection T ρ)

theorem a03ActualWeightReplacementFiniteMellinGrid_frequency_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T a b η : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
    StronglyMeasurable (fun v : ℝ =>
      a03ActualWeightReplacementFiniteMellinGrid c T a b η v f g Φ σ α) := by
  simpa only [a03ActualWeightReplacementFiniteMellinGrid,ite_true] using
    weight_replacement_selected_grid_frequency_stronglyMeasurable hc T a b η f g Φ hΦ σ α hα
      (fun _ _ _ => True)

/-- Complete far Mellin contour, including actual finite arithmetic sums. -/
theorem a03_actual_weight_replacement_far_finite_contour_uniform_rapid
    {a b c η κ θ ρ : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (hη : 0<η)
    (hκ : 0<κ) (hθ : 0≤θ) (hρ : 0<ρ) (hρ1 : ρ≤1) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) → ∀ positive : Bool,
      IntegrableOn (fun v : ℝ => a03ActualWeightReplacementFarFiniteMellinGrid positive c T a b η ρ v f g Φ σ α)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualWeightReplacementFarFiniteContour positive c T a b η ρ θ f g Φ σ α‖≤C*T^(-M) := by
  obtain ⟨C₀,hC₀,hb⟩ := a03_actual_weight_replacement_far_finite_grid_uniform_rapid hf hg hΦ hc hc1 hη
    hκ hθ hρ hρ1 (M+1)
  refine ⟨(1/(2*Real.pi))*C₀*(2*θ),by positivity,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with T hb hT
  intro σ α hα hroot positive
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hL : 0≤Real.log T := Real.log_nonneg hT
  have hθL : 0≤θ*Real.log T := mul_nonneg hθ hL
  have hvbound (v : ℝ) (hv : v∈Icc (-θ*Real.log T) (θ*Real.log T)) :
      ‖a03ActualWeightReplacementFarFiniteMellinGrid positive c T a b η ρ v f g Φ σ α‖≤C₀*T^(-(M+1)) := by
    apply hb σ α hα hroot v _ positive
    exact abs_le.mpr (by simpa only [neg_mul,Set.mem_Icc] using hv)
  have hsm := a03ActualWeightReplacementFarFiniteMellinGrid_frequency_stronglyMeasurable hc T a b η ρ
    f g Φ hΦ σ α hα positive
  have hsfinite : volume (Icc (-θ*Real.log T) (θ*Real.log T))<∞ := isCompact_Icc.measure_lt_top
  constructor
  · apply IntegrableOn.of_bound hsfinite hsm.aestronglyMeasurable (C₀*T^(-(M+1)))
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with v hv
    exact hvbound v hv
  · have hint := norm_setIntegral_le_of_norm_le_const hsfinite hvbound
    have hmeasure : volume.real (Icc (-θ*Real.log T) (θ*Real.log T))=2*θ*Real.log T := by
      rw [Real.volume_real_Icc_of_le (by linarith)]
      ring
    rw [hmeasure] at hint
    have hconst : ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) := by
      rw [show (1/(2*Real.pi):ℂ)=((1/(2*Real.pi):ℝ):ℂ) by push_cast; rfl,
        Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    unfold a03ActualWeightReplacementFarFiniteContour
    rw [norm_mul,hconst]
    calc
      _≤(1/(2*Real.pi))*(C₀*T^(-(M+1))*(2*θ*Real.log T)) := mul_le_mul_of_nonneg_left hint (by positivity)
      _≤(1/(2*Real.pi))*(C₀*T^(-(M+1))*(2*θ*T)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (Real.log_le_self hTp.le) (by positivity)
      _=_ := by
        rw [show -M=-(M+1)+1 by ring,Real.rpow_add hTp (-(M+1)) 1,Real.rpow_one]
        ring


/-- The inclusive near region and the two restricted far signs partition
every actual AFE tuple, including the exact diagonal. -/
theorem a03_weight_replacement_near_far_indicator_partition {T : ℝ} (hT : 0<T)
    (ρ : ℝ) (u w : ℕ) (n : Fin 4→ℕ) (e : ℂ) :
    e=(if a03ActualWeightReplacementNearSelection T ρ u w n then e else 0)+
      (if a03ActualWeightReplacementFarSelection T ρ true u w n then e else 0)+
      (if a03ActualWeightReplacementFarSelection T ρ false u w n then e else 0) := by
  by_cases hn : a03ActualWeightReplacementNearSelection T ρ u w n
  · simp [hn,a03ActualWeightReplacementFarSelection]
  · let A := (u+1)*(n 0+1)*(n 1+1)
    let B := (w+1)*(n 2+1)*(n 3+1)
    let H := T^(ρ-1)*Real.sqrt ((u+1:ℝ)*(w+1)*(n 0+1)*(n 1+1)*(n 2+1)*(n 3+1))
    have hH : 0≤H := by dsimp [H]; positivity
    have hg : H≤|(A:ℝ)-(B:ℝ)| := (lt_of_not_ge hn).le
    rcases lt_trichotomy A B with h | h | h
    · have hnegative : rectangularNegativeQuadGap (u+1) (w+1) n := h
      have hpositive : ¬rectangularPositiveQuadGap (u+1) (w+1) n := not_lt_of_ge h.le
      have hgap : (rectangularAFEGap false (u+1) (w+1) n:ℝ)=|(A:ℝ)-(B:ℝ)| := by
        unfold rectangularAFEGap
        simp only [Bool.false_eq_true,ite_false]
        change ((B-A:ℕ):ℝ)=|(A:ℝ)-(B:ℝ)|
        rw [Nat.cast_sub h.le,abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h.le : (A:ℝ)≤B))]
        ring
      have hf : a03ActualWeightReplacementFarSelection T ρ false u w n :=
        ⟨hn,hnegative,by change H≤_; rw [hgap]; exact hg⟩
      have hp : ¬a03ActualWeightReplacementFarSelection T ρ true u w n := by
        intro hp
        exact hpositive hp.2.1
      simp [hn,hf,hp]
    · exfalso
      apply hn
      change |(A:ℝ)-(B:ℝ)|≤H
      rw [h,sub_self,abs_zero]
      exact hH
    · have hpositive : rectangularPositiveQuadGap (u+1) (w+1) n := h
      have hnegative : ¬rectangularNegativeQuadGap (u+1) (w+1) n := not_lt_of_ge h.le
      have hgap : (rectangularAFEGap true (u+1) (w+1) n:ℝ)=|(A:ℝ)-(B:ℝ)| := by
        unfold rectangularAFEGap
        simp only [ite_true]
        change ((A-B:ℕ):ℝ)=|(A:ℝ)-(B:ℝ)|
        rw [Nat.cast_sub h.le,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h.le : (B:ℝ)≤A))]
      have hf : a03ActualWeightReplacementFarSelection T ρ true u w n :=
        ⟨hn,hpositive,by change H≤_; rw [hgap]; exact hg⟩
      have hp : ¬a03ActualWeightReplacementFarSelection T ρ false u w n := by
        intro hp
        exact hnegative hp.2.1
      simp [hn,hf,hp]

/-- Exact full finite Mellin-grid reconstruction. -/
theorem a03ActualWeightReplacementFiniteMellinGrid_near_add_far {T : ℝ} (hT : 0<T)
    (c a b η ρ v : ℝ) (f g Φ : ℝ→ℝ) (σ α : MomentShifts) :
    a03ActualWeightReplacementFiniteMellinGrid c T a b η v f g Φ σ α=
      a03ActualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ α+
        a03ActualWeightReplacementFarFiniteMellinGrid true c T a b η ρ v f g Φ σ α+
        a03ActualWeightReplacementFarFiniteMellinGrid false c T a b η ρ v f g Φ σ α := by
  unfold a03ActualWeightReplacementFiniteMellinGrid a03ActualWeightReplacementNearFiniteMellinGrid
    a03ActualWeightReplacementFarFiniteMellinGrid
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro n _
  exact a03_weight_replacement_near_far_indicator_partition hT ρ u w n _

end
end Sechstmoment
