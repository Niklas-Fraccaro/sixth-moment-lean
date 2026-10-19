import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Sechstmoment.Numerator.U.Replacement.DualErrorPartsFarFinite
import Sechstmoment.Numerator.U.Replacement.WeightReplacementContour

/-! Genuine frequency measurability, finite near/far decomposition and Mellin
integration for the actual amplified weight replacement error. -/
namespace Sechstmoment
open Complex Source Real MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03ActualDualErrorPartFiniteMellinGrid (phasePart : Bool) (c T a b η v : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
      (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
        rectangularMomentPairWeight T f g Φ u w t*
        rectangularDualErrorPartMellinKernel phasePart T σ (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I))

def a03ActualDualErrorPartNearFiniteMellinGrid (phasePart : Bool) (c T a b η ρ v : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
      if a03ActualWeightReplacementNearSelection T ρ u w n then
        (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
          rectangularMomentPairWeight T f g Φ u w t*
          rectangularDualErrorPartMellinKernel phasePart T σ (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I))
      else 0

def a03ActualDualErrorPartFarFiniteContour (phasePart : Bool) (positive : Bool) (c T a b η ρ θ : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualDualErrorPartFarFiniteMellinGrid phasePart positive c T a b η ρ v f g Φ σ α

def a03ActualDualErrorPartFiniteContour (phasePart : Bool) (c T a b η θ : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualDualErrorPartFiniteMellinGrid phasePart c T a b η v f g Φ σ α

def a03ActualDualErrorPartNearFiniteContour (phasePart : Bool) (c T a b η ρ θ : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualDualErrorPartNearFiniteMellinGrid phasePart c T a b η ρ v f g Φ σ α

theorem rectangular_dual_error_part_Mellin_kernel_joint_measurable (phasePart : Bool)
    {c : ℝ} (hc : 0<c) (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (n : Fin 4→ℕ) :
    Measurable (fun p : ℝ×ℝ => rectangularDualErrorPartMellinKernel phasePart T σ
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
  have hs : ∀ j, |(rawMomentShifts T σ j).re|<1/2 := fun j =>
    ((Complex.abs_re_le_norm _).trans (hσ j)).trans_lt (by norm_num)
  have hχ : Continuous (fun p : ℝ×ℝ => bblrDualMultiplier p.2 (rawMomentShifts T σ)) :=
    (rectangular_dual_multiplier_continuous _ hs).comp continuous_snd
  have hB : Measurable (fun p : ℝ×ℝ =>
      (p.2/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j)) := by
    simp_rw [Complex.cpow_def]
    apply Measurable.ite (by measurability)
    · exact measurable_const
    · fun_prop
  unfold rectangularDualErrorPartMellinKernel
  cases phasePart
  · simp only [Bool.false_eq_true,ite_false]
    exact (((((hG.measurable.div hz.measurable).mul
      (hχ.measurable.mul (hQ.measurable.sub hP))).mul
      hπ.measurable).mul hosc.measurable).div hden.measurable)
  · simp only [ite_true]
    exact (((((hG.measurable.div hz.measurable).mul
      ((hχ.measurable.sub hB).mul hP)).mul
      hπ.measurable).mul hosc.measurable).div hden.measurable)

theorem rectangular_dual_error_part_time_kernel_frequency_stronglyMeasurable (phasePart : Bool)
    {c : ℝ} (hc : 0<c) (T : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (u w : ℕ) (n : Fin 4→ℕ) :
    StronglyMeasurable (fun v : ℝ => ∫ t : ℝ,
      rectangularMomentPairWeight T f g Φ u w t*
      rectangularDualErrorPartMellinKernel phasePart T σ (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) := by
  have hm : Continuous (fun p : ℝ×ℝ => rectangularMomentPairWeight T f g Φ u w p.2) :=
    (rectangular_moment_pair_weight_continuous T f g Φ hΦ u w).comp continuous_snd
  have hk := rectangular_dual_error_part_Mellin_kernel_joint_measurable phasePart hc T σ α hα hσ n
  exact (hm.measurable.mul hk).stronglyMeasurable.integral_prod_right'

private theorem dual_error_part_selected_grid_frequency_stronglyMeasurable (phasePart : Bool)
    {c : ℝ} (hc : 0<c) (T a b η : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4)
    (P : ℕ→ℕ→(Fin 4→ℕ)→Prop) :
    StronglyMeasurable (fun v : ℝ =>
      ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
          if P u w n then (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
            rectangularMomentPairWeight T f g Φ u w t*
            rectangularDualErrorPartMellinKernel phasePart T σ (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0) := by
  have he : (fun v : ℝ =>
      ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
          if P u w n then (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
            rectangularMomentPairWeight T f g Φ u w t*
            rectangularDualErrorPartMellinKernel phasePart T σ (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0)=
      ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
          fun v : ℝ => if P u w n then (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
            rectangularMomentPairWeight T f g Φ u w t*
            rectangularDualErrorPartMellinKernel phasePart T σ (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0 := by
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
    exact (rectangular_dual_error_part_time_kernel_frequency_stronglyMeasurable phasePart hc T f g Φ hΦ σ α hα hσ u w n).const_mul _
  · simp only [hs,ite_false]
    exact stronglyMeasurable_const

theorem a03ActualDualErrorPartFarFiniteMellinGrid_frequency_stronglyMeasurable (phasePart : Bool)
    {c : ℝ} (hc : 0<c) (T a b η ρ : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (positive : Bool) :
    StronglyMeasurable (fun v : ℝ =>
      a03ActualDualErrorPartFarFiniteMellinGrid phasePart positive c T a b η ρ v f g Φ σ α) :=
  dual_error_part_selected_grid_frequency_stronglyMeasurable phasePart hc T a b η f g Φ hΦ σ α hα hσ
    (a03ActualWeightReplacementFarSelection T ρ positive)

theorem a03ActualDualErrorPartNearFiniteMellinGrid_frequency_stronglyMeasurable (phasePart : Bool)
    {c : ℝ} (hc : 0<c) (T a b η ρ : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) :
    StronglyMeasurable (fun v : ℝ =>
      a03ActualDualErrorPartNearFiniteMellinGrid phasePart c T a b η ρ v f g Φ σ α) :=
  dual_error_part_selected_grid_frequency_stronglyMeasurable phasePart hc T a b η f g Φ hΦ σ α hα hσ
    (a03ActualWeightReplacementNearSelection T ρ)

theorem a03ActualDualErrorPartFiniteMellinGrid_frequency_stronglyMeasurable (phasePart : Bool)
    {c : ℝ} (hc : 0<c) (T a b η : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) :
    StronglyMeasurable (fun v : ℝ =>
      a03ActualDualErrorPartFiniteMellinGrid phasePart c T a b η v f g Φ σ α) := by
  simpa only [a03ActualDualErrorPartFiniteMellinGrid,ite_true] using
    dual_error_part_selected_grid_frequency_stronglyMeasurable phasePart hc T a b η f g Φ hΦ σ α hα hσ
      (fun _ _ _ => True)

/-- Complete far Mellin contour, including actual finite arithmetic sums. -/
theorem a03_actual_dual_error_part_far_finite_contour_uniform_rapid
    {a b c η κ θ R ρ : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (hη : 0<η)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hρ : 0<ρ) (hρ1 : ρ≤1) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) → ∀ phasePart : Bool, ∀ positive : Bool,
      IntegrableOn (fun v : ℝ => a03ActualDualErrorPartFarFiniteMellinGrid phasePart positive c T a b η ρ v f g Φ σ α)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualDualErrorPartFarFiniteContour phasePart positive c T a b η ρ θ f g Φ σ α‖≤C*T^(-M) := by
  obtain ⟨C₀,hC₀,hb⟩ := a03_actual_dual_error_part_far_finite_grid_uniform_rapid hf hg hΦ hc hc1 hη
    hκ hθ hR hρ hρ1 (M+1)
  refine ⟨(1/(2*Real.pi))*C₀*(2*θ),by positivity,?_⟩
  have hsmall := rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4)
  filter_upwards [hb,eventually_ge_atTop (1:ℝ),hsmall] with T hb hT hraw
  intro σ α hσ hα hroot phasePart positive
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hL : 0≤Real.log T := Real.log_nonneg hT
  have hθL : 0≤θ*Real.log T := mul_nonneg hθ hL
  have hvbound (v : ℝ) (hv : v∈Icc (-θ*Real.log T) (θ*Real.log T)) :
      ‖a03ActualDualErrorPartFarFiniteMellinGrid phasePart positive c T a b η ρ v f g Φ σ α‖≤C₀*T^(-(M+1)) := by
    apply hb σ α hσ hα hroot phasePart v _ positive
    exact abs_le.mpr (by simpa only [neg_mul,Set.mem_Icc] using hv)
  have hsm := a03ActualDualErrorPartFarFiniteMellinGrid_frequency_stronglyMeasurable phasePart hc T a b η ρ
    f g Φ hΦ σ α hα (hraw σ hσ) positive
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
    unfold a03ActualDualErrorPartFarFiniteContour
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


/-- Exact full finite Mellin-grid reconstruction. -/
theorem a03ActualDualErrorPartFiniteMellinGrid_near_add_far (phasePart : Bool) {T : ℝ} (hT : 0<T)
    (c a b η ρ v : ℝ) (f g Φ : ℝ→ℝ) (σ α : MomentShifts) :
    a03ActualDualErrorPartFiniteMellinGrid phasePart c T a b η v f g Φ σ α=
      a03ActualDualErrorPartNearFiniteMellinGrid phasePart c T a b η ρ v f g Φ σ α+
        a03ActualDualErrorPartFarFiniteMellinGrid phasePart true c T a b η ρ v f g Φ σ α+
        a03ActualDualErrorPartFarFiniteMellinGrid phasePart false c T a b η ρ v f g Φ σ α := by
  unfold a03ActualDualErrorPartFiniteMellinGrid a03ActualDualErrorPartNearFiniteMellinGrid
    a03ActualDualErrorPartFarFiniteMellinGrid
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
