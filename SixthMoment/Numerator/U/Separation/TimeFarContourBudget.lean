import Mathlib.MeasureTheory.Integral.Prod
import SixthMoment.Numerator.Polar.RemainderDecay
import SixthMoment.Numerator.U.Separation.TimeFarFiniteBudget

namespace SixthMoment
open Complex Source Real MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal
open Classical
noncomputable section
set_option maxHeartbeats 1200000

theorem a03_small_positive_Gamma_quotient_joint_continuous
    {c : ℝ} (hc : 0<c) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
    Continuous (fun p : ℝ×ℝ => bblrGammaQuotient p.2 α ((c:ℂ)+(p.1:ℂ)*I)) := by
  unfold bblrGammaQuotient
  apply continuous_finsetProd
  intro j _
  have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
  apply Continuous.div
  · apply continuous_iff_continuousAt.mpr
    intro p
    apply (Complex.continuousAt_Gamma _ ?_).comp
    · apply Continuous.continuousAt
      exact ((((rectangular_source_point_continuous j).comp continuous_snd).add continuous_const).add
        (by fun_prop)).div_const 2
    · intro n hn
      have hr := congrArg Complex.re hn
      have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
      simp at hr
      linarith
  · apply continuous_iff_continuousAt.mpr
    intro p
    apply (Complex.continuousAt_Gamma _ ?_).comp
    · exact ((((rectangular_source_point_continuous j).comp continuous_snd).add continuous_const).div_const 2).continuousAt
    · intro n hn
      have hr := congrArg Complex.re hn
      have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
      simp at hr
      linarith
  · intro p
    apply Complex.Gamma_ne_zero
    intro n hn
    have hr := congrArg Complex.re hn
    have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
    simp at hr
    linarith

theorem a03_actual_small_Mellin_kernel_joint_continuous
    {c : ℝ} (hc : 0<c) (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (n : Fin 4 → ℕ) :
    Continuous (fun p : ℝ×ℝ => rectangularAFEMellinKernel (polarPoleKiller T σ) α p.2 n
      ((c:ℂ)+(p.1:ℂ)*I)) := by
  have hz : Continuous (fun p : ℝ×ℝ => (c:ℂ)+(p.1:ℂ)*I) := by fun_prop
  have hz0 (p : ℝ×ℝ) : (c:ℂ)+(p.1:ℂ)*I≠0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith
  have hG := (polarPoleKiller_differentiable T σ).continuous.comp hz
  have hQ := a03_small_positive_Gamma_quotient_joint_continuous hc α hα
  have hπ : Continuous (fun p : ℝ×ℝ => (Real.pi:ℂ)^(-2*((c:ℂ)+(p.1:ℂ)*I))) := by
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hx : 0<(positiveQuadProduct n:ℝ) := by unfold positiveQuadProduct; positivity
  have hxpow : Continuous (fun p : ℝ×ℝ => ((positiveQuadProduct n:ℝ):ℂ)^(-((c:ℂ)+(p.1:ℂ)*I))) := by
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')
  have hosc : Continuous (fun t : ℝ => rectangularAFEOscillation t n) := by
    unfold rectangularAFEOscillation
    apply Continuous.const_cpow
    · fun_prop
    · apply Or.inl
      have h₁ : (((n 0+1)*(n 1+1):ℕ):ℂ)≠0 := by
        exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 0)) (Nat.succ_ne_zero (n 1))
      have h₂ : (((n 2+1)*(n 3+1):ℕ):ℂ)≠0 := by
        exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 2)) (Nat.succ_ne_zero (n 3))
      exact div_ne_zero h₁ h₂
  have hfirst : Continuous (fun p : ℝ×ℝ => rectangularAFEOscillation p.2 n/
      ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j)) := (hosc.comp continuous_snd).div_const _
  have hh := hfirst.mul ((((hG.div hz hz0).mul hQ).mul hπ).mul hxpow)
  convert hh using 1
  funext p
  simp only [rectangular_AFE_Mellin_kernel_general_line,bblrVKernel,Pi.mul_apply,Pi.div_apply,
    Function.comp_apply]

theorem a03_actual_far_time_kernel_frequency_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T : ℝ) (f g Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4)
    (dual : Bool) (u w : ℕ) (n : Fin 4 → ℕ) :
    StronglyMeasurable (fun v : ℝ => ∫ t : ℝ,
      rectangularMomentPairWeight T f g Φ u w t*
      (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
      rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) := by
  have hs : ∀ j, |(rawMomentShifts T σ j).re|<1/2 := by
    intro j
    exact ((Complex.abs_re_le_norm _).trans (hσ j)).trans_lt (by norm_num)
  have hd : Continuous (fun p : ℝ×ℝ => if dual then
      bblrDualMultiplier p.2 (rawMomentShifts T σ) else 1) := by
    cases dual
    · exact continuous_const
    · exact (rectangular_dual_multiplier_continuous _ hs).comp continuous_snd
  have hm : Continuous (fun p : ℝ×ℝ => rectangularMomentPairWeight T f g Φ u w p.2) :=
    (rectangular_moment_pair_weight_continuous T f g Φ hΦ u w).comp continuous_snd
  have hk := a03_actual_small_Mellin_kernel_joint_continuous hc T σ α hα n
  exact ((hm.mul hd).mul hk).stronglyMeasurable.integral_prod_right'

theorem a03ActualFarFiniteMellinGrid_frequency_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T a b ε ρ : ℝ) (f g Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (dual positive : Bool) :
    StronglyMeasurable (fun v : ℝ =>
      a03ActualFarFiniteMellinGrid dual positive c T a b ε ρ v f g Φ σ α) := by
  have he : (fun v : ℝ => a03ActualFarFiniteMellinGrid dual positive c T a b ε ρ v f g Φ σ α) =
      ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)), ∑ n∈rectangularAFESmoothBox k,
          fun v : ℝ => if a03ActualFarSelection T ρ positive u w n then
            (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
              rectangularMomentPairWeight T f g Φ u w t*
              (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
              rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0 := by
    funext v
    simp only [Finset.sum_apply,a03ActualFarFiniteMellinGrid]
  rw [he]
  apply Finset.stronglyMeasurable_sum
  intro u _
  apply Finset.stronglyMeasurable_sum
  intro w _
  apply Finset.stronglyMeasurable_sum
  intro k _
  apply Finset.stronglyMeasurable_sum
  intro n _
  by_cases hs : a03ActualFarSelection T ρ positive u w n
  · simp only [hs,ite_true]
    exact (a03_actual_far_time_kernel_frequency_stronglyMeasurable hc T f g Φ hΦ σ α hα hσ dual u w n).const_mul _
  · simp only [hs,ite_false]
    exact stronglyMeasurable_const


def a03ActualFarFiniteContour (dual positive : Bool) (c T a b ε ρ θ : ℝ)
    (f g Φ : ℝ → ℝ) (σ α : MomentShifts) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualFarFiniteMellinGrid dual positive c T a b ε ρ v f g Φ σ α

theorem a03_actual_far_finite_contour_uniform_rapid
    {a b c ε κ θ R ρ : ℝ} {f g Φ : ℝ → ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (hε : 0<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hρ : 0<ρ) (hρ1 : ρ≤1) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual positive : Bool,
      IntegrableOn (fun v : ℝ => a03ActualFarFiniteMellinGrid dual positive c T a b ε ρ v f g Φ σ α)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualFarFiniteContour dual positive c T a b ε ρ θ f g Φ σ α‖≤C*T^(-M) := by
  obtain ⟨C₀,hC₀,hb⟩ := a03_actual_far_finite_grid_uniform_rapid hf hg hΦ hc hc1 hε
    hκ hθ hR hρ hρ1 (M+1)
  refine ⟨(1/(2*Real.pi))*C₀*(2*θ),by positivity,?_⟩
  have hsmall : ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
      ∀ j, ‖rawMomentShifts T σ j‖≤1/4 :=
    rawMomentShifts_uniform_eventually_small hR (show (0:ℝ)<1/4 by norm_num)
  filter_upwards [hb,eventually_ge_atTop (1:ℝ),hsmall] with T hb hT hraw
  intro σ α hσ hα hroot dual positive
  have ht0 : 0<T := zero_lt_one.trans_le hT
  have hL : 0≤Real.log T := Real.log_nonneg hT
  have hθL : 0≤θ*Real.log T := mul_nonneg hθ hL
  have hvbound (v : ℝ) (hv : v∈Icc (-θ*Real.log T) (θ*Real.log T)) :
      ‖a03ActualFarFiniteMellinGrid dual positive c T a b ε ρ v f g Φ σ α‖≤C₀*T^(-(M+1)) := by
    apply hb σ α hσ hα hroot v _ dual positive
    exact abs_le.mpr (by simpa only [neg_mul,Set.mem_Icc] using hv)
  have hsm := a03ActualFarFiniteMellinGrid_frequency_stronglyMeasurable hc T a b ε ρ
    f g Φ hΦ σ α hα (hraw σ hσ) dual positive
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
    unfold a03ActualFarFiniteContour
    rw [norm_mul,hconst]
    calc
      _ ≤ (1/(2*Real.pi))*(C₀*T^(-(M+1))*(2*θ*Real.log T)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
      _ ≤ (1/(2*Real.pi))*(C₀*T^(-(M+1))*(2*θ*T)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (Real.log_le_self ht0.le) (by positivity)
      _ = _ := by
        rw [show -M=-(M+1)+1 by ring,Real.rpow_add ht0 (-(M+1)) 1,Real.rpow_one]
        ring

end
