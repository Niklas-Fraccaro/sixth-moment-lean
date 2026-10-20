import Mathlib.MeasureTheory.Integral.Prod
import Sechstmoment.Numerator.U.Replacement.AmplifiedSmallContourMoment
import Sechstmoment.Numerator.U.Replacement.DualWeightReplacementContour
import Sechstmoment.Numerator.U.Replacement.VStar.KernelReplacement
import Sechstmoment.Numerator.U.Separation.DualLeadingRegularity

namespace Sechstmoment
open Complex Source Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_pair_weight_zero_outside {T : ℝ} (hT : 0<T)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) (u w : ℕ)
    (t : ℝ) (ht : t∉Icc T (2*T)) : rectangularMomentPairWeight T f g Φ u w t=0 := by
  have hz : Φ (t/T)=0 := by
    by_contra hn
    have hs : t/T∈tsupport Φ := subset_tsupport Φ (by simpa only [Function.mem_support] using hn)
    have hh := hΦ.2 hs
    exact ht ⟨by simpa using (le_div_iff₀ hT).mp hh.1,(div_le_iff₀ hT).mp hh.2⟩
  simp [rectangularMomentPairWeight,hz]

theorem a03_pair_compact_time_contour_integrable {T : ℝ} (hT : 0<T)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) (u w : ℕ) (R : ℝ)
    (K : ℝ×ℝ→ℂ) (hK : ContinuousOn K (Icc (-R) R ×ˢ Icc T (2*T))) :
    Integrable (fun p : ℝ×ℝ => rectangularMomentPairWeight T f g Φ u w p.2*K p)
      ((volume.restrict (Icc (-R) R)).prod volume) := by
  let F : ℝ×ℝ→ℂ := fun p => rectangularMomentPairWeight T f g Φ u w p.2*K p
  have hw : Continuous (fun p : ℝ×ℝ => rectangularMomentPairWeight T f g Φ u w p.2) :=
    (rectangular_moment_pair_weight_continuous T f g Φ hΦ u w).comp continuous_snd
  have hFc : ContinuousOn F (Icc (-R) R ×ˢ Icc T (2*T)) := hw.continuousOn.mul hK
  have hi : Integrable F ((volume.restrict (Icc (-R) R)).prod (volume.restrict (Icc T (2*T)))) := by
    rw [Measure.prod_restrict]
    exact hFc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hIon : IntegrableOn F (univ ×ˢ Icc T (2*T)) ((volume.restrict (Icc (-R) R)).prod volume) := by
    rw [IntegrableOn,← Measure.prod_restrict,Measure.restrict_univ]
    exact hi
  exact hIon.integrable_of_forall_notMem_eq_zero (by
    intro p hp
    have ht : p.2∉Icc T (2*T) := by simpa using hp
    simp [F,a03_pair_weight_zero_outside hT f g Φ hΦ u w p.2 ht])

theorem a03_pair_compact_time_contour_fubini {T : ℝ} (hT : 0<T)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) (u w : ℕ) (R : ℝ)
    (K : ℝ×ℝ→ℂ) (hK : ContinuousOn K (Icc (-R) R ×ˢ Icc T (2*T))) :
    (∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*(∫ v in Icc (-R) R, K (v,t)))=
      ∫ v in Icc (-R) R, ∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*K (v,t) := by
  have hi := a03_pair_compact_time_contour_integrable hT f g Φ hΦ u w R K hK
  simpa only [Function.uncurry,integral_const_mul] using (integral_integral_swap (f := fun v t => rectangularMomentPairWeight T f g Φ u w t*K (v,t)) hi).symm

def a03SmallMellinCommonFactor (c T : ℝ) (σ α : MomentShifts) (n : Fin 4→ℕ)
    (p : ℝ×ℝ) : ℂ :=
  polarPoleKiller T σ ((c:ℂ)+(p.1:ℂ)*I)/((c:ℂ)+(p.1:ℂ)*I)*
    (Real.pi:ℂ)^(-2*((c:ℂ)+(p.1:ℂ)*I))*rectangularAFEOscillation p.2 n/
      ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+((c:ℂ)+(p.1:ℂ)*I))

private theorem common_factor_continuous {c : ℝ} (hc : 0<c) (T : ℝ)
    (σ α : MomentShifts) (n : Fin 4→ℕ) : Continuous (a03SmallMellinCommonFactor c T σ α n) := by
  have hz : Continuous (fun p : ℝ×ℝ => (c:ℂ)+(p.1:ℂ)*I) := by fun_prop
  have hz0 (p : ℝ×ℝ) : (c:ℂ)+(p.1:ℂ)*I≠0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith
  have hG := (polarPoleKiller_differentiable T σ).continuous.comp hz
  have hπ : Continuous (fun p : ℝ×ℝ => (Real.pi:ℂ)^(-2*((c:ℂ)+(p.1:ℂ)*I))) := by
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hosc : Continuous (fun p : ℝ×ℝ => rectangularAFEOscillation p.2 n) := by
    unfold rectangularAFEOscillation
    apply Continuous.const_cpow
    · fun_prop
    · apply Or.inl
      exact div_ne_zero (by exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 0)) (Nat.succ_ne_zero (n 1)))
        (by exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 2)) (Nat.succ_ne_zero (n 3)))
  have hden : Continuous (fun p : ℝ×ℝ => ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+((c:ℂ)+(p.1:ℂ)*I))) := by
    apply continuous_finsetProd
    intro j _
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (by exact_mod_cast Nat.succ_ne_zero (n j))
  unfold a03SmallMellinCommonFactor
  exact (((hG.div hz hz0).mul hπ).mul hosc).div hden (fun p =>
    Finset.prod_ne_zero_iff.mpr (fun j _ => Complex.natCast_add_one_cpow_ne_zero (n j) _))

private theorem main_Gamma_power_continuousOn {T : ℝ} (hT : 0<T) (c R : ℝ) :
    ContinuousOn (fun p : ℝ×ℝ => (p.2/2:ℂ)^(2*((c:ℂ)+(p.1:ℂ)*I)))
      (Icc (-R) R ×ˢ Icc T (2*T)) := by
  apply ContinuousOn.cpow (by fun_prop) (by fun_prop)
  intro p hp
  apply Complex.mem_slitPlane_iff.mpr
  left
  simp only [Complex.div_ofNat_re,Complex.ofReal_re]
  have hpt : 0<p.2 := hT.trans_le hp.2.1
  positivity

theorem rectangular_weight_replacement_Mellin_kernel_continuousOn
    {c T : ℝ} (hc : 0<c) (hT : 0<T) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (n : Fin 4→ℕ) (R : ℝ) :
    ContinuousOn (fun p : ℝ×ℝ => rectangularWeightReplacementMellinKernel
      (polarPoleKiller T σ) α p.2 n ((c:ℂ)+(p.1:ℂ)*I)) (Icc (-R) R ×ˢ Icc T (2*T)) := by
  have hh := (common_factor_continuous hc T σ α n).continuousOn.mul
    ((a03_small_positive_Gamma_quotient_joint_continuous hc α hα).continuousOn.sub
      (main_Gamma_power_continuousOn hT c R))
  convert hh using 1
  funext p
  simp only [Pi.mul_apply,Pi.sub_apply]
  unfold rectangularWeightReplacementMellinKernel a03SmallMellinCommonFactor
  ring

theorem rectangular_dual_replacement_Mellin_kernel_continuousOn
    {c T : ℝ} (hc : 0<c) (hT : 0<T) (σ τ α : MomentShifts)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (hα : ∀ j, ‖α j‖≤1/4)
    (n : Fin 4→ℕ) (R : ℝ) :
    ContinuousOn (fun p : ℝ×ℝ => rectangularDualReplacementMellinKernel T σ
      (polarPoleKiller T τ) α p.2 n ((c:ℂ)+(p.1:ℂ)*I)) (Icc (-R) R ×ˢ Icc T (2*T)) := by
  have hχ : Continuous (fun p : ℝ×ℝ => bblrDualMultiplier p.2 (rawMomentShifts T σ)) :=
    (rectangular_dual_multiplier_continuous (rawMomentShifts T σ) (fun j =>
    lt_of_le_of_lt ((Complex.abs_re_le_norm _).trans (hσ j)) (by norm_num : (1/4:ℝ)<1/2))).comp continuous_snd
  have hχlead : ContinuousOn (fun p : ℝ×ℝ =>
      (p.2/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j)) (Icc (-R) R ×ˢ Icc T (2*T)) := by
    apply ContinuousOn.cpow_const (by fun_prop)
    intro p hp
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp [Complex.div_re,Complex.mul_re,Complex.mul_im]
    have hpt : 0<p.2 := hT.trans_le hp.2.1
    positivity
  have hh := (common_factor_continuous hc T τ α n).continuousOn.mul
    ((hχ.continuousOn.mul (a03_small_positive_Gamma_quotient_joint_continuous hc α hα).continuousOn).sub
      (hχlead.mul (main_Gamma_power_continuousOn hT c R)))
  convert hh using 1
  funext p
  simp only [Pi.mul_apply,Pi.sub_apply]
  unfold rectangularDualReplacementMellinKernel a03SmallMellinCommonFactor
  ring

theorem rectangular_weight_replacement_time_contour_fubini
    {c T : ℝ} (hc : 0<c) (hT : 0<T) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (u w : ℕ) (n : Fin 4→ℕ) (R : ℝ) :
    (∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
      (∫ v in Icc (-R) R, rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)))=
    ∫ v in Icc (-R) R, ∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
      rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I) :=
  a03_pair_compact_time_contour_fubini hT f g Φ hΦ u w R _
    (rectangular_weight_replacement_Mellin_kernel_continuousOn hc hT σ α hα n R)

theorem rectangular_dual_replacement_time_contour_fubini
    {c T : ℝ} (hc : 0<c) (hT : 0<T) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (σ τ α : MomentShifts) (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (hα : ∀ j, ‖α j‖≤1/4)
    (u w : ℕ) (n : Fin 4→ℕ) (R : ℝ) :
    (∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
      (∫ v in Icc (-R) R, rectangularDualReplacementMellinKernel T σ (polarPoleKiller T τ) α t n ((c:ℂ)+(v:ℂ)*I)))=
    ∫ v in Icc (-R) R, ∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
      rectangularDualReplacementMellinKernel T σ (polarPoleKiller T τ) α t n ((c:ℂ)+(v:ℂ)*I) :=
  a03_pair_compact_time_contour_fubini hT f g Φ hΦ u w R _
    (rectangular_dual_replacement_Mellin_kernel_continuousOn hc hT σ τ α hσ hα n R)

theorem a03_compact_time_contour_integrable {T : ℝ} (W : ℝ→ℂ)
    (hW : Continuous W) (hWs : ∀ t, t∉Icc T (2*T) → W t=0) (R : ℝ)
    (K : ℝ×ℝ→ℂ) (hK : ContinuousOn K (Icc (-R) R ×ˢ Icc T (2*T))) :
    Integrable (fun p : ℝ×ℝ => W p.2*K p) ((volume.restrict (Icc (-R) R)).prod volume) := by
  let F : ℝ×ℝ→ℂ := fun p => W p.2*K p
  have hw : Continuous (fun p : ℝ×ℝ => W p.2) := hW.comp continuous_snd
  have hFc : ContinuousOn F (Icc (-R) R ×ˢ Icc T (2*T)) := hw.continuousOn.mul hK
  have hi : Integrable F ((volume.restrict (Icc (-R) R)).prod (volume.restrict (Icc T (2*T)))) := by
    rw [Measure.prod_restrict]
    exact hFc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hIon : IntegrableOn F (univ ×ˢ Icc T (2*T)) ((volume.restrict (Icc (-R) R)).prod volume) := by
    rw [IntegrableOn,← Measure.prod_restrict,Measure.restrict_univ]
    exact hi
  exact hIon.integrable_of_forall_notMem_eq_zero (by
    intro p hp
    have ht : p.2∉Icc T (2*T) := by simpa using hp
    simp [F,hWs p.2 ht])

theorem a03_compact_time_contour_time_integrable {T : ℝ} (W : ℝ→ℂ)
    (hW : Continuous W) (hWs : ∀ t, t∉Icc T (2*T) → W t=0) (R : ℝ)
    (K : ℝ×ℝ→ℂ) (hK : ContinuousOn K (Icc (-R) R ×ˢ Icc T (2*T))) :
    Integrable (fun t : ℝ => W t*(∫ v in Icc (-R) R, K (v,t))) := by
  have hi := (a03_compact_time_contour_integrable W hW hWs R K hK).integral_prod_right
  simpa only [integral_const_mul] using hi

theorem a03_compact_time_contour_fubini {T : ℝ} (W : ℝ→ℂ)
    (hW : Continuous W) (hWs : ∀ t, t∉Icc T (2*T) → W t=0) (R : ℝ)
    (K : ℝ×ℝ→ℂ) (hK : ContinuousOn K (Icc (-R) R ×ˢ Icc T (2*T))) :
    (∫ t : ℝ, W t*(∫ v in Icc (-R) R, K (v,t)))=
      ∫ v in Icc (-R) R, ∫ t : ℝ, W t*K (v,t) := by
  have hi := a03_compact_time_contour_integrable W hW hWs R K hK
  simpa only [Function.uncurry,integral_const_mul] using
    (integral_integral_swap (f := fun v t => W t*K (v,t)) hi).symm

theorem rectangular_actual_small_VStar_core_summand_Mellin (c T : ℝ)
    (σ α : MomentShifts) (t R : ℝ) (n : Fin 4→ℕ) :
    bblrGaussianVStarCoreSummand c T σ α t R n=(1/(2*Real.pi):ℂ)*
      ∫ v in Icc (-R) R, rectangularVStarAFEMellinKernel (polarPoleKiller T σ)
        α t n ((c:ℂ)+(v:ℂ)*I) := by
  unfold bblrGaussianVStarCoreSummand bblrGaussianVStarCore rectangularVStarAFEMellinKernel
  rw [integral_div,integral_const_mul]
  ring

theorem rectangular_VStar_Mellin_kernel_continuousOn
    {c T : ℝ} (hc : 0<c) (hT : 0<T) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (n : Fin 4→ℕ) (R : ℝ) :
    ContinuousOn (fun p : ℝ×ℝ => rectangularVStarAFEMellinKernel
      (polarPoleKiller T σ) α p.2 n ((c:ℂ)+(p.1:ℂ)*I)) (Icc (-R) R ×ˢ Icc T (2*T)) := by
  apply ((a03_actual_small_Mellin_kernel_joint_continuous hc T σ α hα n).continuousOn.sub
    (rectangular_weight_replacement_Mellin_kernel_continuousOn hc hT σ α hα n R)).congr
  intro p hp
  simp only [Pi.sub_apply]
  rw [rectangularWeightReplacementMellinKernel_eq_actual_sub_star _ _ (hT.trans_le hp.2.1)]
  ring

private theorem lead_time_continuousOn {T : ℝ} (hT : 0<T) (σ : MomentShifts) (R : ℝ) :
    ContinuousOn (fun p : ℝ×ℝ => bblrDualLeadingMultiplier T σ (p.2/T))
      (Icc (-R) R ×ˢ Icc T (2*T)) := by
  simp_rw [bblrDualLeadingMultiplier_time_eq hT.ne']
  apply ContinuousOn.cpow_const (by fun_prop)
  intro p hp
  apply Complex.mem_slitPlane_iff.mpr
  left
  simp [Complex.div_re,Complex.mul_re,Complex.mul_im]
  have hpt : 0<p.2 := hT.trans_le hp.2.1
  positivity

theorem rectangularFiniteSmallVStarIntegrand_integrable
    {c T : ℝ} (hc : 0<c) (hT : 1<T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (σ : MomentShifts)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (X R : ℝ) :
    Integrable (rectangularFiniteSmallVStarIntegrand c T σ f g Φ X R) := by
  have hT0 := zero_lt_one.trans hT
  have hW := rectangular_moment_weight_continuous hT a b f g Φ
    (rectangular_supported_profile_zero_above f hf) (rectangular_supported_profile_zero_above g hg) hΦ
  have hWs := rectangular_moment_weight_zero_outside hT0 f g Φ hΦ
  have hd : ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) 1 j‖≤1/4 := by
    intro j
    fin_cases j <;> simp [bblrSixShifts] <;>
      first | simpa using hσ 0 | simpa using hσ 1 | simpa using hσ 2 | simpa using hσ 3
  have hi (α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (L : ℝ→ℂ)
      (hL : ContinuousOn (fun p : ℝ×ℝ => L p.2) (Icc (-R) R ×ˢ Icc T (2*T))) :
      Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*
        (L t*rectangularFiniteSmallVStarCore c T σ α t X R)) := by
    have hin (n : Fin 4→ℕ) := a03_compact_time_contour_time_integrable _ hW hWs R _
      (hL.mul (rectangular_VStar_Mellin_kernel_continuousOn hc hT0 σ α hα n R))
    simp only [rectangularFiniteSmallVStarCore,rectangular_actual_small_VStar_core_summand_Mellin,
      Finset.mul_sum]
    apply integrable_finsetSum
    intro k _
    apply integrable_finsetSum
    intro n _
    have hh := hin n
    simp only [Pi.mul_apply,integral_const_mul] at hh
    convert hh.const_mul ((rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)) using 1
    funext t
    ring
  unfold rectangularFiniteSmallVStarIntegrand
  simp_rw [mul_add]
  apply Integrable.add
  · simpa only [one_mul] using hi _ hσ (fun _ => 1) continuous_const.continuousOn
  · exact hi _ hd _ (lead_time_continuousOn hT0 σ R)

 theorem rectangularFiniteSmallGaussianGridIntegrand_integrable
    {c T : ℝ} (hc : 0<c) (hT : 1<T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (σ : MomentShifts)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (X R : ℝ) :
    Integrable (rectangularFiniteSmallGaussianGridIntegrand c T σ f g Φ X R) := by
  have hT0 := zero_lt_one.trans hT
  have hW := rectangular_moment_weight_continuous hT a b f g Φ
    (rectangular_supported_profile_zero_above f hf) (rectangular_supported_profile_zero_above g hg) hΦ
  have hWs := rectangular_moment_weight_zero_outside hT0 f g Φ hΦ
  have hd : ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) 1 j‖≤1/4 := by
    intro j
    fin_cases j <;> simp [bblrSixShifts] <;>
      first | simpa using hσ 0 | simpa using hσ 1 | simpa using hσ 2 | simpa using hσ 3
  have hi (α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (L : ℝ→ℂ)
      (hL : ContinuousOn (fun p : ℝ×ℝ => L p.2) (Icc (-R) R ×ˢ Icc T (2*T))) :
      Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*
        (L t*rectangularFiniteSmallGaussianCore c T σ α t X R)) := by
    have hin (n : Fin 4→ℕ) := a03_compact_time_contour_time_integrable _ hW hWs R _
      (hL.mul (a03_actual_small_Mellin_kernel_joint_continuous hc T σ α hα n).continuousOn)
    simp only [rectangularFiniteSmallGaussianCore,rectangular_actual_small_Gaussian_core_summand_Mellin,
      Finset.mul_sum]
    apply integrable_finsetSum
    intro k _
    apply integrable_finsetSum
    intro n _
    have hh := hin n
    simp only [Pi.mul_apply,integral_const_mul] at hh
    convert hh.const_mul ((rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)) using 1
    funext t
    ring
  unfold rectangularFiniteSmallGaussianGridIntegrand
  simp_rw [mul_add]
  apply Integrable.add
  · simpa only [one_mul] using hi _ hσ (fun _ => 1) continuous_const.continuousOn
  · exact hi _ hd _ ((rectangular_dual_multiplier_continuous _ (fun j =>
      lt_of_le_of_lt ((Complex.abs_re_le_norm _).trans (hσ j)) (by norm_num))).comp continuous_snd).continuousOn

private theorem moment_weight_eq_pair_sum {T : ℝ} (hT : 1<T) (a b : ℝ)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (t : ℝ) :
    rectangularMomentWeight T f g Φ t=
      ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        rectangularMomentPairWeight T f g Φ u w t := by
  unfold rectangularMomentWeight
  rw [profileDirichletSum_eq_finite hT a f (rectangular_supported_profile_zero_above f hf),
    profileDirichletSum_eq_finite hT b g (rectangular_supported_profile_zero_above g hg)]
  simp only [Finset.mul_sum,Finset.sum_mul,rectangularMomentPairWeight]
  rw [Finset.sum_comm]

theorem a03_actual_finite_time_contour_fubini {T : ℝ} (hT : 1<T) (a b X R : ℝ)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (K : (Fin 4→ℕ)→(ℝ×ℝ)→ℂ)
    (hK : ∀ n, ContinuousOn (K n) (Icc (-R) R ×ˢ Icc T (2*T))) :
    (∫ t : ℝ, rectangularMomentWeight T f g Φ t*
      (∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*∫ v in Icc (-R) R, K n (v,t)))=
      (1/(2*Real.pi):ℂ)*∫ v in Icc (-R) R,
        ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
          ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
            (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
              rectangularMomentPairWeight T f g Φ u w t*K n (v,t)) := by
  have hT0 := zero_lt_one.trans hT
  have hit (u w : ℕ) (k n : Fin 4→ℕ) : Integrable (fun t : ℝ =>
      (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*
        (rectangularMomentPairWeight T f g Φ u w t*∫ v in Icc (-R) R, K n (v,t))) :=
    (a03_compact_time_contour_time_integrable _
      (rectangular_moment_pair_weight_continuous T f g Φ hΦ u w)
      (fun t ht => a03_pair_weight_zero_outside hT0 f g Φ hΦ u w t ht) R (K n) (hK n)).const_mul _
  have hiv (u w : ℕ) (k n : Fin 4→ℕ) : IntegrableOn (fun v : ℝ =>
      (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
        rectangularMomentPairWeight T f g Φ u w t*K n (v,t))) (Icc (-R) R) :=
    ((a03_pair_compact_time_contour_integrable hT0 f g Φ hΦ u w R (K n) (hK n)).integral_prod_left).const_mul _
  have he : (fun t : ℝ => rectangularMomentWeight T f g Φ t*
      (∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*∫ v in Icc (-R) R, K n (v,t)))=
      fun t : ℝ => ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
          (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*
            (rectangularMomentPairWeight T f g Φ u w t*∫ v in Icc (-R) R, K n (v,t)) := by
    funext t
    rw [moment_weight_eq_pair_sum hT a b f g Φ hf hg t]
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he,integral_finsetSum]
  · simp only [integral_finsetSum _ (fun w _ => integrable_finsetSum _ (fun k _ =>
      integrable_finsetSum _ (fun n _ => hit _ w k n))),
      integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun n _ => hit _ _ k n)),
      integral_finsetSum _ (fun n _ => hit _ _ _ n),integral_const_mul]
    rw [integral_finsetSum]
    · simp only [integral_finsetSum _ (fun w _ => integrable_finsetSum _ (fun k _ =>
        integrable_finsetSum _ (fun n _ => hiv _ w k n))),
        integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun n _ => hiv _ _ k n)),
        integral_finsetSum _ (fun n _ => hiv _ _ _ n),integral_const_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro n _
      rw [a03_pair_compact_time_contour_fubini hT0 f g Φ hΦ u w R (K n) (hK n)]
      ring
    · intro u _
      exact integrable_finsetSum _ (fun w _ => integrable_finsetSum _ (fun k _ =>
        integrable_finsetSum _ (fun n _ => hiv u w k n)))
  · intro u _
    exact integrable_finsetSum _ (fun w _ => integrable_finsetSum _ (fun k _ =>
      integrable_finsetSum _ (fun n _ => hit u w k n)))

private theorem compact_kernel_frequency_integrable {T R : ℝ}
    (K : ℝ×ℝ→ℂ) (hK : ContinuousOn K (Icc (-R) R ×ˢ Icc T (2*T)))
    {t : ℝ} (ht : t∈Icc T (2*T)) : IntegrableOn (fun v : ℝ => K (v,t)) (Icc (-R) R) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact hK.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun v hv => ⟨hv,ht⟩)

private theorem finite_replacement_time_integrable {T : ℝ} (hT : 1<T)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (X R : ℝ) (K : (Fin 4→ℕ)→(ℝ×ℝ)→ℂ)
    (hK : ∀ n, ContinuousOn (K n) (Icc (-R) R ×ˢ Icc T (2*T))) :
    Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*
      (∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*∫ v in Icc (-R) R, K n (v,t))) := by
  have hW := rectangular_moment_weight_continuous hT a b f g Φ
    (rectangular_supported_profile_zero_above f hf) (rectangular_supported_profile_zero_above g hg) hΦ
  have hWs := rectangular_moment_weight_zero_outside (zero_lt_one.trans hT) f g Φ hΦ
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro n _
  convert (a03_compact_time_contour_time_integrable _ hW hWs R (K n) (hK n)).const_mul
    ((rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)) using 1
  funext t
  ring

private theorem finite_original_small_replacement_eq {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (X R : ℝ)
    {t : ℝ} (ht : t∈Icc T (2*T)) :
    rectangularFiniteSmallGaussianCore c T σ α t X R-rectangularFiniteSmallVStarCore c T σ α t X R=
      ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*
          ∫ v in Icc (-R) R, rectangularWeightReplacementMellinKernel
            (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I) := by
  unfold rectangularFiniteSmallGaussianCore rectangularFiniteSmallVStarCore
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hga := compact_kernel_frequency_integrable (R := R) _
    (a03_actual_small_Mellin_kernel_joint_continuous hc T σ α hα n).continuousOn ht
  have hst := compact_kernel_frequency_integrable _
    (rectangular_VStar_Mellin_kernel_continuousOn hc hT σ α hα n R) ht
  simp_rw [rectangularWeightReplacementMellinKernel_eq_actual_sub_star _ _ (hT.trans_le ht.1)]
  rw [integral_sub hga hst,rectangular_actual_small_Gaussian_core_summand_Mellin,
    rectangular_actual_small_VStar_core_summand_Mellin]
  ring

private theorem finite_dual_small_replacement_eq {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (X R : ℝ)
    {t : ℝ} (ht : t∈Icc T (2*T)) :
    bblrDualMultiplier t (rawMomentShifts T σ)*rectangularFiniteSmallGaussianCore c T σ α t X R-
      bblrDualLeadingMultiplier T σ (t/T)*rectangularFiniteSmallVStarCore c T σ α t X R=
      ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*
          ∫ v in Icc (-R) R, rectangularDualReplacementMellinKernel T σ
            (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I) := by
  unfold rectangularFiniteSmallGaussianCore rectangularFiniteSmallVStarCore
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hga := compact_kernel_frequency_integrable (R := R) _
    (a03_actual_small_Mellin_kernel_joint_continuous hc T σ α hα n).continuousOn ht
  have hst := compact_kernel_frequency_integrable _
    (rectangular_VStar_Mellin_kernel_continuousOn hc hT σ α hα n R) ht
  simp_rw [rectangularDualReplacementMellinKernel_eq_actual_sub_leading_star _ _ _ _ (hT.trans_le ht.1)]
  rw [integral_sub (hga.const_mul _) (hst.const_mul _)]
  simp only [integral_const_mul,rectangular_actual_small_Gaussian_core_summand_Mellin,
    rectangular_actual_small_VStar_core_summand_Mellin,bblrDualLeadingMultiplier_time_eq hT.ne']
  ring

theorem rectangularFiniteSmallGaussianGridMoment_sub_VStar_eq_contours
    {c T : ℝ} (hc : 0<c) (hT : 1<T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (σ : MomentShifts)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (η θ : ℝ) :
    rectangularFiniteSmallGaussianGridMoment c T σ f g Φ (T^(2+η)) (θ*Real.log T)-
      rectangularFiniteSmallVStarMoment c T σ f g Φ (T^(2+η)) (θ*Real.log T)=
      a03ActualWeightReplacementFiniteContour c T a b η θ f g Φ σ (rawMomentShifts T σ)+
        a03ActualDualWeightReplacementFiniteContour c T a b η θ f g Φ σ
          (bblrSixShifts (rawMomentShifts T σ) 1) := by
  let X := T^(2+η)
  let R := θ*Real.log T
  let K₀ : (Fin 4→ℕ)→(ℝ×ℝ)→ℂ := fun n p =>
    rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) (rawMomentShifts T σ)
      p.2 n ((c:ℂ)+(p.1:ℂ)*I)
  let K₁ : (Fin 4→ℕ)→(ℝ×ℝ)→ℂ := fun n p =>
    rectangularDualReplacementMellinKernel T σ (polarPoleKiller T σ)
      (bblrSixShifts (rawMomentShifts T σ) 1) p.2 n ((c:ℂ)+(p.1:ℂ)*I)
  let E₀ : ℝ→ℂ := fun t => rectangularMomentWeight T f g Φ t*
    (∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
      (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*∫ v in Icc (-R) R, K₀ n (v,t))
  let E₁ : ℝ→ℂ := fun t => rectangularMomentWeight T f g Φ t*
    (∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
      (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*∫ v in Icc (-R) R, K₁ n (v,t))
  have hT0 := zero_lt_one.trans hT
  have hd : ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) 1 j‖≤1/4 := by
    intro j
    fin_cases j <;> simp [bblrSixShifts] <;>
      first | simpa using hσ 0 | simpa using hσ 1 | simpa using hσ 2 | simpa using hσ 3
  have hk₀ : ∀ n, ContinuousOn (K₀ n) (Icc (-R) R ×ˢ Icc T (2*T)) := fun n =>
    rectangular_weight_replacement_Mellin_kernel_continuousOn hc hT0 σ _ hσ n R
  have hk₁ : ∀ n, ContinuousOn (K₁ n) (Icc (-R) R ×ˢ Icc T (2*T)) := fun n =>
    rectangular_dual_replacement_Mellin_kernel_continuousOn hc hT0 σ σ _ hσ hd n R
  have hi₀ : Integrable E₀ := finite_replacement_time_integrable hT a b f g Φ hf hg hΦ X R K₀ hk₀
  have hi₁ : Integrable E₁ := finite_replacement_time_integrable hT a b f g Φ hf hg hΦ X R K₁ hk₁
  have he : (fun t : ℝ => rectangularFiniteSmallGaussianGridIntegrand c T σ f g Φ X R t-
      rectangularFiniteSmallVStarIntegrand c T σ f g Φ X R t)=fun t => E₀ t+E₁ t := by
    funext t
    by_cases ht : t∈Icc T (2*T)
    · have h₀ := finite_original_small_replacement_eq hc hT0 σ _ hσ X R ht
      have h₁ := finite_dual_small_replacement_eq hc hT0 σ _ hd X R ht
      dsimp [E₀,E₁,K₀,K₁]
      rw [←h₀,←h₁]
      unfold rectangularFiniteSmallGaussianGridIntegrand rectangularFiniteSmallVStarIntegrand
      ring
    · simp [rectangularFiniteSmallGaussianGridIntegrand,rectangularFiniteSmallVStarIntegrand,
        E₀,E₁,rectangular_moment_weight_zero_outside hT0 f g Φ hΦ t ht]
  unfold rectangularFiniteSmallGaussianGridMoment rectangularFiniteSmallVStarMoment
  change (∫ t : ℝ, rectangularFiniteSmallGaussianGridIntegrand c T σ f g Φ X R t)-
    (∫ t : ℝ, rectangularFiniteSmallVStarIntegrand c T σ f g Φ X R t)=_
  rw [←integral_sub
    (rectangularFiniteSmallGaussianGridIntegrand_integrable hc hT a b f g Φ hf hg hΦ σ hσ X R)
    (rectangularFiniteSmallVStarIntegrand_integrable hc hT a b f g Φ hf hg hΦ σ hσ X R),
    he,integral_add hi₀ hi₁]
  congr 1
  · simpa only [E₀,K₀,X,R,a03ActualWeightReplacementFiniteContour,
      a03ActualWeightReplacementFiniteMellinGrid,neg_mul] using
      a03_actual_finite_time_contour_fubini hT a b X R f g Φ hf hg hΦ K₀ hk₀
  · simpa only [E₁,K₁,X,R,a03ActualDualWeightReplacementFiniteContour,
      a03ActualDualWeightReplacementFiniteMellinGrid,neg_mul] using
      a03_actual_finite_time_contour_fubini hT a b X R f g Φ hf hg hΦ K₁ hk₁

end
end Sechstmoment
