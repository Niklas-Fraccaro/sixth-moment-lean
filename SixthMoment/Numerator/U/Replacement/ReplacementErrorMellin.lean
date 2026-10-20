import SixthMoment.Numerator.U.Replacement.DualErrorPartsContour
import SixthMoment.Numerator.U.Replacement.ReplacementErrorDefinitions
import SixthMoment.Numerator.U.Replacement.ReplacementMomentMellin

namespace SixthMoment
open Complex Source Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

private theorem dual_weight_kernel_eq (T : ℝ) (σ : MomentShifts)
    (G : ℂ→ℂ) (α : MomentShifts) (t : ℝ) (n : Fin 4→ℕ) (z : ℂ) :
    rectangularDualErrorPartMellinKernel false T σ G α t n z=
      bblrDualMultiplier t (rawMomentShifts T σ)*rectangularWeightReplacementMellinKernel G α t n z := by
  simp only [rectangularDualErrorPartMellinKernel,rectangularWeightReplacementMellinKernel,
    Bool.false_eq_true,ite_false]
  ring

private theorem dual_phase_kernel_eq {T t : ℝ} (hT : T≠0) (ht : 0<t)
    (σ : MomentShifts) (G : ℂ→ℂ) (α : MomentShifts) (n : Fin 4→ℕ) (z : ℂ) :
    rectangularDualErrorPartMellinKernel true T σ G α t n z=
      (bblrDualMultiplier t (rawMomentShifts T σ)-bblrDualLeadingMultiplier T σ (t/T))*
        rectangularVStarAFEMellinKernel G α t n z := by
  rw [rectangularVStarAFEMellinKernel_eq_main_power G α ht,
    bblrDualLeadingMultiplier_time_eq hT]
  simp only [rectangularDualErrorPartMellinKernel,ite_true]
  ring

theorem rectangular_dual_error_part_Mellin_kernel_continuousOn (phasePart : Bool)
    {c T : ℝ} (hc : 0<c) (hT : 0<T) (σ α : MomentShifts)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (hα : ∀ j, ‖α j‖≤1/4)
    (n : Fin 4→ℕ) (R : ℝ) :
    ContinuousOn (fun p : ℝ×ℝ => rectangularDualErrorPartMellinKernel phasePart T σ
      (polarPoleKiller T σ) α p.2 n ((c:ℂ)+(p.1:ℂ)*I)) (Icc (-R) R ×ˢ Icc T (2*T)) := by
  have hχ : Continuous (fun p : ℝ×ℝ => bblrDualMultiplier p.2 (rawMomentShifts T σ)) :=
    (rectangular_dual_multiplier_continuous _ (fun j =>
      lt_of_le_of_lt ((Complex.abs_re_le_norm _).trans (hσ j)) (by norm_num))).comp continuous_snd
  cases phasePart
  · apply (hχ.continuousOn.mul
      (rectangular_weight_replacement_Mellin_kernel_continuousOn hc hT σ α hα n R)).congr
    intro p _
    simp only [Pi.mul_apply]
    exact dual_weight_kernel_eq T σ _ α p.2 n _
  · have hlead : ContinuousOn (fun p : ℝ×ℝ => bblrDualLeadingMultiplier T σ (p.2/T))
        (Icc (-R) R ×ˢ Icc T (2*T)) := by
      simp_rw [bblrDualLeadingMultiplier_time_eq hT.ne']
      apply ContinuousOn.cpow_const (by fun_prop)
      intro p hp
      apply Complex.mem_slitPlane_iff.mpr
      left
      simp [Complex.div_re,Complex.mul_re,Complex.mul_im]
      have hpt : 0<p.2 := hT.trans_le hp.2.1
      positivity
    apply ((hχ.continuousOn.sub hlead).mul
      (rectangular_VStar_Mellin_kernel_continuousOn hc hT σ α hα n R)).congr
    intro p hp
    simp only [Pi.mul_apply,Pi.sub_apply]
    exact dual_phase_kernel_eq hT.ne' (hT.trans_le hp.2.1) σ _ α n _

private theorem compact_kernel_frequency_integrable {T R : ℝ}
    (K : ℝ×ℝ→ℂ) (hK : ContinuousOn K (Icc (-R) R ×ˢ Icc T (2*T)))
    {t : ℝ} (ht : t∈Icc T (2*T)) : IntegrableOn (fun v : ℝ => K (v,t)) (Icc (-R) R) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact hK.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun v hv => ⟨hv,ht⟩)

private theorem finite_original_replacement_eq {c T : ℝ} (hc : 0<c) (hT : 0<T)
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

private theorem finite_dual_part_eq (phasePart : Bool) {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (X R : ℝ)
    {t : ℝ} (ht : t∈Icc T (2*T)) :
    (if phasePart then (bblrDualMultiplier t (rawMomentShifts T σ)-bblrDualLeadingMultiplier T σ (t/T))*
      rectangularFiniteSmallVStarCore c T σ α t X R
    else bblrDualMultiplier t (rawMomentShifts T σ)*
      (rectangularFiniteSmallGaussianCore c T σ α t X R-rectangularFiniteSmallVStarCore c T σ α t X R))=
      ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*
          ∫ v in Icc (-R) R, rectangularDualErrorPartMellinKernel phasePart T σ
            (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I) := by
  cases phasePart
  · simp only [Bool.false_eq_true,ite_false]
    rw [finite_original_replacement_eq hc hT σ α hα X R ht]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro n _
    simp only [dual_weight_kernel_eq,integral_const_mul]
    ring
  · simp only [ite_true,rectangularFiniteSmallVStarCore,Finset.mul_sum,
      rectangular_actual_small_VStar_core_summand_Mellin]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro n _
    simp only [dual_phase_kernel_eq hT.ne' (hT.trans_le ht.1),integral_const_mul]
    ring

theorem rectangularFiniteOriginalWeightReplacementError_eq_contour
    {c T : ℝ} (hc : 0<c) (hT : 1<T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (σ : MomentShifts)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (η θ : ℝ) :
    rectangularFiniteOriginalWeightReplacementError c T σ f g Φ (T^(2+η)) (θ*Real.log T)=
      a03ActualWeightReplacementFiniteContour c T a b η θ f g Φ σ (rawMomentShifts T σ) := by
  let X := T^(2+η)
  let R := θ*Real.log T
  let K : (Fin 4→ℕ)→(ℝ×ℝ)→ℂ := fun n p => rectangularWeightReplacementMellinKernel
    (polarPoleKiller T σ) (rawMomentShifts T σ) p.2 n ((c:ℂ)+(p.1:ℂ)*I)
  have hT0 := zero_lt_one.trans hT
  have hK : ∀ n, ContinuousOn (K n) (Icc (-R) R ×ˢ Icc T (2*T)) := fun n =>
    rectangular_weight_replacement_Mellin_kernel_continuousOn hc hT0 σ _ hσ n R
  have he : rectangularFiniteOriginalWeightReplacementIntegrand c T σ f g Φ X R=
      fun t => rectangularMomentWeight T f g Φ t*
        (∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
          (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*∫ v in Icc (-R) R, K n (v,t)) := by
    funext t
    by_cases ht : t∈Icc T (2*T)
    · unfold rectangularFiniteOriginalWeightReplacementIntegrand
      rw [finite_original_replacement_eq hc hT0 σ _ hσ X R ht]
    · simp [rectangularFiniteOriginalWeightReplacementIntegrand,
        rectangular_moment_weight_zero_outside hT0 f g Φ hΦ t ht]
  unfold rectangularFiniteOriginalWeightReplacementError
  change (∫ t : ℝ, rectangularFiniteOriginalWeightReplacementIntegrand c T σ f g Φ X R t)=_
  rw [he]
  simpa only [K,X,R,a03ActualWeightReplacementFiniteContour,
    a03ActualWeightReplacementFiniteMellinGrid,neg_mul] using
    a03_actual_finite_time_contour_fubini hT a b X R f g Φ hf hg hΦ K hK

private theorem finite_dual_part_error_eq_contour (phasePart : Bool)
    {c T : ℝ} (hc : 0<c) (hT : 1<T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (σ : MomentShifts)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (η θ : ℝ) :
    (if phasePart then rectangularFiniteDualPhaseReplacementError c T σ f g Φ (T^(2+η)) (θ*Real.log T)
      else rectangularFiniteDualWeightReplacementError c T σ f g Φ (T^(2+η)) (θ*Real.log T))=
      a03ActualDualErrorPartFiniteContour phasePart c T a b η θ f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) 1) := by
  let X := T^(2+η)
  let R := θ*Real.log T
  let K : (Fin 4→ℕ)→(ℝ×ℝ)→ℂ := fun n p => rectangularDualErrorPartMellinKernel phasePart T σ
    (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) 1) p.2 n ((c:ℂ)+(p.1:ℂ)*I)
  have hT0 := zero_lt_one.trans hT
  have hd : ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) 1 j‖≤1/4 := by
    intro j
    fin_cases j <;> simp [bblrSixShifts] <;>
      first | simpa using hσ 0 | simpa using hσ 1 | simpa using hσ 2 | simpa using hσ 3
  have hK : ∀ n, ContinuousOn (K n) (Icc (-R) R ×ˢ Icc T (2*T)) := fun n =>
    rectangular_dual_error_part_Mellin_kernel_continuousOn phasePart hc hT0 σ _ hσ hd n R
  let E : ℝ→ℂ := fun t => if phasePart then
    rectangularFiniteDualPhaseReplacementIntegrand c T σ f g Φ X R t
    else rectangularFiniteDualWeightReplacementIntegrand c T σ f g Φ X R t
  have he : E=fun t => rectangularMomentWeight T f g Φ t*
      (∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        (rectangularAFESmoothWeight k n:ℂ)*(1/(2*Real.pi):ℂ)*∫ v in Icc (-R) R, K n (v,t)) := by
    funext t
    by_cases ht : t∈Icc T (2*T)
    · have hh := finite_dual_part_eq phasePart hc hT0 σ _ hd X R ht
      cases phasePart <;> simp only [E,Bool.false_eq_true,ite_false,ite_true,
        rectangularFiniteDualPhaseReplacementIntegrand,rectangularFiniteDualWeightReplacementIntegrand,
        mul_assoc] at * <;> rw [hh]
    · cases phasePart <;> simp [E,rectangularFiniteDualPhaseReplacementIntegrand,
        rectangularFiniteDualWeightReplacementIntegrand,
        rectangular_moment_weight_zero_outside hT0 f g Φ hΦ t ht]
  have hleft : (if phasePart then rectangularFiniteDualPhaseReplacementError c T σ f g Φ X R
      else rectangularFiniteDualWeightReplacementError c T σ f g Φ X R)=∫ t : ℝ, E t := by
    cases phasePart <;> rfl
  change (if phasePart then rectangularFiniteDualPhaseReplacementError c T σ f g Φ X R
      else rectangularFiniteDualWeightReplacementError c T σ f g Φ X R)=_
  rw [hleft,he]
  simpa only [K,X,R,a03ActualDualErrorPartFiniteContour,
    a03ActualDualErrorPartFiniteMellinGrid,neg_mul] using
    a03_actual_finite_time_contour_fubini hT a b X R f g Φ hf hg hΦ K hK

theorem rectangularFiniteDualWeightReplacementError_eq_contour
    {c T : ℝ} (hc : 0<c) (hT : 1<T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (σ : MomentShifts)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (η θ : ℝ) :
    rectangularFiniteDualWeightReplacementError c T σ f g Φ (T^(2+η)) (θ*Real.log T)=
      a03ActualDualErrorPartFiniteContour false c T a b η θ f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) 1) := by
  simpa only [Bool.false_eq_true,ite_false] using
    finite_dual_part_error_eq_contour false hc hT a b f g Φ hf hg hΦ σ hσ η θ

theorem rectangularFiniteDualPhaseReplacementError_eq_contour
    {c T : ℝ} (hc : 0<c) (hT : 1<T) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (σ : MomentShifts)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4) (η θ : ℝ) :
    rectangularFiniteDualPhaseReplacementError c T σ f g Φ (T^(2+η)) (θ*Real.log T)=
      a03ActualDualErrorPartFiniteContour true c T a b η θ f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) 1) := by
  simpa only [ite_true] using
    finite_dual_part_error_eq_contour true hc hT a b f g Φ hf hg hΦ σ hσ η θ

end
end SixthMoment
