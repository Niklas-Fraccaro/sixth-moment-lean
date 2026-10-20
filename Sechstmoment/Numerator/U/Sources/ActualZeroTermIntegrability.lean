import Sechstmoment.Numerator.U.ZeroModes.LeadingFubini

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

theorem a03LaplaceTensor_physical_term_integrable
    (F : ℝ→ℂ) (hFm : Measurable F) (hFi : Integrable F)
    (T r s : ℝ) {α : MomentShifts} (hα : ∀ j,‖α j‖≤1/4) {z : ℂ} (hz : 0≤z.re)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
      (a03TensorMellinFactor α z (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))*
        profileLaplaceTransform F (((-a03RealLogGapSymbol T r s
          (a03SixGapLinear (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))):ℂ)*I))) (Ioi 0) := by
  have hj := a03LeadingZeroTimeIntegrand_joint_integrable F hFm hFi T r s hα hz m n q hM₂ v hv
  apply hj.integral_prod_left.congr
  apply ae_of_all
  intro x
  unfold Function.uncurry a03LeadingZeroTimeIntegrand profileLaplaceTransform
  simp only [integral_const_mul]
  ring

theorem a03ActualTensorRawKernel_physical_term_integrable
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c : ℝ} (hc : 0≤c) (p : A03NearTensorData) (hT : 10≤p.T)
    (hα : ∀ j,‖p.α j‖≤1/4)
    (hlarge : 192*(‖(c:ℂ)+(p.v:ℂ)*I‖+‖(c:ℂ)+(p.v:ℂ)*I‖^2)<p.T)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
      a03ActualTensorRawKernel Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) (Ioi 0) := by
  let z : ℂ := (c:ℂ)+(p.v:ℂ)*I
  have hFc := a03_gaussian_time_profile_contDiff hΦ hs (by norm_num : (0:ℝ)≤1/4)
    (by norm_num;exact hT) p.σ p.α hα hlarge
  have hFK : HasCompactSupport (a03GaussianTimeProfile Φ p.T p.σ p.α z) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) ((a03_gaussian_time_profile_tsupport _ _ _ _ _).trans hs)
  have he : a03ActualTensorRawKernel Φ c p=(fun y => a03TensorMellinFactor p.α z y*
      profileLaplaceTransform (a03GaussianTimeProfile Φ p.T p.σ p.α z)
        (((-a03RealLogGapSymbol p.T p.r p.s (a03SixGapLinear y)):ℂ)*I)) := by
    funext y
    simp [a03ActualTensorRawKernel,a03SixGaussianFrequencyKernel,a03GaussianFrequencyProfile,z]
  rw [he]
  exact a03LaplaceTensor_physical_term_integrable _ hFc.continuous.measurable
    (hFc.continuous.integrable_of_hasCompactSupport hFK) p.T p.r p.s hα
    (z := z) (by simpa [z] using hc) m n q hM₂ v hv

theorem a03ActualDualTensorRawKernel_physical_term_integrable
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c : ℝ} (hc : 0≤c) (p : A03NearTensorData) (hT : 10≤p.T)
    (hα : ∀ j,‖p.α j‖≤1/4) (hσ : ∀ j,‖rawMomentShifts p.T p.σ j‖≤1/4)
    (hlarge : 192*(‖(c:ℂ)+(p.v:ℂ)*I‖+‖(c:ℂ)+(p.v:ℂ)*I‖^2)<p.T)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
      a03ActualDualTensorRawKernel Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) (Ioi 0) := by
  let z : ℂ := (c:ℂ)+(p.v:ℂ)*I
  let D : ℝ→ℂ := fun x => bblrDualMultiplier (p.T*x) (rawMomentShifts p.T p.σ)
  have hD : Continuous D := (rectangular_dual_multiplier_continuous _ (fun j =>
    ((Complex.abs_re_le_norm _).trans (hσ j)).trans_lt (by norm_num))).comp (by fun_prop)
  have hPD : Continuous (a03ProfileProduct Φ D) := hΦ.continuous.mul hD
  have hPDs : tsupport (a03ProfileProduct Φ D)⊆Icc (1:ℝ) 2 :=
    (a03_profile_product_tsupport _ _).trans hs
  have hFc : Continuous (a03GaussianDualTimeProfile Φ p.T p.σ p.α z) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x∈tsupport (a03ProfileProduct Φ D)
    · exact hPD.continuousAt.mul
        ((bblrGaussianTimeAmplitude_contDiffAt (by norm_num : (0:ℝ)≤1/4)
          (by norm_num;exact hT) p.σ p.α hα hlarge (hPDs hx)).continuousAt)
    · have he : a03GaussianDualTimeProfile Φ p.T p.σ p.α z=ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport (a03ProfileProduct Φ D)).isOpen_compl.mem_nhds hx] with y hy
        have hz : a03ProfileProduct Φ D y=0 := Function.notMem_support.mp (fun hh => hy (subset_tsupport _ hh))
        change a03ProfileProduct Φ D y*bblrGaussianTimeAmplitude p.T p.σ p.α z y=0
        rw [hz,zero_mul]
      exact continuousAt_const.congr_of_eventuallyEq he
  have hFK : HasCompactSupport (a03GaussianDualTimeProfile Φ p.T p.σ p.α z) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) ((a03_gaussian_dual_time_profile_tsupport _ _ _ _ _).trans hs)
  have he : a03ActualDualTensorRawKernel Φ c p=(fun y => a03TensorMellinFactor p.α z y*
      profileLaplaceTransform (a03GaussianDualTimeProfile Φ p.T p.σ p.α z)
        (((-a03RealLogGapSymbol p.T p.r p.s (a03SixGapLinear y)):ℂ)*I)) := by
    funext y
    simp [a03ActualDualTensorRawKernel,a03SixGaussianDualFrequencyKernel,a03GaussianDualFrequencyProfile,z]
  rw [he]
  exact a03LaplaceTensor_physical_term_integrable _ hFc.measurable
    (hFc.integrable_of_hasCompactSupport hFK) p.T p.r p.s hα
    (z := z) (by simpa [z] using hc) m n q hM₂ v hv

end
end Sechstmoment
