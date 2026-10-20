import Sechstmoment.Numerator.U.Separation.ActualTensorMellinMeasurability
import Sechstmoment.Numerator.U.ZeroModes.LeadingFubini
import Sechstmoment.Numerator.U.ZeroModes.Linearization.Kernels
import Sechstmoment.Numerator.U.ZeroModes.Transforms.SmoothedCosineGamma

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03PhaseZeroTimeIntegrand (F : ℝ→ℂ) (P : A03SixTensorSpace→ℝ) (α : MomentShifts) (z : ℂ)
    (m n : Bool) (q : QuadraticScales) (v : Fin 5→ℕ) (x t : ℝ) : ℂ :=
  let y := a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)
  a03PhysicalZeroSmoothMask m n q v x*a03TensorMellinFactor α z y*
    (Complex.exp (((-P y:ℂ)*I)*(t:ℂ))*F t)

theorem a03PhaseZeroTimeIntegrand_joint_integrable
    (F : ℝ→ℂ) (hFm : Measurable F) (hFi : Integrable F)
    (P : A03SixTensorSpace→ℝ) (hPm : Measurable P) {α : MomentShifts} (hα : ∀ j,‖α j‖≤1/4) {z : ℂ} (hz : 0≤z.re)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    Integrable (Function.uncurry (a03PhaseZeroTimeIntegrand F P α z m n q v))
      ((volume.restrict (Ioi 0)).prod volume) := by
  obtain ⟨L,_hL,hzero⟩ := a03PhysicalZeroSmoothMask_compact_band m n q hM₂ v hv
  let W : ℝ→ℝ := (Icc 0 L).indicator (fun _ => (1:ℝ))
  have hiW : Integrable W (volume.restrict (Ioi 0)) :=
    ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (measure_Icc_lt_top.ne))).restrict
  have hy : Measurable (fun x => a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)) :=
    a03SixTensorLogPoint_measurable.comp (a03SixZeroSourceArguments_continuous m n q v).measurable
  have hgap : Measurable (fun x => P (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) :=
    hPm.comp hy
  have hm : AEStronglyMeasurable
      (Function.uncurry (a03PhaseZeroTimeIntegrand F P α z m n q v))
      ((volume.restrict (Ioi 0)).prod volume) := by
    unfold a03PhaseZeroTimeIntegrand Function.uncurry
    convert (((a03PhysicalZeroSmoothMask_continuous m n q v).measurable.comp measurable_fst).mul
      (((a03TensorMellinFactor_contDiff α z).continuous.measurable.comp hy).comp measurable_fst) |>.mul
        ((((((Complex.continuous_ofReal.measurable.comp (hgap.neg.comp measurable_fst))).mul_const I).mul (Complex.continuous_ofReal.measurable.comp measurable_snd)).cexp).mul
          (hFm.comp measurable_snd))).aestronglyMeasurable using 1
    funext p
    simp only [Pi.mul_apply,Pi.neg_apply,Function.comp_apply,Complex.ofReal_neg]
  apply (hiW.mul_prod hFi.norm).mono' hm
  apply ae_of_all
  intro p
  by_cases hx : p.1∈Icc 0 L
  · simp only [W,indicator_of_mem hx,one_mul]
    unfold Function.uncurry a03PhaseZeroTimeIntegrand
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_exp]
    have hreal : (((-P (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v p.1)):ℂ)*I)*(p.2:ℂ)).re=0 := by
      simp
    rw [hreal,Real.exp_zero,one_mul]
    rw [←norm_mul]
    exact mul_le_mul_of_nonneg_right (a03PhysicalZeroSmoothMask_tensor_norm_le_one hα hz m n q v p.1)
      (norm_nonneg _)|>.trans_eq (one_mul _)
  · simp only [W,indicator_of_notMem hx,zero_mul]
    unfold Function.uncurry a03PhaseZeroTimeIntegrand
    simp only [hzero p.1 hx,zero_mul,norm_zero,le_refl]

theorem a03PhaseZeroTimeIntegrand_fubini
    (F : ℝ→ℂ) (hFm : Measurable F) (hFi : Integrable F)
    (P : A03SixTensorSpace→ℝ) (hPm : Measurable P) {α : MomentShifts} (hα : ∀ j,‖α j‖≤1/4) {z : ℂ} (hz : 0≤z.re)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    (∫ x : ℝ in Ioi 0,∫ t : ℝ,a03PhaseZeroTimeIntegrand F P α z m n q v x t)=
      ∫ t : ℝ,∫ x : ℝ in Ioi 0,a03PhaseZeroTimeIntegrand F P α z m n q v x t :=
  integral_integral_swap (a03PhaseZeroTimeIntegrand_joint_integrable F hFm hFi P hPm hα hz m n q hM₂ v hv)


def a03PhasePhysicalZeroTimeMode (F : ℝ→ℂ) (P : A03SixTensorSpace→ℝ) (α : MomentShifts) (z : ℂ)
    (m n : Bool) (q : QuadraticScales) (a b : ℕ→ℂ) (t : ℝ) : ℂ :=
  ∑ v∈quadraticMainIndexSet q,a (v 0)*b (v 1)*
    ∫ x : ℝ in Ioi 0,a03PhaseZeroTimeIntegrand F P α z m n q v x t

theorem a03PhasePhysicalZeroTimeMode_integrable_eq
    (F : ℝ→ℂ) (hFm : Measurable F) (hFi : Integrable F)
    (P : A03SixTensorSpace→ℝ) (hPm : Measurable P) {α : MomentShifts} (hα : ∀ j,‖α j‖≤1/4) {z : ℂ} (hz : 0≤z.re)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂) (a b : ℕ→ℂ) :
    Integrable (a03PhasePhysicalZeroTimeMode F P α z m n q a b) ∧
    a03SixTensorPhysicalZeroMode (fun y => a03TensorMellinFactor α z y*
      profileLaplaceTransform F (((-P y):ℂ)*I))
      m n q a b=∫ t : ℝ,a03PhasePhysicalZeroTimeMode F P α z m n q a b t := by
  have hj (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) :=
    a03PhaseZeroTimeIntegrand_joint_integrable F hFm hFi P hPm hα hz m n q hM₂ v
      (fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv j)).1)
  have hi (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) :
      Integrable (fun t : ℝ => a (v 0)*b (v 1)*
        ∫ x : ℝ in Ioi 0,a03PhaseZeroTimeIntegrand F P α z m n q v x t) :=
    (hj v hv).integral_prod_right.const_mul _
  refine ⟨integrable_finsetSum _ hi,?_⟩
  unfold a03PhasePhysicalZeroTimeMode
  rw [integral_finsetSum _ hi]
  unfold a03SixTensorPhysicalZeroMode
  apply Finset.sum_congr rfl
  intro v hv
  rw [integral_const_mul]
  congr 1
  rw [←integral_integral_swap (hj v hv)]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold a03PhaseZeroTimeIntegrand profileLaplaceTransform a03PhysicalZeroSmoothMask
  simp only [integral_const_mul]
  ring



def a03LinearZeroGap (p : A03NearTensorData) (y : A03SixTensorSpace) : ℝ :=
  p.T*p.s*p.r*Real.exp (a03SixGapLinear y)

theorem a03LinearZeroGap_continuous (p : A03NearTensorData) : Continuous (a03LinearZeroGap p) := by
  unfold a03LinearZeroGap
  fun_prop

theorem a03LeadingLinearTensorRawKernel_physical_time_reconstruction
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c : ℝ} (hc : 0≤c) (p : A03NearTensorData) (hT : 0<p.T)
    (hα : ∀ j,‖p.α j‖≤1/4) (m n : Bool) (q : QuadraticScales)
    (hM₂ : 0<q.M₂) (a b : ℕ→ℂ) :
    Integrable (a03PhasePhysicalZeroTimeMode
      (a03GaussianLeadingTimeProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I))
      (a03LinearZeroGap p) p.α ((c:ℂ)+(p.v:ℂ)*I) m n q a b) ∧
    a03SixTensorPhysicalZeroMode (a03LeadingLinearTensorRawKernel Φ c p) m n q a b=
      ∫ t : ℝ,a03PhasePhysicalZeroTimeMode
        (a03GaussianLeadingTimeProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I))
        (a03LinearZeroGap p) p.α ((c:ℂ)+(p.v:ℂ)*I) m n q a b t := by
  have hf := a03GaussianLeadingTimeProfile_continuous hΦ hs hT p.σ p.α ((c:ℂ)+(p.v:ℂ)*I)
  have hi := a03GaussianLeadingTimeProfile_integrable hΦ hs hT p.σ p.α ((c:ℂ)+(p.v:ℂ)*I)
  have he : a03LeadingLinearTensorRawKernel Φ c p=(fun y =>
      a03TensorMellinFactor p.α ((c:ℂ)+(p.v:ℂ)*I) y*
        profileLaplaceTransform (a03GaussianLeadingTimeProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I))
          (((-a03LinearZeroGap p y):ℂ)*I)) := by
    funext y
    simp [a03LeadingLinearTensorRawKernel,a03GaussianLeadingFrequencyProfile,a03LinearZeroGap]
  rw [he]
  exact a03PhasePhysicalZeroTimeMode_integrable_eq _ hf.measurable hi (a03LinearZeroGap p)
    (a03LinearZeroGap_continuous p).measurable hα (z := ((c:ℂ)+(p.v:ℂ)*I))
    (by simpa using hc) m n q hM₂ a b

theorem a03LeadingLinearDualTensorRawKernel_physical_time_reconstruction
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c : ℝ} (hc : 0≤c) (p : A03NearTensorData) (hT : 0<p.T)
    (hα : ∀ j,‖p.α j‖≤1/4) (m n : Bool) (q : QuadraticScales)
    (hM₂ : 0<q.M₂) (a b : ℕ→ℂ) :
    Integrable (a03PhasePhysicalZeroTimeMode
      (a03GaussianDualLeadingTimeProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I))
      (a03LinearZeroGap p) p.α ((c:ℂ)+(p.v:ℂ)*I) m n q a b) ∧
    a03SixTensorPhysicalZeroMode (a03LeadingLinearDualTensorRawKernel Φ c p) m n q a b=
      ∫ t : ℝ,a03PhasePhysicalZeroTimeMode
        (a03GaussianDualLeadingTimeProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I))
        (a03LinearZeroGap p) p.α ((c:ℂ)+(p.v:ℂ)*I) m n q a b t :=
  a03LeadingLinearTensorRawKernel_physical_time_reconstruction
    (a03DualLeadingSupportedProfile_continuous hΦ hs hT p.σ)
    ((a03_profile_product_tsupport _ _).trans hs) hc p hT hα m n q hM₂ a b


theorem a03PhaseLaplaceTensor_physical_term_integrable
    (F : ℝ→ℂ) (hFm : Measurable F) (hFi : Integrable F)
    (P : A03SixTensorSpace→ℝ) (hPm : Measurable P)
    {α : MomentShifts} (hα : ∀ j,‖α j‖≤1/4) {z : ℂ} (hz : 0≤z.re)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
      (a03TensorMellinFactor α z (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))*
        profileLaplaceTransform F (((-P (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))):ℂ)*I))) (Ioi 0) := by
  have hj := a03PhaseZeroTimeIntegrand_joint_integrable F hFm hFi P hPm hα hz m n q hM₂ v hv
  apply hj.integral_prod_left.congr
  apply ae_of_all
  intro x
  unfold Function.uncurry a03PhaseZeroTimeIntegrand profileLaplaceTransform
  simp only [integral_const_mul]
  ring

theorem a03LeadingLinearTensorRawKernel_physical_term_integrable
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c : ℝ} (hc : 0≤c) (p : A03NearTensorData) (hT : 0<p.T)
    (hα : ∀ j,‖p.α j‖≤1/4) (m n : Bool) (q : QuadraticScales)
    (hM₂ : 0<q.M₂) (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
      a03LeadingLinearTensorRawKernel Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) (Ioi 0) := by
  let z : ℂ := (c:ℂ)+(p.v:ℂ)*I
  have hFm := (a03GaussianLeadingTimeProfile_continuous hΦ hs hT p.σ p.α z).measurable
  have hFi := a03GaussianLeadingTimeProfile_integrable hΦ hs hT p.σ p.α z
  have hi := a03PhaseLaplaceTensor_physical_term_integrable _ hFm hFi (a03LinearZeroGap p)
    (a03LinearZeroGap_continuous p).measurable hα (z := z) (by simpa [z] using hc) m n q hM₂ v hv
  convert hi using 1
  funext x
  simp [a03LeadingLinearTensorRawKernel,a03GaussianLeadingFrequencyProfile,a03LinearZeroGap,z]

theorem a03LeadingLinearDualTensorRawKernel_physical_term_integrable
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c : ℝ} (hc : 0≤c) (p : A03NearTensorData) (hT : 0<p.T)
    (hα : ∀ j,‖p.α j‖≤1/4) (m n : Bool) (q : QuadraticScales)
    (hM₂ : 0<q.M₂) (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
      a03LeadingLinearDualTensorRawKernel Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) (Ioi 0) :=
  a03LeadingLinearTensorRawKernel_physical_term_integrable
    (a03DualLeadingSupportedProfile_continuous hΦ hs hT p.σ)
    ((a03_profile_product_tsupport _ _).trans hs) hc p hT hα m n q hM₂ v hv

end
end Sechstmoment
