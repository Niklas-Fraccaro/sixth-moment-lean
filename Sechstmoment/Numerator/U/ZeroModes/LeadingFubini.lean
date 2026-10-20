import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Sechstmoment.Numerator.U.ZeroModes.Replacement.Kernels

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

private theorem leadingLogPoint_measurable : Measurable a03SixTensorLogPoint :=
  (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun j =>
    Real.measurable_log.comp (measurable_pi_apply j))

private theorem leadingSourceArguments_continuous (m n : Bool) (q : QuadraticScales)
    (v : Fin 5→ℕ) : Continuous (a03SixZeroSourceArguments m n q v) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact continuous_const
  · cases m <;> cases n <;> fin_cases i <;>
      simp [a03SixZeroSourceArguments,a03SixZeroPairArguments] <;>
      exact rectangularZeroArguments_continuous q v _

private theorem leadingGapSymbol_measurable (T r s : ℝ) : Measurable (a03RealLogGapSymbol T r s) := by
  unfold a03RealLogGapSymbol
  fun_prop

def a03PhysicalZeroSmoothMask (m n : Bool) (q : QuadraticScales) (v : Fin 5→ℕ) (x : ℝ) : ℂ :=
  ∏ j : Fin 5,(rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q v x j.succ):ℂ)

theorem a03PhysicalZeroSmoothMask_eq (m n : Bool) (q : QuadraticScales) (v : Fin 5→ℕ) (x : ℝ) :
    a03PhysicalZeroSmoothMask m n q v x=
      ∏ j : Fin 5,(rectangularSmoothBlockWeight (rectangularZeroArguments q v x j):ℂ) := by
  cases m <;> cases n <;>
    simp [a03PhysicalZeroSmoothMask,a03SixZeroSourceArguments,a03SixZeroPairArguments,Fin.prod_univ_five,
      mul_comm,mul_left_comm,mul_assoc]

theorem a03PhysicalZeroSmoothMask_continuous (m n : Bool) (q : QuadraticScales) (v : Fin 5→ℕ) :
    Continuous (a03PhysicalZeroSmoothMask m n q v) := by
  unfold a03PhysicalZeroSmoothMask
  apply continuous_finsetProd
  intro j _
  exact Complex.continuous_ofReal.comp (rectangularSmoothBlockWeight_contDiff.continuous.comp
    ((continuous_apply j.succ).comp (leadingSourceArguments_continuous m n q v)))

theorem a03PhysicalZeroSmoothMask_norm_le_one (m n : Bool) (q : QuadraticScales) (v : Fin 5→ℕ) (x : ℝ) :
    ‖a03PhysicalZeroSmoothMask m n q v x‖≤1 := by
  unfold a03PhysicalZeroSmoothMask
  rw [norm_prod]
  calc
    _≤∏ _j : Fin 5,(1:ℝ) := Finset.prod_le_prod₀
      (fun _ _ => norm_nonneg _) (fun j _ => by
        simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (rectangularSmoothBlockWeight_nonneg _)]
        exact rectangularSmoothBlockWeight_le_one _)
    _=1 := Finset.prod_const_one

theorem a03PhysicalZeroSmoothMask_quad_support (m n : Bool) (q : QuadraticScales)
    (v : Fin 5→ℕ) (x : ℝ) (hw : a03PhysicalZeroSmoothMask m n q v x≠0) :
    ∀ j : Fin 4,a03SixZeroSourceArguments m n q v x j.succ.succ∈Icc (1:ℝ) 2 := by
  intro j
  have hz : rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q v x j.succ.succ)≠0 := by
    intro he
    apply hw
    unfold a03PhysicalZeroSmoothMask
    exact Finset.prod_eq_zero (Finset.mem_univ j.succ) (by simp [he])
  exact rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hz)

theorem a03TensorMellinFactor_nonpositive_log_norm_le_one
    {α : MomentShifts} (hα : ∀ j,‖α j‖≤1/4) {z : ℂ} (hz : 0≤z.re)
    (y : A03SixTensorSpace) (hy : ∀ j : Fin 4,0≤y j.succ.succ) :
    ‖a03TensorMellinFactor α z y‖≤1 := by
  rw [a03TensorMellinFactor_eq_exp,Complex.norm_exp,←Real.exp_zero]
  apply Real.exp_le_exp.mpr
  rw [Complex.re_sum]
  apply Finset.sum_nonpos
  intro j _
  have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
  simp only [Complex.mul_re,Complex.neg_re,Complex.add_re,Complex.div_ofNat_re,
    Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hy j)

theorem a03PhysicalZeroSmoothMask_tensor_norm_le_one
    {α : MomentShifts} (hα : ∀ j,‖α j‖≤1/4) {z : ℂ} (hz : 0≤z.re)
    (m n : Bool) (q : QuadraticScales) (v : Fin 5→ℕ) (x : ℝ) :
    ‖a03PhysicalZeroSmoothMask m n q v x*
      a03TensorMellinFactor α z (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))‖≤1 := by
  by_cases hw : a03PhysicalZeroSmoothMask m n q v x=0
  · simp [hw]
  · rw [norm_mul]
    apply (mul_le_mul (a03PhysicalZeroSmoothMask_norm_le_one m n q v x)
      (a03TensorMellinFactor_nonpositive_log_norm_le_one hα hz _ ?_)
      (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)
    intro j
    exact Real.log_nonneg (a03PhysicalZeroSmoothMask_quad_support m n q v x hw j).1

theorem a03PhysicalZeroSmoothMask_compact_band (m n : Bool) (q : QuadraticScales)
    (hM₂ : 0<q.M₂) (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    ∃ L : ℝ,0<L ∧ ∀ x : ℝ,x∉Icc 0 L → a03PhysicalZeroSmoothMask m n q v x=0 := by
  let d : ℝ := Nat.gcd (v 0*v 2) (v 1*v 3)
  let P : ℝ := (v 1:ℝ)*(v 3:ℝ)
  let L : ℝ := 2*d*q.M₂/P
  have hp (j : Fin 5) : 0<(v j:ℝ) := by exact_mod_cast (show 0<v j by have := hv j; omega)
  have hd : 0<d := by
    dsimp [d]
    exact_mod_cast Nat.gcd_pos_of_pos_left (v 1*v 3)
      (mul_pos (show 0<v 0 by have := hv 0; omega) (show 0<v 2 by have := hv 2; omega))
  have hP : 0<P := mul_pos (hp 1) (hp 3)
  have hden : 0<d*q.M₂ := mul_pos hd hM₂
  refine ⟨L,by dsimp [L]; positivity,?_⟩
  intro x hx
  rw [a03PhysicalZeroSmoothMask_eq]
  apply Finset.prod_eq_zero (Finset.mem_univ (2:Fin 5))
  by_contra hn
  have hs := rectangularSmoothBlockWeight_tsupport (subset_tsupport _ (by simpa using hn))
  have harg : rectangularZeroArguments q v x 2=P*x/(d*q.M₂) := by
    simp [rectangularZeroArguments,P,d]
  rw [harg] at hs
  have hlo := (le_div_iff₀ hden).mp hs.1
  have hhi := (div_le_iff₀ hden).mp hs.2
  apply hx
  constructor
  · by_contra hxneg
    have hneg : P*x<0 := mul_neg_of_pos_of_neg hP (lt_of_not_ge hxneg)
    linarith
  · dsimp [L]
    apply (le_div_iff₀ hP).mpr
    nlinarith only [hhi]

def a03LeadingZeroTimeIntegrand (F : ℝ→ℂ) (T r s : ℝ) (α : MomentShifts) (z : ℂ)
    (m n : Bool) (q : QuadraticScales) (v : Fin 5→ℕ) (x t : ℝ) : ℂ :=
  let y := a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)
  a03PhysicalZeroSmoothMask m n q v x*a03TensorMellinFactor α z y*
    (Complex.exp (((-a03RealLogGapSymbol T r s (a03SixGapLinear y):ℂ)*I)*(t:ℂ))*F t)

theorem a03LeadingZeroTimeIntegrand_joint_integrable
    (F : ℝ→ℂ) (hFm : Measurable F) (hFi : Integrable F)
    (T r s : ℝ) {α : MomentShifts} (hα : ∀ j,‖α j‖≤1/4) {z : ℂ} (hz : 0≤z.re)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    Integrable (Function.uncurry (a03LeadingZeroTimeIntegrand F T r s α z m n q v))
      ((volume.restrict (Ioi 0)).prod volume) := by
  obtain ⟨L,_hL,hzero⟩ := a03PhysicalZeroSmoothMask_compact_band m n q hM₂ v hv
  let W : ℝ→ℝ := (Icc 0 L).indicator (fun _ => (1:ℝ))
  have hiW : Integrable W (volume.restrict (Ioi 0)) :=
    ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (measure_Icc_lt_top.ne))).restrict
  have hy : Measurable (fun x => a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)) :=
    leadingLogPoint_measurable.comp (leadingSourceArguments_continuous m n q v).measurable
  have hgap : Measurable (fun x => a03RealLogGapSymbol T r s
      (a03SixGapLinear (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))) :=
    (leadingGapSymbol_measurable T r s).comp (a03SixGapLinear.continuous.measurable.comp hy)
  have hm : AEStronglyMeasurable
      (Function.uncurry (a03LeadingZeroTimeIntegrand F T r s α z m n q v))
      ((volume.restrict (Ioi 0)).prod volume) := by
    unfold a03LeadingZeroTimeIntegrand Function.uncurry
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
    unfold Function.uncurry a03LeadingZeroTimeIntegrand
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_exp]
    have hreal : (((-a03RealLogGapSymbol T r s
      (a03SixGapLinear (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v p.1))):ℂ)*I)*(p.2:ℂ)).re=0 := by
      simp
    rw [hreal,Real.exp_zero,one_mul]
    rw [←norm_mul]
    exact mul_le_mul_of_nonneg_right (a03PhysicalZeroSmoothMask_tensor_norm_le_one hα hz m n q v p.1)
      (norm_nonneg _)|>.trans_eq (one_mul _)
  · simp only [W,indicator_of_notMem hx,zero_mul]
    unfold Function.uncurry a03LeadingZeroTimeIntegrand
    simp only [hzero p.1 hx,zero_mul,norm_zero,le_refl]

theorem a03LeadingZeroTimeIntegrand_fubini
    (F : ℝ→ℂ) (hFm : Measurable F) (hFi : Integrable F)
    (T r s : ℝ) {α : MomentShifts} (hα : ∀ j,‖α j‖≤1/4) {z : ℂ} (hz : 0≤z.re)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    (∫ x : ℝ in Ioi 0,∫ t : ℝ,a03LeadingZeroTimeIntegrand F T r s α z m n q v x t)=
      ∫ t : ℝ,∫ x : ℝ in Ioi 0,a03LeadingZeroTimeIntegrand F T r s α z m n q v x t :=
  integral_integral_swap (a03LeadingZeroTimeIntegrand_joint_integrable F hFm hFi T r s hα hz m n q hM₂ v hv)


def a03LeadingPhysicalZeroTimeMode (F : ℝ→ℂ) (T r s : ℝ) (α : MomentShifts) (z : ℂ)
    (m n : Bool) (q : QuadraticScales) (a b : ℕ→ℂ) (t : ℝ) : ℂ :=
  ∑ v∈quadraticMainIndexSet q,a (v 0)*b (v 1)*
    ∫ x : ℝ in Ioi 0,a03LeadingZeroTimeIntegrand F T r s α z m n q v x t

theorem a03LeadingPhysicalZeroTimeMode_integrable_eq
    (F : ℝ→ℂ) (hFm : Measurable F) (hFi : Integrable F)
    (T r s : ℝ) {α : MomentShifts} (hα : ∀ j,‖α j‖≤1/4) {z : ℂ} (hz : 0≤z.re)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂) (a b : ℕ→ℂ) :
    Integrable (a03LeadingPhysicalZeroTimeMode F T r s α z m n q a b) ∧
    a03SixTensorPhysicalZeroMode (fun y => a03TensorMellinFactor α z y*
      profileLaplaceTransform F (((-a03RealLogGapSymbol T r s (a03SixGapLinear y)):ℂ)*I))
      m n q a b=∫ t : ℝ,a03LeadingPhysicalZeroTimeMode F T r s α z m n q a b t := by
  have hj (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) :=
    a03LeadingZeroTimeIntegrand_joint_integrable F hFm hFi T r s hα hz m n q hM₂ v
      (fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv j)).1)
  have hi (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) :
      Integrable (fun t : ℝ => a (v 0)*b (v 1)*
        ∫ x : ℝ in Ioi 0,a03LeadingZeroTimeIntegrand F T r s α z m n q v x t) :=
    (hj v hv).integral_prod_right.const_mul _
  refine ⟨integrable_finsetSum _ hi,?_⟩
  unfold a03LeadingPhysicalZeroTimeMode
  rw [integral_finsetSum _ hi]
  unfold a03SixTensorPhysicalZeroMode
  apply Finset.sum_congr rfl
  intro v hv
  rw [integral_const_mul]
  congr 1
  rw [←integral_integral_swap (hj v hv)]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold a03LeadingZeroTimeIntegrand profileLaplaceTransform a03PhysicalZeroSmoothMask
  simp only [integral_const_mul]
  ring


private theorem supported_product_continuous {Φ A : ℝ→ℂ} (hΦ : Continuous Φ)
    (hA : ∀ x∈tsupport Φ,ContinuousAt A x) : Continuous (a03ProfileProduct Φ A) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x∈tsupport Φ
  · exact hΦ.continuousAt.mul (hA x hx)
  · have he : a03ProfileProduct Φ A=ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport Φ).isOpen_compl.mem_nhds hx] with y hy
      have hz : Φ y=0 := Function.notMem_support.mp (fun hs => hy (subset_tsupport Φ hs))
      simp [a03ProfileProduct,hz]
    exact continuousAt_const.congr_of_eventuallyEq he

theorem a03GaussianLeadingTimeProfile_continuous {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hs : tsupport Φ⊆Icc (1:ℝ) 2) {T : ℝ} (hT : 0<T)
    (σ α : MomentShifts) (z : ℂ) : Continuous (a03GaussianLeadingTimeProfile Φ T σ α z) := by
  unfold a03GaussianLeadingTimeProfile
  apply supported_product_continuous hΦ
  intro x hx
  have hp : 0<T*x/2 := by have := (hs hx).1; positivity
  have hpow : ContinuousAt (fun x : ℝ => ((T*x/2:ℝ):ℂ)^(2*z)) x :=
    (continuousAt_ofReal_cpow_const (T*x/2) (2*z) (Or.inr hp.ne')).comp
      (x := x) (f := fun y : ℝ => T*y/2) (by fun_prop)
  have he : (fun x : ℝ => polarPoleKiller T σ z/z*(T*x/2:ℂ)^(2*z)*(Real.pi:ℂ)^(-2*z))=
      (fun x : ℝ => polarPoleKiller T σ z/z*((T*x/2:ℝ):ℂ)^(2*z)*(Real.pi:ℂ)^(-2*z)) := by
    funext y
    push_cast
    rfl
  rw [he]
  exact (hpow.const_mul _).mul_const _

theorem a03GaussianLeadingTimeProfile_integrable {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hs : tsupport Φ⊆Icc (1:ℝ) 2) {T : ℝ} (hT : 0<T)
    (σ α : MomentShifts) (z : ℂ) : Integrable (a03GaussianLeadingTimeProfile Φ T σ α z) := by
  apply (a03GaussianLeadingTimeProfile_continuous hΦ hs hT σ α z).integrable_of_hasCompactSupport
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    ((a03_profile_product_tsupport _ _).trans hs)

theorem a03LeadingTensorRawKernel_physical_time_reconstruction
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c : ℝ} (hc : 0≤c) (p : A03NearTensorData) (hT : 0<p.T)
    (hα : ∀ j,‖p.α j‖≤1/4) (m n : Bool) (q : QuadraticScales)
    (hM₂ : 0<q.M₂) (a b : ℕ→ℂ) :
    Integrable (a03LeadingPhysicalZeroTimeMode
      (a03GaussianLeadingTimeProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I))
      p.T p.r p.s p.α ((c:ℂ)+(p.v:ℂ)*I) m n q a b) ∧
    a03SixTensorPhysicalZeroMode (a03LeadingTensorRawKernel Φ c p) m n q a b=
      ∫ t : ℝ,a03LeadingPhysicalZeroTimeMode
        (a03GaussianLeadingTimeProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I))
        p.T p.r p.s p.α ((c:ℂ)+(p.v:ℂ)*I) m n q a b t := by
  have hf := a03GaussianLeadingTimeProfile_continuous hΦ hs hT p.σ p.α ((c:ℂ)+(p.v:ℂ)*I)
  have hi := a03GaussianLeadingTimeProfile_integrable hΦ hs hT p.σ p.α ((c:ℂ)+(p.v:ℂ)*I)
  have he : a03LeadingTensorRawKernel Φ c p=(fun y =>
      a03TensorMellinFactor p.α ((c:ℂ)+(p.v:ℂ)*I) y*
        profileLaplaceTransform (a03GaussianLeadingTimeProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I))
          (((-a03RealLogGapSymbol p.T p.r p.s (a03SixGapLinear y)):ℂ)*I)) := by
    funext y
    simp [a03LeadingTensorRawKernel,a03GaussianLeadingFrequencyProfile]
  rw [he]
  exact a03LeadingPhysicalZeroTimeMode_integrable_eq _ hf.measurable hi p.T p.r p.s hα
    (z := ((c:ℂ)+(p.v:ℂ)*I)) (by simpa using hc) m n q hM₂ a b


theorem a03LeadingTensorRawKernel_physical_term_integrable
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c : ℝ} (hc : 0≤c) (p : A03NearTensorData) (hT : 0<p.T)
    (hα : ∀ j,‖p.α j‖≤1/4) (m n : Bool) (q : QuadraticScales)
    (hM₂ : 0<q.M₂) (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
      a03LeadingTensorRawKernel Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) (Ioi 0) := by
  let z : ℂ := (c:ℂ)+(p.v:ℂ)*I
  let F := a03GaussianLeadingTimeProfile Φ p.T p.σ p.α z
  have hFm : Measurable F := (a03GaussianLeadingTimeProfile_continuous hΦ hs hT p.σ p.α z).measurable
  have hFi : Integrable F := a03GaussianLeadingTimeProfile_integrable hΦ hs hT p.σ p.α z
  have hj := a03LeadingZeroTimeIntegrand_joint_integrable F hFm hFi p.T p.r p.s hα
    (z := z) (by simpa [z] using hc) m n q hM₂ v hv
  apply hj.integral_prod_left.congr
  apply ae_of_all
  intro x
  unfold Function.uncurry a03LeadingZeroTimeIntegrand a03LeadingTensorRawKernel
    a03GaussianLeadingFrequencyProfile profileLaplaceTransform
  simp only [integral_const_mul]
  simp only [F,z,Complex.ofReal_neg]
  ring


theorem a03DualLeadingSupportedProfile_continuous {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hs : tsupport Φ⊆Icc (1:ℝ) 2) {T : ℝ} (hT : 0<T) (σ : MomentShifts) :
    Continuous (a03ProfileProduct Φ (bblrDualLeadingMultiplier T σ)) := by
  apply supported_product_continuous hΦ
  intro x hx
  have hp : 0<T*x/(2*Real.pi) := by have := (hs hx).1; positivity
  have hpow : ContinuousAt (fun x : ℝ => ((T*x/(2*Real.pi):ℝ):ℂ)^(-∑j : Fin 4,rawMomentShifts T σ j)) x :=
    (continuousAt_ofReal_cpow_const (T*x/(2*Real.pi)) _ (Or.inr hp.ne')).comp
      (x := x) (f := fun y : ℝ => T*y/(2*Real.pi)) (by fun_prop)
  convert hpow using 1
  unfold bblrDualLeadingMultiplier
  funext y
  push_cast
  rfl

theorem a03GaussianDualLeadingTimeProfile_continuous {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hs : tsupport Φ⊆Icc (1:ℝ) 2) {T : ℝ} (hT : 0<T)
    (σ α : MomentShifts) (z : ℂ) : Continuous (a03GaussianDualLeadingTimeProfile Φ T σ α z) :=
  a03GaussianLeadingTimeProfile_continuous (a03DualLeadingSupportedProfile_continuous hΦ hs hT σ)
    ((a03_profile_product_tsupport _ _).trans hs) hT σ α z

theorem a03GaussianDualLeadingTimeProfile_integrable {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hs : tsupport Φ⊆Icc (1:ℝ) 2) {T : ℝ} (hT : 0<T)
    (σ α : MomentShifts) (z : ℂ) : Integrable (a03GaussianDualLeadingTimeProfile Φ T σ α z) :=
  a03GaussianLeadingTimeProfile_integrable (a03DualLeadingSupportedProfile_continuous hΦ hs hT σ)
    ((a03_profile_product_tsupport _ _).trans hs) hT σ α z

theorem a03LeadingDualTensorRawKernel_physical_term_integrable
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c : ℝ} (hc : 0≤c) (p : A03NearTensorData) (hT : 0<p.T)
    (hα : ∀ j,‖p.α j‖≤1/4) (m n : Bool) (q : QuadraticScales)
    (hM₂ : 0<q.M₂) (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
      a03LeadingDualTensorRawKernel Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) (Ioi 0) :=
  a03LeadingTensorRawKernel_physical_term_integrable
    (a03DualLeadingSupportedProfile_continuous hΦ hs hT p.σ)
    ((a03_profile_product_tsupport _ _).trans hs) hc p hT hα m n q hM₂ v hv

theorem a03LeadingDualTensorRawKernel_physical_time_reconstruction
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c : ℝ} (hc : 0≤c) (p : A03NearTensorData) (hT : 0<p.T)
    (hα : ∀ j,‖p.α j‖≤1/4) (m n : Bool) (q : QuadraticScales)
    (hM₂ : 0<q.M₂) (a b : ℕ→ℂ) :
    Integrable (a03LeadingPhysicalZeroTimeMode
      (a03GaussianDualLeadingTimeProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I))
      p.T p.r p.s p.α ((c:ℂ)+(p.v:ℂ)*I) m n q a b) ∧
    a03SixTensorPhysicalZeroMode (a03LeadingDualTensorRawKernel Φ c p) m n q a b=
      ∫ t : ℝ,a03LeadingPhysicalZeroTimeMode
        (a03GaussianDualLeadingTimeProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I))
        p.T p.r p.s p.α ((c:ℂ)+(p.v:ℂ)*I) m n q a b t :=
  a03LeadingTensorRawKernel_physical_time_reconstruction
    (a03DualLeadingSupportedProfile_continuous hΦ hs hT p.σ)
    ((a03_profile_product_tsupport _ _).trans hs) hc p hT hα m n q hM₂ a b

end
end Sechstmoment
