import Sechstmoment.Numerator.U.ZeroModes.RatioEuclideanMultiplier
import Sechstmoment.Numerator.U.ZeroModes.SpectralFubini

/-! The full positive-line V* reconstruction of the actual native physical
zero, retaining every arithmetic weight and a genuine ratio multiplier. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 300000

def a03PhysicalLinearVStarZeroMode (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (r s : ℝ) (G : A03SixTensorSpace→ℂ) (m n : Bool) (q : QuadraticScales)
    (a b : ℕ→ℂ) : ℂ :=
  ∑ v∈quadraticMainIndexSet q,a (v 0)*b (v 1)*∫x : ℝ in Ioi 0,
    let y := a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)
    let Q := a03ZeroModePermutedPhysicalQuad m n q v x
    a03PhysicalZeroSmoothMask m n q v x*G y*
      (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*
        ∫t : ℝ,Complex.exp (((-(T*s*r*Real.exp (a03SixGapLinear y)):ℝ):ℂ)*I*(t:ℂ))*Φ t*
          bblrVStar (polarPoleKiller T σ) (a03PhysicalQuadProduct Q/(T*t)^2)

def a03SourceSpectralLinearZeroTerm (Φ : ℝ→ℂ) (T c : ℝ) (σ α : MomentShifts)
    (r s : ℝ) (G : A03SixTensorSpace→ℂ) (m n : Bool) (q : QuadraticScales)
    (v : Fin 5→ℕ) (w x : ℝ) : ℂ :=
  a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α ((c:ℂ)+(w:ℂ)*I)*
    (a03PhysicalZeroSmoothMask m n q v x*
      (G (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))*
        a03LeadingLinearTensorRawKernel Φ c ⟨T,σ,α,w,r,s⟩
          (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))))

theorem a03SourceSpectralLinearZeroTerm_joint_integrable
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts)
    (hα : ∀ j,‖α j‖≤1/4) (r s : ℝ)
    (G : A03SixTensorSpace→ℂ) (hG : Measurable G) {K : ℝ} (hGK : ∀ y,‖G y‖≤K)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (hq : ∀ j,0<a03ZeroModeQuadScales (phasePairSwapScales m n q) j)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    Integrable (Function.uncurry (a03SourceSpectralLinearZeroTerm Φ T c σ α r s G m n q v))
      (volume.prod (volume.restrict (Ioi 0))) := by
  let P := a03LinearZeroGap ⟨T,σ,α,0,r,s⟩
  have hj := a03SourceSpectralZeroTimeIntegrand_integral_time_integrable
    hΦ hSupp hT hc σ α hα P (a03LinearZeroGap_continuous _).measurable m n q hM₂ hq v hv
  have hy : Measurable (fun x => a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)) :=
    a03SixTensorLogPoint_measurable.comp (a03SixZeroSourceArguments_continuous m n q v).measurable
  have hm : AEStronglyMeasurable (fun p : ℝ×ℝ =>
      G (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v p.2)))
      (volume.prod (volume.restrict (Ioi 0))) :=
    (hG.comp (hy.comp measurable_snd)).aestronglyMeasurable
  apply (hj.bdd_mul hm (ae_of_all _ fun p => hGK _)).congr
  apply ae_of_all
  intro p
  dsimp only
  rw [a03SourceSpectralZeroTimeIntegrand_integral_time_eq]
  unfold Function.uncurry a03SourceSpectralLinearZeroTerm a03LeadingLinearTensorRawKernel
    a03GaussianLeadingFrequencyProfile P a03LinearZeroGap
  dsimp only
  simp only [Complex.ofReal_mul,Complex.ofReal_neg,neg_mul]
  ring

theorem a03SourceSpectralLinearZeroTerm_set_joint_integrable
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts)
    (hα : ∀ j,‖α j‖≤1/4) (r s : ℝ)
    (G : A03SixTensorSpace→ℂ) (hG : Measurable G) {K : ℝ} (hGK : ∀ y,‖G y‖≤K)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (hq : ∀ j,0<a03ZeroModeQuadScales (phasePairSwapScales m n q) j)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) (S : Set ℝ) :
    Integrable (Function.uncurry (a03SourceSpectralLinearZeroTerm Φ T c σ α r s G m n q v))
      ((volume.restrict S).prod (volume.restrict (Ioi 0))) :=
  (a03SourceSpectralLinearZeroTerm_joint_integrable hΦ hSupp hT hc σ α hα r s G hG hGK
    m n q hM₂ hq v hv).mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)

def a03SourceSpectralNativeLinearZero (Φ : ℝ→ℂ) (T c : ℝ) (σ α : MomentShifts)
    (r s : ℝ) (G : A03SixTensorSpace→ℂ) (m n : Bool) (q : QuadraticScales)
    (a b : ℕ→ℂ) (w : ℝ) : ℂ :=
  a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α ((c:ℂ)+(w:ℂ)*I)*
    a03SixTensorPhysicalZeroMode
      (fun y => G y*a03LeadingLinearTensorRawKernel Φ c ⟨T,σ,α,w,r,s⟩ y) m n q a b

theorem a03SourceSpectralNativeLinearZero_eq_sum_terms
    (Φ : ℝ→ℂ) (T c : ℝ) (σ α : MomentShifts) (r s : ℝ)
    (G : A03SixTensorSpace→ℂ) (m n : Bool) (q : QuadraticScales)
    (a b : ℕ→ℂ) (w : ℝ) :
    a03SourceSpectralNativeLinearZero Φ T c σ α r s G m n q a b w=
      ∑v∈quadraticMainIndexSet q,a (v 0)*b (v 1)*∫x : ℝ in Ioi 0,
        a03SourceSpectralLinearZeroTerm Φ T c σ α r s G m n q v w x := by
  unfold a03SourceSpectralNativeLinearZero a03SixTensorPhysicalZeroMode
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  unfold a03SourceSpectralLinearZeroTerm a03PhysicalZeroSmoothMask
  rw [integral_const_mul]
  ring

theorem a03SourceSpectralNativeLinearZero_set_integrable
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts)
    (hα : ∀ j,‖α j‖≤1/4) (r s : ℝ)
    (G : A03SixTensorSpace→ℂ) (hG : Measurable G) {K : ℝ} (hGK : ∀ y,‖G y‖≤K)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (hq : ∀ j,0<a03ZeroModeQuadScales (phasePairSwapScales m n q) j)
    (a b : ℕ→ℂ) (S : Set ℝ) :
    IntegrableOn (a03SourceSpectralNativeLinearZero Φ T c σ α r s G m n q a b) S := by
  have hj (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) :=
    a03SourceSpectralLinearZeroTerm_set_joint_integrable hΦ hSupp hT hc σ α hα r s G hG hGK
      m n q hM₂ hq v (fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv j)).1) S
  apply (integrable_finsetSum _ (fun v hv => (hj v hv).integral_prod_left.const_mul (a (v 0)*b (v 1)))).congr
  exact ae_of_all _ fun w => (a03SourceSpectralNativeLinearZero_eq_sum_terms Φ T c σ α r s G m n q a b w).symm

theorem a03SourceSpectralNativeLinearZero_set_fubini
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts)
    (hα : ∀ j,‖α j‖≤1/4) (r s : ℝ)
    (G : A03SixTensorSpace→ℂ) (hG : Measurable G) {K : ℝ} (hGK : ∀ y,‖G y‖≤K)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (hq : ∀ j,0<a03ZeroModeQuadScales (phasePairSwapScales m n q) j)
    (a b : ℕ→ℂ) (S : Set ℝ) :
    (∫w : ℝ in S,a03SourceSpectralNativeLinearZero Φ T c σ α r s G m n q a b w)=
      ∑v∈quadraticMainIndexSet q,a (v 0)*b (v 1)*∫x : ℝ in Ioi 0,
        ∫w : ℝ in S,a03SourceSpectralLinearZeroTerm Φ T c σ α r s G m n q v w x := by
  have hj (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) :=
    a03SourceSpectralLinearZeroTerm_set_joint_integrable hΦ hSupp hT hc σ α hα r s G hG hGK
      m n q hM₂ hq v (fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv j)).1) S
  have hi (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) :
      Integrable (fun w : ℝ => a (v 0)*b (v 1)*∫x : ℝ in Ioi 0,
        a03SourceSpectralLinearZeroTerm Φ T c σ α r s G m n q v w x) (volume.restrict S) := by
    simpa only [Function.uncurry] using (hj v hv).integral_prod_left.const_mul (a (v 0)*b (v 1))
  simp_rw [a03SourceSpectralNativeLinearZero_eq_sum_terms]
  rw [integral_finsetSum _ hi]
  apply Finset.sum_congr rfl
  intro v hv
  rw [integral_const_mul,integral_integral_swap (hj v hv)]

theorem a03SourceSpectralNativeLinearZero_full_eq_VStar
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts)
    (hα : ∀ j,‖α j‖≤1/4) (r s : ℝ)
    (G : A03SixTensorSpace→ℂ) (hG : Measurable G) {K : ℝ} (hGK : ∀ y,‖G y‖≤K)
    (m n : Bool) (q : QuadraticScales) (hq : ∀ j,0<q.size j)
    (a b : ℕ→ℂ) :
    (1/(2*Real.pi):ℂ)*(∫w : ℝ,
      a03SourceSpectralNativeLinearZero Φ T c σ α r s G m n q a b w)=
      a03PhysicalLinearVStarZeroMode Φ T σ α r s G m n q a b := by
  have hM₂ : 0<q.M₂ := by simpa [QuadraticScales.size] using hq 3
  have hquad : ∀ j,0<a03ZeroModeQuadScales (phasePairSwapScales m n q) j := by
    intro j
    cases m <;> cases n <;> fin_cases j <;>
      simp [a03ZeroModeQuadScales,phasePairSwapScales] <;>
      first | exact hq 2 | exact hq 3 | exact hq 4 | exact hq 5
  have he := a03SourceSpectralNativeLinearZero_set_fubini hΦ hSupp hT hc σ α hα r s
    G hG hGK m n q hM₂ hquad a b univ
  simp only [Measure.restrict_univ] at he
  rw [he,Finset.mul_sum]
  unfold a03PhysicalLinearVStarZeroMode
  apply Finset.sum_congr rfl
  intro v hv
  have hv1 (j : Fin 5) : 1≤v j := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv j)).1
  rw [show (1/(2*Real.pi):ℂ)*(a (v 0)*b (v 1)*∫x : ℝ in Ioi 0,
      ∫w : ℝ,a03SourceSpectralLinearZeroTerm Φ T c σ α r s G m n q v w x)=
      a (v 0)*b (v 1)*(∫x : ℝ in Ioi 0,(1/(2*Real.pi):ℂ)*
        ∫w : ℝ,a03SourceSpectralLinearZeroTerm Φ T c σ α r s G m n q v w x) by
      rw [integral_const_mul]; ring]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0<x := hx
  have hp := a03LeadingLinearTensor_sourceScale_vertical_eq_VStar hΦ hSupp hT hc σ α r s m n q hq v hv1 hx0
  unfold a03SourceSpectralLinearZeroTerm
  dsimp only
  calc
    _=(a03PhysicalZeroSmoothMask m n q v x*
        G (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))*
      ((1/(2*Real.pi):ℂ)*∫w : ℝ,
        a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α ((c:ℂ)+(w:ℂ)*I)*
          a03LeadingLinearTensorRawKernel Φ c ⟨T,σ,α,w,r,s⟩
            (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) := by
      simp only [←integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun w => by ring
    _=_ := by rw [hp]; ring

def a03PhysicalSpectralSetNativeLinearZero (Φ : ℝ→ℂ) (T c : ℝ) (σ α : MomentShifts)
    (r s : ℝ) (G : A03SixTensorSpace→ℂ) (m n : Bool) (q : QuadraticScales)
    (a b : ℕ→ℂ) (S : Set ℝ) : ℂ :=
  ∑ v∈quadraticMainIndexSet q,a (v 0)*b (v 1)*∫x : ℝ in Ioi 0,
    let y := a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)
    a03PhysicalZeroSmoothMask m n q v x*G y*
      a03PhysicalLeadingFourierSet Φ c T σ α (a03ZeroModePermutedPhysicalQuad m n q v x)
        (T*s*r*Real.exp (a03SixGapLinear y)) S

theorem a03SourceSpectralNativeLinearZero_set_eq_physical
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts)
    (hα : ∀ j,‖α j‖≤1/4) (r s : ℝ)
    (G : A03SixTensorSpace→ℂ) (hG : Measurable G) {K : ℝ} (hGK : ∀ y,‖G y‖≤K)
    (m n : Bool) (q : QuadraticScales) (hq : ∀ j,0<q.size j)
    (a b : ℕ→ℂ) (S : Set ℝ) :
    (1/(2*Real.pi):ℂ)*(∫w : ℝ in S,
      a03SourceSpectralNativeLinearZero Φ T c σ α r s G m n q a b w)=
      a03PhysicalSpectralSetNativeLinearZero Φ T c σ α r s G m n q a b S := by
  have hM₂ : 0<q.M₂ := by simpa [QuadraticScales.size] using hq 3
  have hquad : ∀ j,0<a03ZeroModeQuadScales (phasePairSwapScales m n q) j := by
    intro j
    cases m <;> cases n <;> fin_cases j <;>
      simp [a03ZeroModeQuadScales,phasePairSwapScales] <;>
      first | exact hq 2 | exact hq 3 | exact hq 4 | exact hq 5
  rw [a03SourceSpectralNativeLinearZero_set_fubini hΦ hSupp hT hc σ α hα r s
    G hG hGK m n q hM₂ hquad a b S,Finset.mul_sum]
  unfold a03PhysicalSpectralSetNativeLinearZero
  apply Finset.sum_congr rfl
  intro v hv
  have hv1 (j : Fin 5) : 1≤v j := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv j)).1
  rw [show (1/(2*Real.pi):ℂ)*(a (v 0)*b (v 1)*∫x : ℝ in Ioi 0,
      ∫w : ℝ in S,a03SourceSpectralLinearZeroTerm Φ T c σ α r s G m n q v w x)=
      a (v 0)*b (v 1)*(∫x : ℝ in Ioi 0,(1/(2*Real.pi):ℂ)*
        ∫w : ℝ in S,a03SourceSpectralLinearZeroTerm Φ T c σ α r s G m n q v w x) by
      rw [integral_const_mul]; ring]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hp := a03LeadingLinearTensor_sourceScale_set_eq_physicalFourier Φ c T σ α r s m n q hq v hv1 hx S
  unfold a03SourceSpectralLinearZeroTerm
  dsimp only
  calc
    _=(a03PhysicalZeroSmoothMask m n q v x*
        G (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))*
      ((1/(2*Real.pi):ℂ)*∫w : ℝ in S,
        a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α ((c:ℂ)+(w:ℂ)*I)*
          a03LeadingLinearTensorRawKernel Φ c ⟨T,σ,α,w,r,s⟩
            (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) := by
      simp only [←integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun w => by ring
    _=_ := by rw [hp]

theorem a03SourceSpectralNativeLinearZero_core_sub_full_eq_neg_tail
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts)
    (hα : ∀ j,‖α j‖≤1/4) (r s L : ℝ)
    (G : A03SixTensorSpace→ℂ) (hG : Measurable G) {K : ℝ} (hGK : ∀ y,‖G y‖≤K)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (hq : ∀ j,0<a03ZeroModeQuadScales (phasePairSwapScales m n q) j)
    (a b : ℕ→ℂ) :
    (1/(2*Real.pi):ℂ)*(∫w : ℝ in Icc (-L) L,
      a03SourceSpectralNativeLinearZero Φ T c σ α r s G m n q a b w)-
      (1/(2*Real.pi):ℂ)*(∫w : ℝ,
        a03SourceSpectralNativeLinearZero Φ T c σ α r s G m n q a b w)=
      -(1/(2*Real.pi):ℂ)*(∫w : ℝ in {w : ℝ | L < |w|},
        a03SourceSpectralNativeLinearZero Φ T c σ α r s G m n q a b w) := by
  have hi := a03SourceSpectralNativeLinearZero_set_integrable hΦ hSupp hT hc σ α hα r s
    G hG hGK m n q hM₂ hq a b univ
  simp only [IntegrableOn,Measure.restrict_univ] at hi
  have hs : MeasurableSet {w : ℝ | L < |w|} := (isOpen_lt continuous_const continuous_abs).measurableSet
  have he := integral_add_compl hs hi
  have hset : {w : ℝ | L < |w|}ᶜ=Icc (-L) L := by
    ext w
    simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_lt,Set.mem_Icc]
    exact abs_le
  rw [hset] at he
  rw [←he]
  ring

end
end Sechstmoment
