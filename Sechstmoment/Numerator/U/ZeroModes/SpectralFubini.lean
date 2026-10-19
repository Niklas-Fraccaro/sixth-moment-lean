import Sechstmoment.Numerator.U.Replacement.VStar.SourcePhysicalPoint
import Sechstmoment.Numerator.U.ZeroModes.Replacement.Measurability

/-! Absolute three-variable convergence for the source-scaled native zero.
The majorant uses the actual smooth physical band and the Gaussian on the
small positive Mellin line. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 300000

theorem a03ZeroModeMellinScaleFactor_vertical_norm
    (q : QuadraticScales) (hq : ∀ j,0<a03ZeroModeQuadScales q j)
    (α : MomentShifts) (c w : ℝ) :
    ‖a03ZeroModeMellinScaleFactor q α ((c:ℂ)+(w:ℂ)*I)‖=
      ‖a03ZeroModeMellinScaleFactor q α (c:ℂ)‖ := by
  unfold a03ZeroModeMellinScaleFactor
  rw [norm_prod,norm_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (hq j),
    Complex.norm_cpow_eq_rpow_re_of_pos (hq j)]
  simp

theorem a03GaussianLeadingTimeProfile_gaussian_bound
    {Φ : ℝ→ℂ} (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts) (w t : ℝ) :
    ‖a03GaussianLeadingTimeProfile Φ T σ α ((c:ℂ)+(w:ℂ)*I) t‖≤
      (polarGaussianConstant T σ c/c*(2*T)^(2*c))*
        ((1+|w|)^48*Real.exp (-(1/2)*w^2))*‖Φ t‖ := by
  by_cases ht : Φ t=0
  · simp [a03GaussianLeadingTimeProfile,a03ProfileProduct,ht]
  · have hts := hSupp (subset_tsupport _ ht)
    have hb := a03PhysicalLeadingTimeAmplitude_gaussian_bound hT hc σ α
      (fun _ : Fin 4 => 1) (by intro j; norm_num) w t hts
    simp only [a03PhysicalLeadingTimeAmplitude,a03ZeroModeRealQuadDenominator,
      a03PhysicalQuadProduct] at hb
    simp only [Complex.ofReal_one,Complex.one_cpow,Finset.prod_const_one,inv_one,
      norm_one,one_mul,Real.one_rpow,mul_one] at hb
    unfold a03GaussianLeadingTimeProfile a03ProfileProduct
    rw [norm_mul]
    calc
      _≤‖Φ t‖*((polarGaussianConstant T σ c/c*(2*T)^(2*c))*
        ((1+|w|)^48*Real.exp (-(1/2)*w^2))) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _=_ := by ring

def a03SourceSpectralZeroTimeIntegrand
    (Φ : ℝ→ℂ) (T c : ℝ) (σ α : MomentShifts)
    (P : A03SixTensorSpace→ℝ) (m n : Bool) (q : QuadraticScales)
    (v : Fin 5→ℕ) (w x t : ℝ) : ℂ :=
  a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α ((c:ℂ)+(w:ℂ)*I)*
    a03PhaseZeroTimeIntegrand
      (a03GaussianLeadingTimeProfile Φ T σ α ((c:ℂ)+(w:ℂ)*I))
      P α ((c:ℂ)+(w:ℂ)*I) m n q v x t

theorem a03SourceSpectralZeroTimeIntegrand_joint_integrable
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts)
    (hα : ∀ j,‖α j‖≤1/4) (P : A03SixTensorSpace→ℝ) (hP : Measurable P)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (hq : ∀ j,0<a03ZeroModeQuadScales (phasePairSwapScales m n q) j)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    Integrable (fun p : ℝ×(ℝ×ℝ) =>
      a03SourceSpectralZeroTimeIntegrand Φ T c σ α P m n q v p.1 p.2.1 p.2.2)
      (volume.prod ((volume.restrict (Ioi 0)).prod volume)) := by
  obtain ⟨L,_hL,hzero⟩ := a03PhysicalZeroSmoothMask_compact_band m n q hM₂ v hv
  let W : ℝ→ℝ := (Icc 0 L).indicator (fun _ => (1:ℝ))
  let B : ℝ := ‖a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α (c:ℂ)‖*
    (polarGaussianConstant T σ c/c*(2*T)^(2*c))
  have hCG := polarGaussianConstant_nonneg T σ c
  have hB : 0≤B := by dsimp [B]; positivity
  have hiW : Integrable W (volume.restrict (Ioi 0)) :=
    ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (measure_Icc_lt_top.ne))).restrict
  have hFi : Integrable Φ := hΦ.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hSupp)
  have hy : Measurable (fun x => a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)) :=
    a03SixTensorLogPoint_measurable.comp (a03SixZeroSourceArguments_continuous m n q v).measurable
  have hgap := hP.comp hy
  have hscale : Measurable (fun w : ℝ =>
      a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α ((c:ℂ)+(w:ℂ)*I)) := by
    unfold a03ZeroModeMellinScaleFactor
    apply Finset.measurable_prod
    intro j _
    exact measurable_const.pow (by fun_prop)
  have hM : Measurable (fun p : ℝ×(ℝ×ℝ) =>
      a03TensorMellinFactor α ((c:ℂ)+(p.1:ℂ)*I)
        (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v p.2.1))) :=
    by
      have hmap : Measurable (fun p : ℝ×(ℝ×ℝ) =>
          (p.1,a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v p.2.1))) :=
        measurable_fst.prodMk (hy.comp (measurable_fst.comp measurable_snd))
      simpa only [Function.comp_def] using
        (a03TensorMellinFactor_joint_continuous α c).measurable.comp hmap
  have hprof : Measurable (fun p : ℝ×(ℝ×ℝ) =>
      a03GaussianLeadingTimeProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2.2) :=
    by
      have hmap : Measurable (fun p : ℝ×(ℝ×ℝ) => (p.1,p.2.2)) :=
        measurable_fst.prodMk (measurable_snd.comp measurable_snd)
      simpa only [Function.comp_def] using
        (a03GaussianLeadingTimeProfile_mellin_joint_measurable Φ hΦ.measurable T c σ α).comp hmap
  have hphase : Measurable (fun p : ℝ×(ℝ×ℝ) =>
      Complex.exp (((-P (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v p.2.1)):ℂ)*I)*(p.2.2:ℂ))) :=
    by
      convert ((((Complex.continuous_ofReal.measurable.comp (hgap.neg.comp (measurable_fst.comp measurable_snd))).mul_const I).mul
        (Complex.continuous_ofReal.measurable.comp (measurable_snd.comp measurable_snd))).cexp) using 1
      funext p
      simp only [Function.comp_apply,Pi.mul_apply,Pi.neg_apply,Complex.ofReal_neg]
  have hm : AEStronglyMeasurable (fun p : ℝ×(ℝ×ℝ) =>
      a03SourceSpectralZeroTimeIntegrand Φ T c σ α P m n q v p.1 p.2.1 p.2.2)
      (volume.prod ((volume.restrict (Ioi 0)).prod volume)) := by
    convert ((hscale.comp measurable_fst).mul
      (((a03PhysicalZeroSmoothMask_continuous m n q v).measurable.comp
        (measurable_fst.comp measurable_snd)).mul hM |>.mul (hphase.mul hprof))).aestronglyMeasurable using 1
    funext p
    simp [a03SourceSpectralZeroTimeIntegrand,a03PhaseZeroTimeIntegrand]
  apply (((gaussian_polynomial_half_integrable 48).mul_prod (hiW.mul_prod hFi.norm)).const_mul B).mono' hm
  apply ae_of_all
  intro p
  by_cases hx : p.2.1∈Icc 0 L
  · simp only [W,indicator_of_mem hx,one_mul]
    unfold a03SourceSpectralZeroTimeIntegrand a03PhaseZeroTimeIntegrand
    rw [norm_mul,norm_mul,norm_mul,norm_mul,Complex.norm_exp]
    have hre : (((-P (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v p.2.1)):ℂ)*I)*(p.2.2:ℂ)).re=0 := by simp
    rw [hre,Real.exp_zero,one_mul,a03ZeroModeMellinScaleFactor_vertical_norm _ hq]
    have hmell := a03PhysicalZeroSmoothMask_tensor_norm_le_one hα
      (z := ((c:ℂ)+(p.1:ℂ)*I)) (by simpa using hc.le) m n q v p.2.1
    have hp := a03GaussianLeadingTimeProfile_gaussian_bound hSupp hT hc σ α p.1 p.2.2
    rw [norm_mul] at hmell
    calc
      _≤‖a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α (c:ℂ)‖*
        (1*((polarGaussianConstant T σ c/c*(2*T)^(2*c))*
          ((1+|p.1|)^48*Real.exp (-(1/2)*p.1^2))*‖Φ p.2.2‖)) := by gcongr
      _=_ := by dsimp [B]; ring
  · simp only [W,indicator_of_notMem hx]
    simp [a03SourceSpectralZeroTimeIntegrand,a03PhaseZeroTimeIntegrand,hzero p.2.1 hx]

theorem a03SourceSpectralZeroTimeIntegrand_integral_time_integrable
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts)
    (hα : ∀ j,‖α j‖≤1/4) (P : A03SixTensorSpace→ℝ) (hP : Measurable P)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (hq : ∀ j,0<a03ZeroModeQuadScales (phasePairSwapScales m n q) j)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    Integrable (fun p : ℝ×ℝ => ∫t : ℝ,
      a03SourceSpectralZeroTimeIntegrand Φ T c σ α P m n q v p.1 p.2 t)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hj := a03SourceSpectralZeroTimeIntegrand_joint_integrable
    hΦ hSupp hT hc σ α hα P hP m n q hM₂ hq v hv
  have ha := (measurePreserving_prodAssoc volume (volume.restrict (Ioi (0:ℝ))) volume).integrable_comp_of_integrable hj
  exact ha.integral_prod_left

theorem a03SourceSpectralZeroTimeIntegrand_integral_time_eq
    (Φ : ℝ→ℂ) (T c : ℝ) (σ α : MomentShifts)
    (P : A03SixTensorSpace→ℝ) (m n : Bool) (q : QuadraticScales)
    (v : Fin 5→ℕ) (w x : ℝ) :
    (∫t : ℝ,a03SourceSpectralZeroTimeIntegrand Φ T c σ α P m n q v w x t)=
      a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α ((c:ℂ)+(w:ℂ)*I)*
        (a03PhysicalZeroSmoothMask m n q v x*
          (a03TensorMellinFactor α ((c:ℂ)+(w:ℂ)*I)
            (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))*
            profileLaplaceTransform
              (a03GaussianLeadingTimeProfile Φ T σ α ((c:ℂ)+(w:ℂ)*I))
              (((-P (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))):ℂ)*I))) := by
  unfold a03SourceSpectralZeroTimeIntegrand a03PhaseZeroTimeIntegrand profileLaplaceTransform
  simp only [integral_const_mul]
  ring

theorem a03SourceSpectralZeroTimeIntegrand_spectral_physical_fubini
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts)
    (hα : ∀ j,‖α j‖≤1/4) (P : A03SixTensorSpace→ℝ) (hP : Measurable P)
    (m n : Bool) (q : QuadraticScales) (hM₂ : 0<q.M₂)
    (hq : ∀ j,0<a03ZeroModeQuadScales (phasePairSwapScales m n q) j)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) :
    (∫w : ℝ,∫x : ℝ in Ioi 0,∫t : ℝ,
      a03SourceSpectralZeroTimeIntegrand Φ T c σ α P m n q v w x t)=
      ∫x : ℝ in Ioi 0,∫w : ℝ,∫t : ℝ,
        a03SourceSpectralZeroTimeIntegrand Φ T c σ α P m n q v w x t :=
  integral_integral_swap (a03SourceSpectralZeroTimeIntegrand_integral_time_integrable
    hΦ hSupp hT hc σ α hα P hP m n q hM₂ hq v hv)

end
end Sechstmoment
