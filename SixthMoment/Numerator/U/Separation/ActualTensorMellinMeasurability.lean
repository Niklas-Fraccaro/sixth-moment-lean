import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import SixthMoment.Numerator.U.Separation.TimeFarContourBudget
import SixthMoment.Numerator.U.Sources.PhysicalBound

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology FourierTransform
open Classical
noncomputable section
set_option maxHeartbeats 200000

theorem a03TensorMellinFactor_joint_continuous (α : MomentShifts) (c : ℝ) :
    Continuous (fun p : ℝ×A03SixTensorSpace =>
      a03TensorMellinFactor α ((c:ℂ)+(p.1:ℂ)*I) p.2) := by
  simp_rw [a03TensorMellinFactor_eq_exp]
  apply Continuous.cexp
  apply continuous_finsetSum
  intro i _
  have hy : Continuous (fun p : ℝ×A03SixTensorSpace => p.2 i.succ.succ) :=
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 6 => ℝ) i.succ.succ).continuous.comp continuous_snd
  exact (by fun_prop : Continuous (fun p : ℝ×A03SixTensorSpace =>
    -(1/2+α i+((c:ℂ)+(p.1:ℂ)*I)))).mul (Complex.continuous_ofReal.comp hy)

theorem a03GaussianTimeAmplitude_mellin_joint_continuous {c : ℝ} (hc : 0<c)
    (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
    Continuous (fun p : ℝ×ℝ =>
      bblrGaussianTimeAmplitude T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) := by
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
  have hmap : Continuous (fun p : ℝ×ℝ => (p.1,T*p.2)) := by fun_prop
  change Continuous (fun p : ℝ×ℝ =>
    (polarPoleKiller T σ ((c:ℂ)+(p.1:ℂ)*I)/((c:ℂ)+(p.1:ℂ)*I)*
      (Real.pi:ℂ)^(-2*((c:ℂ)+(p.1:ℂ)*I)))*
      bblrGammaQuotient (T*p.2) α ((c:ℂ)+(p.1:ℂ)*I))
  apply Continuous.mul
  · exact (hG.div hz hz0).mul hπ
  · simpa only [Function.comp_def] using
      (a03_small_positive_Gamma_quotient_joint_continuous hc α hα).comp hmap

theorem a03GaussianFrequencyProfile_mellin_joint_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (Φ : ℝ → ℂ) (hΦ : Continuous Φ) :
    StronglyMeasurable (fun p : ℝ×ℝ =>
      a03GaussianFrequencyProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) := by
  have hΓ := a03GaussianTimeAmplitude_mellin_joint_continuous hc T σ α hα
  have hΓ' : Continuous (fun p : (ℝ×ℝ)×ℝ =>
      bblrGaussianTimeAmplitude T σ α ((c:ℂ)+(p.1.1:ℂ)*I) p.2) :=
    hΓ.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hosc : Continuous (fun p : (ℝ×ℝ)×ℝ => Complex.exp (((p.1.2:ℂ)*I)*(p.2:ℂ))) := by fun_prop
  have hh : Continuous (fun p : (ℝ×ℝ)×ℝ =>
      Complex.exp (((p.1.2:ℂ)*I)*(p.2:ℂ)) *
        (Φ p.2*bblrGaussianTimeAmplitude T σ α ((c:ℂ)+(p.1.1:ℂ)*I) p.2)) :=
    hosc.mul ((hΦ.comp continuous_snd).mul hΓ')
  exact hh.stronglyMeasurable.integral_prod_right'

theorem a03GaussianDualFrequencyProfile_mellin_joint_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4)
    (Φ : ℝ → ℂ) (hΦ : Continuous Φ) :
    StronglyMeasurable (fun p : ℝ×ℝ =>
      a03GaussianDualFrequencyProfile Φ T σ α ((c:ℂ)+(p.1:ℂ)*I) p.2) := by
  have hΓ := a03GaussianTimeAmplitude_mellin_joint_continuous hc T σ α hα
  have hΓ' : Continuous (fun p : (ℝ×ℝ)×ℝ =>
      bblrGaussianTimeAmplitude T σ α ((c:ℂ)+(p.1.1:ℂ)*I) p.2) :=
    hΓ.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hr : ∀ j, |(rawMomentShifts T σ j).re|<1/2 := by
    intro j
    exact ((Complex.abs_re_le_norm _).trans (hσ j)).trans_lt (by norm_num)
  have hD : Continuous (fun p : (ℝ×ℝ)×ℝ =>
      bblrDualMultiplier (T*p.2) (rawMomentShifts T σ)) :=
    (rectangular_dual_multiplier_continuous _ hr).comp (continuous_snd.const_mul T)
  have hosc : Continuous (fun p : (ℝ×ℝ)×ℝ => Complex.exp (((p.1.2:ℂ)*I)*(p.2:ℂ))) := by fun_prop
  have hh : Continuous (fun p : (ℝ×ℝ)×ℝ =>
      Complex.exp (((p.1.2:ℂ)*I)*(p.2:ℂ)) *
        ((Φ p.2*bblrDualMultiplier (T*p.2) (rawMomentShifts T σ))*
          bblrGaussianTimeAmplitude T σ α ((c:ℂ)+(p.1.1:ℂ)*I) p.2)) :=
    hosc.mul (((hΦ.comp continuous_snd).mul hD).mul hΓ')
  exact hh.stronglyMeasurable.integral_prod_right'

theorem a03RealLogGapSymbol_measurable (T r s : ℝ) : Measurable (a03RealLogGapSymbol T r s) := by
  unfold a03RealLogGapSymbol
  fun_prop

theorem a03_actual_main_tensor_kernel_mellin_joint_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T ε r s : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (Φ : ℝ → ℂ) (hΦ : Continuous Φ) :
    StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
      a03ActualTensorNormalizedKernel Φ c ε ⟨T,σ,α,p.1,r,s⟩ p.2) := by
  have hgap : Measurable (fun y : A03SixTensorSpace =>
      a03RealLogGapSymbol T r s (a03SixGapLinear y)) :=
    (a03RealLogGapSymbol_measurable T r s).comp a03SixGapLinear.continuous.measurable
  have hf := (a03GaussianFrequencyProfile_mellin_joint_stronglyMeasurable hc T σ α hα Φ hΦ).comp_measurable
    (measurable_fst.prodMk (hgap.neg.comp measurable_snd))
  exact ((a03TensorMellinFactor_joint_continuous α c).stronglyMeasurable.mul hf).const_smul (T^(-ε))

theorem a03_actual_dual_tensor_kernel_mellin_joint_stronglyMeasurable
    {c : ℝ} (hc : 0<c) (T ε r s : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (hσ : ∀ j, ‖rawMomentShifts T σ j‖≤1/4)
    (Φ : ℝ → ℂ) (hΦ : Continuous Φ) :
    StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
      a03ActualDualTensorNormalizedKernel Φ c ε ⟨T,σ,α,p.1,r,s⟩ p.2) := by
  have hgap : Measurable (fun y : A03SixTensorSpace =>
      a03RealLogGapSymbol T r s (a03SixGapLinear y)) :=
    (a03RealLogGapSymbol_measurable T r s).comp a03SixGapLinear.continuous.measurable
  have hf := (a03GaussianDualFrequencyProfile_mellin_joint_stronglyMeasurable hc T σ α hα hσ Φ hΦ).comp_measurable
    (measurable_fst.prodMk ((hgap.neg).comp measurable_snd))
  exact ((a03TensorMellinFactor_joint_continuous α c).stronglyMeasurable.mul hf).const_smul (T^(-ε))

theorem a03SixTensorLogPoint_measurable : Measurable a03SixTensorLogPoint := by
  exact (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun j =>
    Real.measurable_log.comp (measurable_pi_apply j))

theorem a03SixZeroSourceArguments_continuous (m n : Bool) (q : QuadraticScales)
    (v : Fin 5→ℕ) : Continuous (a03SixZeroSourceArguments m n q v) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact continuous_const
  · cases m <;> cases n <;> fin_cases i <;>
      simp [a03SixZeroSourceArguments,a03SixZeroPairArguments] <;>
      exact rectangularZeroArguments_continuous q v _

theorem a03SixTensorPhysicalZeroMode_mellin_stronglyMeasurable
    (F : ℝ→A03SixTensorSpace→ℂ)
    (hF : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace => F p.1 p.2))
    (m n : Bool) (q : QuadraticScales) (α β : ℕ→ℂ) :
    StronglyMeasurable (fun v : ℝ => a03SixTensorPhysicalZeroMode (F v) m n q α β) := by
  have hs : StronglyMeasurable (∑ w∈quadraticMainIndexSet q, fun v : ℝ => α (w 0)*β (w 1)*
      ∫ x : ℝ in Ioi 0, (∏ j : Fin 5,
        (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q w x j.succ):ℂ))*
          F v (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x))) := by
    apply Finset.stronglyMeasurable_sum
    intro w _
    apply StronglyMeasurable.const_mul
    have hargs := a03SixZeroSourceArguments_continuous m n q w
    have hy : Measurable (fun x : ℝ => a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x)) :=
      a03SixTensorLogPoint_measurable.comp hargs.measurable
    have hFm := hF.comp_measurable (measurable_fst.prodMk (hy.comp measurable_snd))
    have hweight : Continuous (fun p : ℝ×ℝ => ∏ j : Fin 5,
        (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q w p.2 j.succ):ℂ)) := by
      apply continuous_finsetProd
      intro j _
      exact Complex.continuous_ofReal.comp ((rectangularSmoothBlockWeight_contDiff.continuous).comp
        ((continuous_apply j.succ).comp (hargs.comp continuous_snd)))
    exact (hweight.stronglyMeasurable.mul hFm).integral_prod_right'
  convert hs using 1
  funext v
  simp only [Finset.sum_apply,a03SixTensorPhysicalZeroMode]

theorem a03EndpointPhysicalSortedZeroMode_mellin_stronglyMeasurable
    (F : ℝ→A03SixTensorSpace→ℂ)
    (hF : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace => F p.1 p.2))
    (T A B H : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ) :
    StronglyMeasurable (fun v : ℝ => a03EndpointPhysicalSortedZeroMode (F v) T A B H f g k) :=
  a03SixTensorPhysicalZeroMode_mellin_stronglyMeasurable F hF _ _ _ _ _

theorem a03EndpointPhysicalTensorSum_mellin_stronglyMeasurable
    (F : A03NearTensorData→A03SixTensorSpace→ℂ)
    (positive : Bool) (T A B H : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) (k : Fin 4→ℕ)
    (hF : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
      F (phaseActualNearTensorData T σ α p.1 A B H k positive) p.2)) :
    StronglyMeasurable (fun v : ℝ => a03EndpointPhysicalTensorSum F positive T A B H σ α v f g k) := by
  have hs : StronglyMeasurable (∑ n∈quadraticIndexSet (phaseActualScales A B H k), fun v : ℝ =>
      if signedQuadraticRelation positive n then
        phaseActualAmplifierCoefficient T f A (n 0)*phaseActualAmplifierCoefficient T g B (n 1)*
          (∏ j : Fin 5, (rectangularSmoothBlockWeight
            (rectangularWeightArguments (phaseActualScales A B H k) n j):ℂ))*
          F (phaseActualNearTensorData T σ α v A B H k positive)
            (a03SixTensorLogPoint (a03SixSourceArguments (phaseActualScales A B H k) n)) else 0) := by
    apply Finset.stronglyMeasurable_sum
    intro n _
    by_cases hr : signedQuadraticRelation positive n
    · simp only [hr,ite_true]
      exact (hF.comp_measurable (measurable_id.prodMk measurable_const)).const_mul _
    · simp only [hr,ite_false]
      exact stronglyMeasurable_const
  convert hs using 1
  funext v
  simp only [Finset.sum_apply,a03EndpointPhysicalTensorSum]

end
end SixthMoment
