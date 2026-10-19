import Sechstmoment.Numerator.U.ZeroModes.Ratio.FullVStarNative
import Sechstmoment.Numerator.U.ZeroModes.Replacement.Identity

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 300000

theorem a03SixTensorPhysicalZeroMode_sub_weighted
    (F H G : A03SixTensorSpace→ℂ) (hG : Measurable G) {K : ℝ} (hGK : ∀ y,‖G y‖≤K)
    (m n : Bool) (q : QuadraticScales) (a b : ℕ→ℂ)
    (hF : ∀ v∈quadraticMainIndexSet q,IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
      F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) (Ioi 0))
    (hH : ∀ v∈quadraticMainIndexSet q,IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
      H (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) (Ioi 0)) :
    a03SixTensorPhysicalZeroMode (fun y => G y*(F y-H y)) m n q a b=
      a03SixTensorPhysicalZeroMode (fun y => G y*F y) m n q a b-
        a03SixTensorPhysicalZeroMode (fun y => G y*H y) m n q a b := by
  have hw (V : A03SixTensorSpace→ℂ)
      (hV : ∀ v∈quadraticMainIndexSet q,IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
        V (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) (Ioi 0))
      (v : Fin 5→ℕ) (hv : v∈quadraticMainIndexSet q) :
      IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q v x*
        (G (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))*
          V (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))) (Ioi 0) := by
    have hy : Measurable (fun x => a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)) :=
      a03SixTensorLogPoint_measurable.comp (a03SixZeroSourceArguments_continuous m n q v).measurable
    apply ((hV v hv).bdd_mul (hG.comp hy).aestronglyMeasurable (ae_of_all _ fun x => hGK _)).congr
    exact ae_of_all _ fun x => by dsimp only [Function.comp_apply]; ring
  have he := a03SixTensorPhysicalZeroMode_sub (fun y => G y*F y) (fun y => G y*H y)
    m n q a b (hw F hF) (hw H hH)
  simpa only [mul_sub] using he

theorem a03_actual_ratio_zero_eventually_sub_linear_eq_symbols
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j,‖α j‖≤1/4) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ dual : Bool,∀ r s tM tN : ℝ,
      ∀ m n : Bool,∀ q : QuadraticScales,0<q.M₂ → ∀ a b : ℕ→ℂ,
      let p : A03NearTensorData := ⟨T,σ,α,v,r,s⟩
      let G := a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN
      a03SixTensorPhysicalZeroMode (fun y => G y*a03SourceRawKernel dual Φ c p y) m n q a b-
        a03SixTensorPhysicalZeroMode (fun y => G y*a03ZeroModeLinearKernel dual Φ c p y) m n q a b=
        a03SixTensorPhysicalZeroMode (fun y => G y*a03ZeroModeReplacementKernel dual Φ c p y) m n q a b+
          a03SixTensorPhysicalZeroMode (fun y => G y*a03ZeroModeLinearizationKernel dual Φ c p y) m n q a b := by
  filter_upwards [a03_replacement_tensor_eventually_eq_actual_sub_leading hΦ hΦs hc hc1 hθ,
    a03_dual_replacement_tensor_eventually_eq_actual_sub_leading hΦ hΦs hc hc1 hκ hθ hR,
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    bblrGamma_logarithmic_strip_large hc.le hc1 hθ,eventually_ge_atTop (10:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hmain hdual hsmall hlarge hT hlog
  intro σ α hσ hα hroot v hv dual r s tM tN m n q hM₂ a b
  dsimp only
  let p : A03NearTensorData := ⟨T,σ,α,v,r,s⟩
  let G := a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN
  have hTp : 0<T := by linarith
  have hT1 : 1<T := by linarith
  have hGm : Measurable G := (a03RatioEuclideanMultiplier_contDiff _ _ _).continuous.measurable
  have hGK : ∀ y,‖G y‖≤a03RatioMultiplierDerivativeBudget κ 0*(Real.log T)^8 :=
    a03ActualRatioMultiplier_norm_le hT1 hlog hκ σ hroot tM tN
  have hF (w : Fin 5→ℕ) (hw : w∈quadraticMainIndexSet q) :
      IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q w x*
        a03SourceRawKernel dual Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x))) (Ioi 0) := by
    have hw1 (j : Fin 5) : 1≤w j := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
    cases dual
    · exact a03ActualTensorRawKernel_physical_term_integrable hΦ hΦs hc.le p hT hα (hlarge v hv) m n q hM₂ w hw1
    · exact a03ActualDualTensorRawKernel_physical_term_integrable hΦ hΦs hc.le p hT hα
        (hsmall σ hσ) (hlarge v hv) m n q hM₂ w hw1
  have hL (w : Fin 5→ℕ) (hw : w∈quadraticMainIndexSet q) :
      IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q w x*
        a03ZeroModeLeadingKernel dual Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x))) (Ioi 0) := by
    have hw1 (j : Fin 5) : 1≤w j := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
    cases dual
    · exact a03LeadingTensorRawKernel_physical_term_integrable hΦ.continuous hΦs hc.le p hTp hα m n q hM₂ w hw1
    · exact a03LeadingDualTensorRawKernel_physical_term_integrable hΦ.continuous hΦs hc.le p hTp hα m n q hM₂ w hw1
  have hV (w : Fin 5→ℕ) (hw : w∈quadraticMainIndexSet q) :
      IntegrableOn (fun x : ℝ => a03PhysicalZeroSmoothMask m n q w x*
        a03ZeroModeLinearKernel dual Φ c p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x))) (Ioi 0) := by
    have hw1 (j : Fin 5) : 1≤w j := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
    cases dual
    · exact a03LeadingLinearTensorRawKernel_physical_term_integrable hΦ.continuous hΦs hc.le p hTp hα m n q hM₂ w hw1
    · exact a03LeadingLinearDualTensorRawKernel_physical_term_integrable hΦ.continuous hΦs hc.le p hTp hα m n q hM₂ w hw1
  have hE : a03ZeroModeReplacementKernel dual Φ c p=(fun y => a03SourceRawKernel dual Φ c p y-a03ZeroModeLeadingKernel dual Φ c p y) := by
    funext y
    cases dual
    · exact hmain σ α hα v r s hv y
    · exact hdual σ α hσ hα hroot v r s hv y
  have he1 := a03SixTensorPhysicalZeroMode_sub_weighted _ _ G hGm hGK m n q a b hF hL
  have he2 := a03SixTensorPhysicalZeroMode_sub_weighted _ _ G hGm hGK m n q a b hL hV
  have hEpoint (y : A03SixTensorSpace) := congrFun hE y
  simp_rw [←hEpoint] at he1
  change a03SixTensorPhysicalZeroMode (fun y => G y*a03ZeroModeLinearizationKernel dual Φ c p y) m n q a b=_ at he2
  rw [he1,he2]
  ring

end
end Sechstmoment
