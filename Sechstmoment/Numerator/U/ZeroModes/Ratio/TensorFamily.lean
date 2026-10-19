import Sechstmoment.Certificate.Scale
import Sechstmoment.Numerator.U.Sources.ErrorAggregate
import Sechstmoment.Numerator.U.ZeroModes.RatioEuclideanMultiplier
import Sechstmoment.Numerator.U.ZeroModes.SoftSourceFactory

/-! Genuine bounded Schwartz families for the actual original and dual
Gamma tensor times the two-root ratio multiplier. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000

structure A03RatioTensorData where
  base : A03NearTensorData
  tM : ℝ
  tN : ℝ

def A03RatioTensorValid (T0 θ κ R : ℝ) (p : A03RatioTensorData) : Prop :=
  A03DualNearTensorValid T0 θ κ R p.base

def a03ActualRatioTensorNormalizedKernel (dual : Bool) (Φ : ℝ→ℂ) (c e : ℝ)
    (p : A03RatioTensorData) (y : A03SixTensorSpace) : ℂ :=
  a03RatioNormalizedMultiplier (2*e/3) p.base.T p.base.σ p.tM p.tN y*
    a03SourceKernel dual Φ c (e/3) p.base y

def a03ActualRatioTensorRawKernel (dual : Bool) (Φ : ℝ→ℂ) (c : ℝ)
    (p : A03RatioTensorData) (y : A03SixTensorSpace) : ℂ :=
  a03RatioEuclideanMultiplier (rawMomentShifts p.base.T p.base.σ) p.tM p.tN y*
    a03SourceRawKernel dual Φ c p.base y

theorem a03ActualRatioTensorNormalizedKernel_eq {T : ℝ} (hT : 0<T)
    (dual : Bool) (Φ : ℝ→ℂ) (c e : ℝ) (p : A03RatioTensorData) (hp : p.base.T=T)
    (y : A03SixTensorSpace) :
    a03ActualRatioTensorNormalizedKernel dual Φ c e p y=
      ((T^(-e):ℝ):ℂ)*a03ActualRatioTensorRawKernel dual Φ c p y := by
  have hpow : T^(-(2*e/3))*T^(-(e/3))=T^(-e) := by
    rw [←Real.rpow_add hT]
    congr 1
    ring
  cases dual <;>
    simp only [a03ActualRatioTensorNormalizedKernel,a03ActualRatioTensorRawKernel,a03RatioNormalizedMultiplier,
      a03SourceKernel,a03SourceRawKernel,Bool.false_eq_true,ite_false,ite_true,
      a03ActualTensorNormalizedKernel,a03ActualDualTensorNormalizedKernel,Complex.real_smul,hp]
  all_goals
    have halg (X Y Z W : ℂ) : X*Y*(Z*W)=(X*Z)*(Y*W) := by ring
    rw [halg,←Complex.ofReal_mul,hpow]

theorem a03ActualRatioTensorNormalizedKernel_restore {T : ℝ} (hT : 0<T)
    (dual : Bool) (Φ : ℝ→ℂ) (c e : ℝ) (p : A03RatioTensorData) (hp : p.base.T=T)
    (y : A03SixTensorSpace) :
    ((T^e:ℝ):ℂ)*a03ActualRatioTensorNormalizedKernel dual Φ c e p y=
      a03ActualRatioTensorRawKernel dual Φ c p y := by
  rw [a03ActualRatioTensorNormalizedKernel_eq hT dual Φ c e p hp y,←mul_assoc,
    ←Complex.ofReal_mul,←Real.rpow_add hT,add_neg_cancel,Real.rpow_zero,Complex.ofReal_one,one_mul]

theorem a03_actual_source_kernel_uniform_local_bounds (dual : Bool)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c e κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (he : 4*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ B : ℕ→ℝ,(∀ n,0≤B n) ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v r s : ℝ,|v|≤θ*Real.log T → 0≤r → r≤1/100 → |s|=1 →
      let p : A03NearTensorData := ⟨T,σ,α,v,r,s⟩
      ContDiffOn ℝ ∞ (a03SourceKernel dual Φ c e p) a03SixGapDomain ∧
        ∀ n y,y∈tsupport a03TensorLogCutoff →
          ‖iteratedFDeriv ℝ n (a03SourceKernel dual Φ c e p) y‖≤B n := by
  cases dual
  · obtain ⟨B,hB,hb⟩ := a03_actual_tensor_normalized_uniform_local_bounds hΦ hΦs hc hc1 he hκ hθ
    refine ⟨B,hB,?_⟩
    filter_upwards [hb] with T hb
    intro σ α _hσ hα hroot v r s hv hr hr1 hs
    exact hb σ α hα hroot v r s hv hr hr1 hs
  · simpa only [a03SourceKernel,ite_true] using
      a03_actual_dual_tensor_normalized_uniform_local_bounds hΦ hΦs hc hc1 he hκ hθ hR

theorem a03_actual_ratio_tensor_uniform_local_bounds (dual : Bool)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c e κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ B : ℕ→ℝ,(∀ n,0≤B n) ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v r s : ℝ,|v|≤θ*Real.log T → 0≤r → r≤1/100 → |s|=1 →
      ∀ tM tN : ℝ,let p : A03RatioTensorData := ⟨⟨T,σ,α,v,r,s⟩,tM,tN⟩
      ContDiffOn ℝ ∞ (a03ActualRatioTensorNormalizedKernel dual Φ c e p) a03SixGapDomain ∧
        ∀ n y,y∈tsupport a03TensorLogCutoff →
          ‖iteratedFDeriv ℝ n (a03ActualRatioTensorNormalizedKernel dual Φ c e p) y‖≤B n := by
  have he3 : 4*c<e/3 := by linarith
  have hδ : 0<2*e/3 := by linarith
  obtain ⟨B,hB,hb⟩ := a03_actual_source_kernel_uniform_local_bounds dual hΦ hΦs hc hc1 he3 hκ hθ hR
  let A : ℕ→ℝ := a03RatioSubpowerDerivativeBudget (2*e/3) κ
  have hA (n : ℕ) : 0≤A n := a03RatioSubpowerDerivativeBudget_nonneg hδ κ n
  let D := phaseLocalizedKernelDerivativeBudget A B
  have hD (n : ℕ) : 0≤D n :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB (n-i)))
  refine ⟨D,hD,?_⟩
  filter_upwards [hb,eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hb hT hlog
  intro σ α hσ hα hroot v r s hv hr hr1 hs tM tN
  let p : A03NearTensorData := ⟨T,σ,α,v,r,s⟩
  let f := a03RatioNormalizedMultiplier (2*e/3) T σ tM tN
  let g := a03SourceKernel dual Φ c (e/3) p
  have hf : ContDiff ℝ ∞ f := a03RatioNormalizedMultiplier_contDiff _ _ _ _ _
  have hg := hb σ α hσ hα hroot v r s hv hr hr1 hs
  refine ⟨hf.contDiffOn.mul hg.1,?_⟩
  intro n y hy
  have hyU := a03TensorLogCutoff_subset_gapDomain hy
  have hd := norm_iteratedFDerivWithin_mul_le hf.contDiffOn hg.1
    a03SixGapDomain_isOpen.uniqueDiffOn hyU (n:=n) (by simp)
  simp_rw [iteratedFDerivWithin_of_isOpen _ a03SixGapDomain_isOpen hyU] at hd
  apply hd.trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul (mul_le_mul_of_nonneg_left
    (a03RatioNormalizedMultiplier_uniform_derivative_bound hδ hT hlog hκ σ hroot tM tN i y) (Nat.cast_nonneg _))
    (hg.2 (n-i) y hy) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))

theorem a03_actual_ratio_tensor_bounded_schwartz_family (dual : Bool)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c e κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ T0 : ℝ,∃ kernels : {p : A03RatioTensorData // A03RatioTensorValid T0 θ κ R p}→SchwartzMap A03SixTensorSpace ℂ,
      (∀ p y,kernels p y=a03TensorLogCutoff y*a03ActualRatioTensorNormalizedKernel dual Φ c e p.val y) ∧
      ∀ k n : ℕ,∃ C : ℝ,0≤C ∧ ∀ p,SchwartzMap.seminorm ℂ k n (kernels p)≤C := by
  obtain ⟨B,hB,hb⟩ := a03_actual_ratio_tensor_uniform_local_bounds dual hΦ hΦs hc hc1 he hκ hθ hR
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp hb
  let P : {p : A03RatioTensorData // A03RatioTensorValid T0 θ κ R p}→A03SixTensorSpace→ℂ :=
    fun p => a03ActualRatioTensorNormalizedKernel dual Φ c e p.val
  have hP (p : {p : A03RatioTensorData // A03RatioTensorValid T0 θ κ R p}) :
      ContDiffOn ℝ ∞ (P p) a03SixGapDomain := by
    rcases p.property with ⟨⟨_hT,hpT,hα,hroot,hv,hr,hr1,hs⟩,hσ⟩
    exact (hT0 p.val.base.T hpT p.val.base.σ p.val.base.α hσ hα hroot
      p.val.base.v p.val.base.r p.val.base.s hv hr hr1 hs p.val.tM p.val.tN).1
  have hPd (n : ℕ) (p : {p : A03RatioTensorData // A03RatioTensorValid T0 θ κ R p})
      (y : A03SixTensorSpace) (hy : y∈tsupport a03TensorLogCutoff) :
      ‖iteratedFDeriv ℝ n (P p) y‖≤B n := by
    rcases p.property with ⟨⟨_hT,hpT,hα,hroot,hv,hr,hr1,hs⟩,hσ⟩
    exact (hT0 p.val.base.T hpT p.val.base.σ p.val.base.α hσ hα hroot
      p.val.base.v p.val.base.r p.val.base.s hv hr hr1 hs p.val.tM p.val.tN).2 n y hy
  obtain ⟨kernels,hgraph,hseminorm⟩ := phase_localized_uniform_schwartz_family a03TensorLogCutoff
    a03TensorLogCutoff_contDiff a03TensorLogCutoff_hasCompactSupport
    a03SixGapDomain_isOpen a03TensorLogCutoff_subset_gapDomain P hP B hB hPd
    (by norm_num : (0:ℝ)≤3) (fun y hy => a03TensorLogCutoffBox_norm_bound (a03TensorLogCutoff_tsupport hy))
  exact ⟨T0,kernels,hgraph,hseminorm⟩

end
end Sechstmoment
