import Sechstmoment.Numerator.U.Separation.Frequency.SixDualComposition
import Sechstmoment.Numerator.U.Separation.Tensor.Kernel

namespace Sechstmoment
open Complex Real Source Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology FourierTransform
noncomputable section
set_option maxHeartbeats 2000000

def A03DualNearTensorValid (T0 θ κ R : ℝ) (p : A03NearTensorData) : Prop :=
  A03NearTensorValid T0 θ κ p ∧ (∀ j, ‖p.σ j‖ ≤ R)

def a03ActualDualTensorRawKernel (Φ : ℝ → ℂ) (c : ℝ) (p : A03NearTensorData)
    (y : A03SixTensorSpace) : ℂ :=
  a03TensorMellinFactor p.α ((c : ℂ)+(p.v : ℂ)*I) y *
    a03SixGaussianDualFrequencyKernel Φ p.T p.σ p.α ((c : ℂ)+(p.v : ℂ)*I) p.r p.s y

def a03ActualDualTensorNormalizedKernel (Φ : ℝ → ℂ) (c ε : ℝ)
    (p : A03NearTensorData) (y : A03SixTensorSpace) : ℂ :=
  (p.T^(-ε)) • a03ActualDualTensorRawKernel Φ c p y

theorem a03_actual_dual_tensor_normalized_uniform_local_bounds
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    {c ε κ θ R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 4*c < ε)
    (hκ : 0 < κ) (hθ : 0 ≤ θ) (hR : 0 ≤ R) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ α : MomentShifts, (∀ j, ‖σ j‖ ≤ R) → (∀ j, ‖α j‖ ≤ 1/4) →
      (∀ j : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ j‖) →
      ∀ v r s : ℝ, |v| ≤ θ*Real.log T → 0 ≤ r → r ≤ 1/100 → |s| = 1 →
      let p : A03NearTensorData := ⟨T,σ,α,v,r,s⟩
      ContDiffOn ℝ ∞ (a03ActualDualTensorNormalizedKernel Φ c ε p) a03SixGapDomain ∧
        ∀ n y, y ∈ tsupport a03TensorLogCutoff →
          ‖iteratedFDeriv ℝ n (a03ActualDualTensorNormalizedKernel Φ c ε p) y‖ ≤ B n := by
  have hεhalf : 0 < ε/2 := by linarith
  have hchalf : 2*c < ε/2 := by linarith
  obtain ⟨M,hM,hMd⟩ := a03TensorMellinFactor_logarithmic_uniform_derivative_bounds hεhalf hθ
  obtain ⟨F,hF,hFd⟩ := a03_six_gaussian_dual_frequency_uniform_bounds hΦ hΦs hc hc1 hchalf hκ hθ
    (by norm_num : (0 : ℝ) ≤ 1/4) hR
  let B := phaseLocalizedKernelDerivativeBudget M F
  have hB (n : ℕ) : 0 ≤ B n := by
    unfold B phaseLocalizedKernelDerivativeBudget
    exact Finset.sum_nonneg (fun i _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hM i)) (hF (n-i)))
  refine ⟨B,hB,?_⟩
  filter_upwards [hFd, eventually_ge_atTop (1 : ℝ)] with T hfreq hT
  intro σ α hσ hα hroot v r s hv hr hr1 hs
  let p : A03NearTensorData := ⟨T,σ,α,v,r,s⟩
  let m := a03TensorMellinFactor α ((c : ℂ)+(v : ℂ)*I)
  let g := a03SixGaussianDualFrequencyKernel Φ T σ α ((c : ℂ)+(v : ℂ)*I) r s
  have hm : ContDiff ℝ ∞ m := a03TensorMellinFactor_contDiff α _
  have hg : ContDiffOn ℝ ∞ g a03SixGapDomain := (hfreq σ α hσ hα hroot v r s hv hr hr1 hs).1
  have hprod : ContDiffOn ℝ ∞ (fun y => m y*g y) a03SixGapDomain := hm.contDiffOn.mul hg
  have hnorm : ContDiffOn ℝ ∞ (a03ActualDualTensorNormalizedKernel Φ c ε p) a03SixGapDomain := by
    have hconst : ContDiffOn ℝ ∞ (fun _ : A03SixTensorSpace => T^(-ε)) a03SixGapDomain :=
      contDiffOn_const
    exact hconst.smul hprod
  refine ⟨hnorm, ?_⟩
  intro n y hy
  have hyU := a03TensorLogCutoff_subset_gapDomain hy
  have hybox := a03TensorLogCutoff_tsupport hy
  have hd := norm_iteratedFDerivWithin_mul_le hm.contDiffOn hg
    a03SixGapDomain_isOpen.uniqueDiffOn hyU (n := n) (by simp)
  simp_rw [iteratedFDerivWithin_of_isOpen _ a03SixGapDomain_isOpen hyU] at hd
  have hbprod : ‖iteratedFDeriv ℝ n (fun y => m y*g y) y‖ ≤ B n*T^ε := by
    apply hd.trans
    calc
      _ ≤ ∑ i∈Finset.range (n+1), (n.choose i : ℝ)*(M i*T^(ε/2))*(F (n-i)*T^(ε/2)) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hMd T hT α hα c hc.le hc1 v hv i y hybox)
            (Nat.cast_nonneg _))
          ((hfreq σ α hσ hα hroot v r s hv hr hr1 hs).2 (n-i) y hyU)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hM i) (by positivity)))
      _ = B n*T^ε := by
        have he : T^(ε/2)*T^(ε/2) = T^ε := by
          rw [← Real.rpow_add (zero_lt_one.trans_le hT)]
          congr 1
          ring
        simp only [B,phaseLocalizedKernelDerivativeBudget,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = ((n.choose i : ℝ)*M i*F (n-i))*(T^(ε/2)*T^(ε/2)) := by ring
          _ = _ := by rw [he]
  have hpAt := (hprod y hyU).contDiffAt (a03SixGapDomain_isOpen.mem_nhds hyU)
  change ‖iteratedFDeriv ℝ n (fun y => T^(-ε) • (m y*g y)) y‖ ≤ B n
  rw [iteratedFDeriv_const_smul_apply' (hpAt.of_le (by simp)), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hT) _)]
  calc
    _ ≤ T^(-ε)*(B n*T^ε) :=
      mul_le_mul_of_nonneg_left hbprod (Real.rpow_nonneg (zero_le_one.trans hT) _)
    _ = B n := by
      rw [mul_left_comm, ← Real.rpow_add (zero_lt_one.trans_le hT), neg_add_cancel,
        Real.rpow_zero, mul_one]

theorem a03_actual_dual_tensor_bounded_schwartz_family
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    {c ε κ θ R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 4*c < ε)
    (hκ : 0 < κ) (hθ : 0 ≤ θ) (hR : 0 ≤ R) :
    ∃ T0 : ℝ, ∃ f : {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p} →
        SchwartzMap A03SixTensorSpace ℂ,
      (∀ p y, f p y = a03TensorLogCutoff y*a03ActualDualTensorNormalizedKernel Φ c ε p.val y) ∧
      ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p,
        SchwartzMap.seminorm ℂ k n (f p) ≤ C := by
  obtain ⟨B,hB,hfuture⟩ := a03_actual_dual_tensor_normalized_uniform_local_bounds
    hΦ hΦs hc hc1 hε hκ hθ hR
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp hfuture
  let P := fun p : {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p} =>
    a03ActualDualTensorNormalizedKernel Φ c ε p.val
  have hp (p : {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p}) := p.property
  have hP (p : {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p}) :
      ContDiffOn ℝ ∞ (P p) a03SixGapDomain := by
    rcases hp p with ⟨⟨_hT,hT0p,hα,hroot,hv,hr,hr1,hs⟩,hσ⟩
    exact (hT0 p.val.T hT0p p.val.σ p.val.α hσ hα hroot p.val.v p.val.r p.val.s hv hr hr1 hs).1
  have hPd (n : ℕ) (p : {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p})
      (y : A03SixTensorSpace) (hy : y ∈ tsupport a03TensorLogCutoff) :
      ‖iteratedFDeriv ℝ n (P p) y‖ ≤ B n := by
    rcases hp p with ⟨⟨_hT,hT0p,hα,hroot,hv,hr,hr1,hs⟩,hσ⟩
    exact (hT0 p.val.T hT0p p.val.σ p.val.α hσ hα hroot p.val.v p.val.r p.val.s hv hr hr1 hs).2 n y hy
  obtain ⟨f,hfeq,hfb⟩ := phase_localized_uniform_schwartz_family a03TensorLogCutoff
    a03TensorLogCutoff_contDiff a03TensorLogCutoff_hasCompactSupport
    a03SixGapDomain_isOpen a03TensorLogCutoff_subset_gapDomain P hP B hB hPd
    (by norm_num : (0 : ℝ) ≤ 3)
    (fun y hy => a03TensorLogCutoffBox_norm_bound (a03TensorLogCutoff_tsupport hy))
  exact ⟨T0,f,hfeq,hfb⟩

theorem a03_actual_dual_tensor_uniform_separation
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    {c ε κ θ R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 4*c < ε)
    (hκ : 0 < κ) (hθ : 0 ≤ θ) (hR : 0 ≤ R) :
    ∃ T0 : ℝ, ∃ f : {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p} →
        SchwartzMap A03SixTensorSpace ℂ,
      ∃ a : A03SixTensorSpace → ℝ, ∃ B : ℕ → ℝ, ∃ K : ℝ,
      (∀ p y, f p y = a03TensorLogCutoff y*a03ActualDualTensorNormalizedKernel Φ c ε p.val y) ∧
      Measurable a ∧ (∀ ν, 0 < a ν) ∧ (∀ j, 0 ≤ B j) ∧ 0 ≤ K ∧
      (∀ ν j, RectangularComplexWeight (a03SixTensorWeight a ν j)) ∧
      (∀ j ν i x, ‖iteratedDeriv j (a03SixTensorWeight a ν i) x‖ ≤ B j) ∧
      (∀ p, Integrable (a03SixTensorCoefficient (f p) a) ∧
        (∫ ν, ‖a03SixTensorCoefficient (f p) a ν‖) ≤ K) ∧
      (∀ p (x : Fin 6 → ℝ),
        (∀ j, x j ∈ Icc (1 : ℝ) 2) →
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (x j.succ) : ℂ)) *
          a03ActualDualTensorNormalizedKernel Φ c ε p.val (a03SixTensorLogPoint x) =
          ∫ ν, a03SixTensorCoefficient (f p) a ν *
            ((x 0 : ℂ)^a03SixTensorExponent ν 0 *
              ∏ j, a03SixTensorWeight a ν j (x j.succ))) := by
  obtain ⟨T0,f,hfeq,hfb⟩ := a03_actual_dual_tensor_bounded_schwartz_family hΦ hΦs hc hc1 hε hκ hθ hR
  obtain ⟨a,B,K,hm,ha,hB,hK,hW,hd,hcoef,heq⟩ := a03SixTensor_uniform_separation f hfb
  refine ⟨T0,f,a,B,K,hfeq,hm,ha,hB,hK,hW,hd,hcoef,?_⟩
  intro p x hx
  have h := heq p x (zero_lt_one.trans_le (hx 0).1)
  rw [hfeq p (a03SixTensorLogPoint x), a03TensorLogCutoff_logPoint_one hx, one_mul] at h
  exact h

end
end Sechstmoment
