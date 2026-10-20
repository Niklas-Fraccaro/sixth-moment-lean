import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Sechstmoment.Numerator.U.ZeroModes.Transforms.ComplexLaplaceGamma
import Sechstmoment.Numerator.U.ZeroModes.Transforms.SmoothedCosineMellin


namespace Sechstmoment.Source
open Complex Real Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option maxHeartbeats 0

def a03CosineGammaKernel (s : ℂ) (ε t : ℝ) : ℂ :=
  (((ε:ℂ)-(t:ℂ)*I)^(-s)+((ε:ℂ)+(t:ℂ)*I)^(-s))/2*Complex.Gamma s

theorem a03CosineGammaKernel_zero (s : ℂ) {t : ℝ} (ht : 0<t) :
    a03CosineGammaKernel s 0 t=
      Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*(t:ℂ)^(-s) := by
  have ht0 : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hp : ((t:ℂ)*I)^(-s)=
      (t:ℂ)^(-s)*Complex.exp (-(((Real.pi:ℂ)*s/2)*I)) := by
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero ht0 Complex.I_ne_zero),
      Complex.log_ofReal_mul ht Complex.I_ne_zero,Complex.log_I,add_mul,Complex.exp_add,
      Complex.cpow_def_of_ne_zero ht0,←Complex.ofReal_log ht.le]
    congr 2
    ring
  have hn : ((t:ℂ)*(-I))^(-s)=
      (t:ℂ)^(-s)*Complex.exp (((Real.pi:ℂ)*s/2)*I) := by
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero ht0 (neg_ne_zero.mpr Complex.I_ne_zero)),
      Complex.log_ofReal_mul ht (neg_ne_zero.mpr Complex.I_ne_zero),Complex.log_neg_I,
      add_mul,Complex.exp_add,Complex.cpow_def_of_ne_zero ht0,←Complex.ofReal_log ht.le]
    congr 2
    ring
  unfold a03CosineGammaKernel
  simp only [Complex.ofReal_zero,zero_sub,zero_add]
  rw [show -((t:ℂ)*I)=(t:ℂ)*(-I) by ring,hn,hp]
  unfold Complex.cos
  ring

theorem a03CosineGammaKernel_continuous_time (s : ℂ) {ε : ℝ} (hε : 0<ε) :
    Continuous (a03CosineGammaKernel s ε) := by
  have hminus : Continuous (fun t : ℝ => (ε:ℂ)-(t:ℂ)*I) := by fun_prop
  have hplus : Continuous (fun t : ℝ => (ε:ℂ)+(t:ℂ)*I) := by fun_prop
  have hm := hminus.cpow (continuous_const (y:= -s)) (fun t =>
    (show (ε:ℂ)-(t:ℂ)*I∈Complex.slitPlane from Or.inl (by simpa using hε)))
  have hp := hplus.cpow (continuous_const (y:= -s)) (fun t =>
    (show (ε:ℂ)+(t:ℂ)*I∈Complex.slitPlane from Or.inl (by simpa using hε)))
  exact ((hm.add hp).div_const 2).mul_const (Complex.Gamma s)

theorem a03CosineGammaKernel_compact_bound (s : ℂ) :
    ∃ C : ℝ,0≤C ∧ ∀ ε∈Icc (0:ℝ) 1,∀ t∈Icc (1:ℝ) 2,
      ‖a03CosineGammaKernel s ε t‖≤C := by
  have hminus : Continuous (fun x : ℝ × ℝ => (x.1:ℂ)-(x.2:ℂ)*I) := by fun_prop
  have hplus : Continuous (fun x : ℝ × ℝ => (x.1:ℂ)+(x.2:ℂ)*I) := by fun_prop
  have hm : ContinuousOn (fun x : ℝ × ℝ => ((x.1:ℂ)-(x.2:ℂ)*I)^(-s))
      (Icc (0:ℝ) 1 ×ˢ Icc (1:ℝ) 2) := hminus.continuousOn.cpow_const (by
        intro x hx
        right
        simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
          Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_sub]
        have ht : 0<x.2 := lt_of_lt_of_le (by norm_num) hx.2.1
        exact neg_ne_zero.mpr ht.ne')
  have hp : ContinuousOn (fun x : ℝ × ℝ => ((x.1:ℂ)+(x.2:ℂ)*I)^(-s))
      (Icc (0:ℝ) 1 ×ˢ Icc (1:ℝ) 2) := hplus.continuousOn.cpow_const (by
        intro x hx
        right
        simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
          Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
        exact (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hx.2.1).ne')
  have hc : ContinuousOn (fun x : ℝ × ℝ => a03CosineGammaKernel s x.1 x.2)
      (Icc (0:ℝ) 1 ×ˢ Icc (1:ℝ) 2) :=
    ((hm.add hp).div_const 2).mul_const (Complex.Gamma s)
  obtain ⟨D,hD⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro ε hε t ht
  exact (hD (ε,t) ⟨hε,ht⟩).trans (le_max_left _ _)

theorem a03CosineGammaKernel_abel_tendsto (s : ℂ) {t : ℝ} (ht : 0<t) :
    Tendsto (fun n : ℕ => a03CosineGammaKernel s (a03CosineAbelScale n) t) atTop
      (𝓝 (Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*(t:ℂ)^(-s))) := by
  have hε := a03CosineAbelScale_tendsto_zero.ofReal
  have hminus := hε.sub_const ((t:ℂ)*I)
  have hplus := hε.add_const ((t:ℂ)*I)
  have ht0 : t≠0 := ht.ne'
  have hm := hminus.cpow (tendsto_const_nhds : Tendsto (fun _ : ℕ => -s) atTop (𝓝 (-s)))
    (show (0:ℂ)-(t:ℂ)*I∈Complex.slitPlane from Or.inr (by simpa using neg_ne_zero.mpr ht0))
  have hp := hplus.cpow (tendsto_const_nhds : Tendsto (fun _ : ℕ => -s) atTop (𝓝 (-s)))
    (show (0:ℂ)+(t:ℂ)*I∈Complex.slitPlane from Or.inr (by simpa using ht0))
  have h := ((hm.add hp).div_const (2:ℂ)).mul_const (Complex.Gamma s)
  change Tendsto (fun n : ℕ => a03CosineGammaKernel s (a03CosineAbelScale n) t) atTop
    (𝓝 (a03CosineGammaKernel s 0 t)) at h
  rw [a03CosineGammaKernel_zero s ht] at h
  exact h

theorem a03CosineGamma_time_integral_tendsto (s : ℂ) {Φ : ℝ→ℂ}
    (hΦ : Continuous Φ) (hK : HasCompactSupport Φ)
    (hSupp : ∀ t : ℝ,t∉Icc (1:ℝ) 2 → Φ t=0) :
    Tendsto (fun n : ℕ => ∫ t : ℝ,Φ t*a03CosineGammaKernel s (a03CosineAbelScale n) t) atTop
      (𝓝 (Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*
        ∫ t : ℝ,Φ t*(t:ℂ)^(-s))) := by
  obtain ⟨C,_hC,hb⟩ := a03CosineGammaKernel_compact_bound s
  have hε (n : ℕ) : a03CosineAbelScale n∈Icc (0:ℝ) 1 := by
    constructor
    · exact (a03CosineAbelScale_positive n).le
    · unfold a03CosineAbelScale
      apply (div_le_one₀ (by positivity)).mpr
      linarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun t : ℝ => Φ t*a03CosineGammaKernel s (a03CosineAbelScale n) t) volume :=
    (hΦ.mul (a03CosineGammaKernel_continuous_time s (a03CosineAbelScale_positive n))).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ t : ℝ,‖Φ t*a03CosineGammaKernel s (a03CosineAbelScale n) t‖≤C*‖Φ t‖ := by
    apply ae_of_all
    intro t
    by_cases ht : t∈Icc (1:ℝ) 2
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb _ (hε n) t ht) (norm_nonneg _)).trans_eq (mul_comm _ _)
    · simp [hSupp t ht]
  have hlim : ∀ᵐ t : ℝ,Tendsto (fun n : ℕ => Φ t*a03CosineGammaKernel s (a03CosineAbelScale n) t)
      atTop (𝓝 (Φ t*(Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*(t:ℂ)^(-s)))) := by
    apply ae_of_all
    intro t
    by_cases ht : t∈Icc (1:ℝ) 2
    · exact (a03CosineGammaKernel_abel_tendsto s (lt_of_lt_of_le (by norm_num) ht.1)).const_mul (Φ t)
    · simp only [hSupp t ht,zero_mul]
      exact tendsto_const_nhds
  have h := tendsto_integral_of_dominated_convergence (fun t : ℝ => C*‖Φ t‖)
    hmeas ((hΦ.integrable_of_hasCompactSupport hK).norm.const_mul C) hbound hlim
  have he : (∫ t : ℝ,Φ t*(Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*(t:ℂ)^(-s)))=
      Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*(∫ t : ℝ,Φ t*(t:ℂ)^(-s)) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro t
    ring
  rw [he] at h
  exact h

end
end Sechstmoment.Source
