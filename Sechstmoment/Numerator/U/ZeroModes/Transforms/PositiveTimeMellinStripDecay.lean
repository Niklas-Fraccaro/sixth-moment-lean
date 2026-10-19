import Mathlib.Analysis.Calculus.ContDiff.Basic
import Sechstmoment.Numerator.U.ZeroModes.Transforms.PositiveTimeMellinDecay

/-! Uniform full-height Mellin decay on a compact real strip. The parameter
dependence of every time derivative is proved from the actual smooth profile. -/
namespace Sechstmoment
open Complex Real Set MeasureTheory
open scoped Topology ContDiff FourierTransform
noncomputable section
set_option maxHeartbeats 2000000

theorem a03PositiveTimeLogProfile_iteratedDeriv_joint_continuous {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (N : ℕ) :
    Continuous (fun p : ℝ×ℝ => iteratedDeriv N (a03PositiveTimeLogProfile Φ p.1) p.2) := by
  let F : ℝ×ℝ→ℂ := fun p => (Real.exp (-p.1*p.2):ℂ)*Φ (Real.exp (-p.2))
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.mul
    · exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (by fun_prop))
    · exact hΦ.comp (Real.contDiff_exp.comp (by fun_prop))
  let g : ℝ→L[ℝ] ℝ×ℝ := ContinuousLinearMap.inr ℝ ℝ ℝ
  have he (a u : ℝ) : iteratedDeriv N (a03PositiveTimeLogProfile Φ a) u=
      iteratedFDeriv ℝ N F (a,u) (fun _ : Fin N => (0,1)) := by
    have hf : a03PositiveTimeLogProfile Φ a=(fun p : ℝ×ℝ => F ((a,0)+p)) ∘ g := by
      funext u
      simp [F,g,a03PositiveTimeLogProfile]
    have hFa : ContDiff ℝ ∞ (fun p : ℝ×ℝ => F ((a,0)+p)) :=
      hF.comp (contDiff_const.add contDiff_id)
    rw [hf,iteratedDeriv_eq_iteratedFDeriv,
      g.iteratedFDeriv_comp_right hFa u (by simp),
      iteratedFDeriv_comp_add_left]
    simp [g,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hj : Continuous (fun p : ℝ×ℝ => iteratedFDeriv ℝ N F p (fun _ : Fin N => (0,1))) :=
    (continuous_eval_const _).comp (hF.continuous_iteratedFDeriv (by simp))
  exact hj.congr (fun p => (he p.1 p.2).symm)

theorem a03PositiveTimeLogProfile_uniform_derivative_bound {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (A B : ℝ) (N : ℕ) :
    ∃ D : ℝ,0≤D ∧ ∀ a∈Icc A B,∀ u : ℝ,
      ‖iteratedDeriv N (a03PositiveTimeLogProfile Φ a) u‖≤D := by
  have hj := a03PositiveTimeLogProfile_iteratedDeriv_joint_continuous hΦ N
  obtain ⟨D,hD⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s:=Icc A B ×ˢ Icc (-Real.log 2) 0) hj.continuousOn
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro a ha u
  by_cases hu : u∈Icc (-Real.log 2) 0
  · exact (hD (a,u) ⟨ha,hu⟩).trans (le_max_left _ _)
  · have hz : iteratedDeriv N (a03PositiveTimeLogProfile Φ a) u=0 := by
      apply Function.notMem_support.mp
      intro hn
      exact hu ((a03PositiveTimeLogProfile_support hSupp a)
        ((a03_iteratedDeriv_tsupport_subset _ N) (subset_tsupport _ hn)))
    rw [hz,norm_zero]
    exact le_max_right _ _

theorem a03PositiveTimeLogProfile_uniform_frequency_power_bound {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (A B : ℝ) (N : ℕ) :
    ∃ D : ℝ,0≤D ∧ ∀ a∈Icc A B,∀ ξ : ℝ,
      |ξ|^N*‖profileLaplaceTransform (a03PositiveTimeLogProfile Φ a) ((ξ:ℂ)*I)‖≤D := by
  obtain ⟨D,hD,hbound⟩ := a03PositiveTimeLogProfile_uniform_derivative_bound hΦ hSupp A B N
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨D*Real.log 2,mul_nonneg hD hlog.le,?_⟩
  intro a ha ξ
  have hK := a03PositiveTimeLogProfile_compact hSupp a
  have hS := a03PositiveTimeLogProfile_contDiff hΦ a
  apply (a03_profile_frequency_derivative_integral hK hS N ξ).trans
  have he : (∫u:ℝ,‖iteratedDeriv N (a03PositiveTimeLogProfile Φ a) u‖)=
      ∫u:ℝ in Icc (-Real.log 2) 0,‖iteratedDeriv N (a03PositiveTimeLogProfile Φ a) u‖ := by
    rw [←integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    apply ae_of_all
    intro u
    by_cases hu : u∈Icc (-Real.log 2) 0
    · simp only [indicator_of_mem hu]
    · have hz : iteratedDeriv N (a03PositiveTimeLogProfile Φ a) u=0 := by
        apply Function.notMem_support.mp
        intro hn
        exact hu ((a03PositiveTimeLogProfile_support hSupp a)
          ((a03_iteratedDeriv_tsupport_subset _ N) (subset_tsupport _ hn)))
      simp only [indicator_of_notMem hu,hz,norm_zero]
  rw [he]
  have hi : IntegrableOn (fun u : ℝ => ‖iteratedDeriv N (a03PositiveTimeLogProfile Φ a) u‖)
      (Icc (-Real.log 2) 0) := (hS.continuous_iteratedDeriv N (by simp)).norm.integrableOn_Icc
  calc
    _≤∫_u:ℝ in Icc (-Real.log 2) 0,D := integral_mono hi (integrableOn_const (measure_Icc_lt_top.ne)) (hbound a ha)
    _=D*Real.log 2 := by simp [Real.volume_real_Icc,max_eq_left hlog.le,mul_comm]

/-- Uniform in a complete compact real-part interval and in all imaginary
heights, with constants derived from the original fixed smooth profile. -/
theorem a03PositiveTimeMellin_strip_full_height_decay {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (A B : ℝ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ a∈Icc A B,∀ v : ℝ,
      (1+|v|)^N*‖mellin Φ ((a:ℂ)+(v:ℂ)*I)‖≤C := by
  obtain ⟨D,hD,hdb⟩ := a03PositiveTimeLogProfile_uniform_frequency_power_bound hΦ hSupp A B N
  obtain ⟨E,hE,heb⟩ := a03PositiveTimeLogProfile_uniform_frequency_power_bound hΦ hSupp A B 0
  refine ⟨2^N*(D+E),by positivity,?_⟩
  intro a ha v
  have hd := hdb a ha (-v)
  have he := heb a ha (-v)
  simp only [abs_neg,pow_zero,one_mul] at hd he
  rw [a03PositiveTimeMellin_eq_laplace]
  have hp : (1+|v|)^N≤2^N*(1+|v|^N) := by
    by_cases hv : |v|≤1
    · calc
        _≤(2:ℝ)^N := pow_le_pow_left₀ (by positivity) (by linarith only [hv]) N
        _≤_ := by nlinarith only [pow_nonneg (abs_nonneg v) N,pow_nonneg (by norm_num : (0:ℝ)≤2) N]
    · have hv' : 1≤|v| := le_of_lt (lt_of_not_ge hv)
      calc
        _≤(2*|v|)^N := pow_le_pow_left₀ (by positivity) (by linarith only [hv']) N
        _=2^N*|v|^N := mul_pow _ _ _
        _≤_ := by nlinarith only [pow_nonneg (abs_nonneg v) N,pow_nonneg (by norm_num : (0:ℝ)≤2) N]
  calc
    _≤2^N*(1+|v|^N)*‖profileLaplaceTransform (a03PositiveTimeLogProfile Φ a) (((-v:ℝ):ℂ)*I)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _≤2^N*(D+E) := by nlinarith only [hd,he,pow_nonneg (by norm_num : (0:ℝ)≤2) N]

end
end Sechstmoment
