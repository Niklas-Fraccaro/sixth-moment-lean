import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import SixthMoment.Analysis.Fourier.ProfileDecay

namespace SixthMoment
open Complex Real MeasureTheory Set
open scoped ContDiff FourierTransform
noncomputable section
set_option maxHeartbeats 1000000

theorem a03_iteratedDeriv_tsupport_subset (f : ℝ → ℂ) (N : ℕ) :
    tsupport (iteratedDeriv N f)⊆tsupport f := by
  induction N with
  | zero => simp
  | succ N hN => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans hN

theorem a03_profile_frequency_derivative_integral {f : ℝ → ℂ}
    (hK : HasCompactSupport f) (hS : ContDiff ℝ ∞ f) (N : ℕ) (ξ : ℝ) :
    |ξ|^N*‖profileLaplaceTransform f ((ξ:ℂ)*I)‖≤
      ∫ x : ℝ, ‖iteratedDeriv N f x‖ := by
  have hI (n : ℕ) (_hn : (n:ℕ∞)≤⊤) : Integrable (iteratedDeriv n f) := by
    have hC := hS.continuous_iteratedDeriv n (by simp)
    apply hC.integrable_of_hasCompactSupport
    change IsCompact (tsupport (iteratedDeriv n f))
    exact hK.of_isClosed_subset (isClosed_tsupport _) (a03_iteratedDeriv_tsupport_subset f n)
  have hd := congrFun (Real.fourier_iteratedDeriv hS hI (n := N) (by simp)) (-ξ/(2*π))
  have hc : (2*π*I*((-ξ/(2*π):ℝ):ℂ):ℂ)=-(ξ:ℂ)*I := by
    push_cast
    field_simp
  have hn : ‖𝓕 (iteratedDeriv N f) (-ξ/(2*π))‖=
      |ξ|^N*‖𝓕 f (-ξ/(2*π))‖ := by
    rw [hd,norm_smul,hc,norm_pow,norm_mul,norm_neg,Complex.norm_real,
      Real.norm_eq_abs,Complex.norm_I,mul_one]
  have hf : profileLaplaceTransform f ((ξ:ℂ)*I)=𝓕 f (-ξ/(2*π)) := by
    have hwt : profileExponentialWeight f 0=f := by
      funext x
      simp [profileExponentialWeight]
    simpa only [Complex.ofReal_zero,zero_add,hwt] using profileLaplaceTransform_eq_fourier f 0 ξ
  rw [hf,← hn,Real.fourier_eq']
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with x
  rw [norm_smul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,zero_mul,sub_zero,Real.exp_zero,one_mul]

theorem a03_profile_frequency_dyadic_derivative_bound {f : ℝ → ℂ}
    (hS : ContDiff ℝ ∞ f) (hs : tsupport f⊆Icc 1 2) (N : ℕ) {B : ℝ}
    (hB : ∀ x, ‖iteratedDeriv N f x‖≤B) (ξ : ℝ) :
    |ξ|^N*‖profileLaplaceTransform f ((ξ:ℂ)*I)‖≤B := by
  have hK : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  apply (a03_profile_frequency_derivative_integral hK hS N ξ).trans
  have hsub := (a03_iteratedDeriv_tsupport_subset f N).trans hs
  have he : (∫ x : ℝ, ‖iteratedDeriv N f x‖)=
      ∫ x : ℝ in Icc 1 2, ‖iteratedDeriv N f x‖ := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Icc (1:ℝ) 2
    · simp only [indicator_of_mem hx]
    · have hzero : iteratedDeriv N f x=0 := by
        apply Function.notMem_support.mp
        exact fun hh => hx (hsub (subset_tsupport _ hh))
      simp only [indicator_of_notMem hx,hzero,norm_zero]
  rw [he]
  have hi : IntegrableOn (fun x : ℝ => ‖iteratedDeriv N f x‖) (Icc 1 2) := by
    exact ((hS.continuous_iteratedDeriv N (by simp)).norm.integrableOn_Icc)
  calc
    _ ≤ ∫ _x : ℝ in Icc (1:ℝ) 2, B :=
      integral_mono hi (integrableOn_const (measure_Icc_lt_top.ne)) hB
    _ = B := by norm_num [Real.volume_real_Icc]

end
end SixthMoment
