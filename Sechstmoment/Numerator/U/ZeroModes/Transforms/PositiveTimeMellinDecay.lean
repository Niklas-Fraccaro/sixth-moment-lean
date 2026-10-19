import Mathlib.Analysis.MellinInversion
import Sechstmoment.Analysis.Fourier.UniformDecay

/-! Full-height decay of the actual compact positive-time Mellin integral. -/
namespace Sechstmoment
open Complex Real Set MeasureTheory
open scoped Topology ContDiff FourierTransform
noncomputable section
set_option maxHeartbeats 500000

def a03PositiveTimeLogProfile (Φ : ℝ→ℂ) (a : ℝ) (u : ℝ) : ℂ :=
  (Real.exp (-a*u):ℂ)*Φ (Real.exp (-u))

theorem a03PositiveTimeLogProfile_contDiff {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (a : ℝ) :
    ContDiff ℝ ∞ (a03PositiveTimeLogProfile Φ a) := by
  unfold a03PositiveTimeLogProfile
  exact (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))).mul
    (hΦ.comp (Real.contDiff_exp.comp contDiff_neg))

theorem a03PositiveTimeLogProfile_support {Φ : ℝ→ℂ}
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) (a : ℝ) :
    tsupport (a03PositiveTimeLogProfile Φ a)⊆Icc (-Real.log 2) 0 := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  have hφ : Φ (Real.exp (-u))≠0 := by
    intro hz
    exact hu (by simp [a03PositiveTimeLogProfile,hz])
  have hs := hSupp (subset_tsupport _ hφ)
  constructor
  · have hh := Real.log_le_log (Real.exp_pos (-u)) hs.2
    rw [Real.log_exp] at hh
    linarith only [hh]
  · have hh := Real.log_le_log (by norm_num : (0:ℝ)<1) hs.1
    rw [Real.log_one,Real.log_exp] at hh
    linarith only [hh]

theorem a03PositiveTimeLogProfile_compact {Φ : ℝ→ℂ}
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) (a : ℝ) :
    HasCompactSupport (a03PositiveTimeLogProfile Φ a) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (a03PositiveTimeLogProfile_support hSupp a)

theorem a03PositiveTimeMellin_eq_laplace (Φ : ℝ→ℂ) (a v : ℝ) :
    mellin Φ ((a:ℂ)+(v:ℂ)*I)=
      profileLaplaceTransform (a03PositiveTimeLogProfile Φ a) (((-v:ℝ):ℂ)*I) := by
  rw [mellin_eq_fourier]
  have he := profileLaplaceTransform_eq_fourier (a03PositiveTimeLogProfile Φ a) 0 (-v)
  simp only [Complex.ofReal_zero,zero_add] at he
  have hw : profileExponentialWeight (a03PositiveTimeLogProfile Φ a) 0=a03PositiveTimeLogProfile Φ a := by
    funext u
    simp [profileExponentialWeight]
  rw [hw] at he
  rw [he]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,sub_self,add_zero,Complex.add_im,Complex.mul_im,
    mul_one,zero_add,neg_neg]
  simp only [Complex.real_smul]
  rfl


/-- Arbitrary powers of the true Mellin height are controlled on every fixed
real line, including the lines with negative real part needed after reflection. -/
theorem a03PositiveTimeMellin_full_height_decay {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (a : ℝ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ v : ℝ,
      (1+|v|)^N*‖mellin Φ ((a:ℂ)+(v:ℂ)*I)‖≤C := by
  let f := a03PositiveTimeLogProfile Φ a
  have hK := a03PositiveTimeLogProfile_compact hSupp a
  have hS := a03PositiveTimeLogProfile_contDiff hΦ a
  obtain ⟨D,hD,hdb⟩ := a03_profile_frequency_power_bound hK hS N
  obtain ⟨E,hE,heb⟩ := a03_profile_frequency_power_bound hK hS 0
  refine ⟨2^N*(D+E),by positivity,?_⟩
  intro v
  have hd := hdb (-v)
  have he := heb (-v)
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
    _≤2^N*(1+|v|^N)*‖profileLaplaceTransform f (((-v:ℝ):ℂ)*I)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _≤2^N*(D+E) := by nlinarith only [hd,he,pow_nonneg (by norm_num : (0:ℝ)≤2) N]

end
end Sechstmoment
