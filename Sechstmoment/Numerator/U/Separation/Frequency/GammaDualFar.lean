import Sechstmoment.Numerator.U.Separation.Frequency.ActualFarIntegral
import Sechstmoment.Numerator.U.Separation.Frequency.GammaDualProfile

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def a03GaussianActualDualTimeIntegral (Φ : ℝ → ℂ) (T : ℝ) (σ α : MomentShifts)
    (z : ℂ) (a b : ℕ) (n : Fin 4 → ℕ) : ℂ :=
  ∫ t : ℝ, Φ (t/T)*(polarPoleKiller T σ z/z*(Real.pi:ℂ)^(-2*z)*
    bblrGammaQuotient t α z)*bblrDualMultiplier t (rawMomentShifts T σ)*rectangularTwistedQuadPhase t a b n

theorem a03_gaussian_actual_dual_time_exact_rescaling (Φ : ℝ → ℂ)
    {T : ℝ} (hT : 0<T) (σ α : MomentShifts) (z : ℂ)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (n : Fin 4 → ℕ) :
    a03GaussianActualDualTimeIntegral Φ T σ α z a b n=
      (T:ℂ)*a03GaussianDualFrequencyProfile Φ T σ α z
        (-T*Real.log (phaseActualProductRatio a b n)) := by
  have he : a03GaussianActualDualTimeIntegral Φ T σ α z a b n=
      phaseActualTimeIntegral (a03GaussianDualTimeProfile Φ T σ α z) T a b n := by
    unfold a03GaussianActualDualTimeIntegral phaseActualTimeIntegral
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [a03GaussianDualTimeProfile,a03ProfileProduct,bblrGaussianTimeAmplitude,
      mul_div_cancel₀ t hT.ne']
    ring
  rw [he,phase_actual_time_integral_eq_profile_unrestricted _ T ha hb,
    a03_profile_time_fourier_rescaling _ hT]
  unfold a03GaussianDualFrequencyProfile
  congr 2
  push_cast
  ring

theorem a03_gaussian_all_far_dual_uniform_rapid
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ A R ρ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ)
    (hθ : 0≤θ) (hA : 0≤A) (hR : 0≤R) (hρ : 0<ρ) (hρ1 : ρ≤1) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤A) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool, ∀ a b : ℕ, 0<a → 0<b →
      ∀ n : Fin 4 → ℕ,
      (if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n) →
      T^(ρ-1)*Real.sqrt ((a:ℝ)*b*(n 0+1)*(n 1+1)*(n 2+1)*(n 3+1))≤
        (rectangularAFEGap positive a b n:ℝ) →
      ‖a03GaussianActualDualTimeIntegral Φ T σ α ((c:ℂ)+(v:ℂ)*I) a b n‖≤C*T^(-M) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((M+1+ε)/ρ)
  have hexp : 1+ε-ρ*(N:ℝ)≤-M := by
    have h := (div_lt_iff₀ hρ).mp hN
    nlinarith
  obtain ⟨C,hC,hCd⟩ := a03_gaussian_dual_frequency_logarithmic_uniform_derivative_bounds
    hΦ hs hc hc1 hε hκ hθ hA hR
  refine ⟨C 0 N*8^N,mul_nonneg (hC 0 N) (by positivity),?_⟩
  filter_upwards [hCd,eventually_ge_atTop (1:ℝ)] with T hbT hT
  intro σ α hσ hα hroot v hv positive a b ha hb n hn hfar
  have hTp : 0<T := zero_lt_one.trans_le hT
  let ℓ : ℝ := Real.log (phaseActualProductRatio a b n)
  have hη : 0≤T^(ρ-1) := Real.rpow_nonneg hTp.le _
  have hη1 : T^(ρ-1)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by linarith)
  have hlog : T^(ρ-1)/8≤|ℓ| :=
    phase_actual_selected_far_log_lower positive ha hb n hn hη hη1 hfar
  have hfreq : T^ρ/8≤|-T*ℓ| := by
    have hm := mul_le_mul_of_nonneg_left hlog hTp.le
    have he : T*T^(ρ-1)=T^ρ := by
      calc
        _ = T^(1:ℝ)*T^(ρ-1) := by rw [Real.rpow_one]
        _ = T^ρ := by rw [← Real.rpow_add hTp]; congr 1; ring
    rw [abs_mul,abs_neg,abs_of_pos hTp]
    nlinarith
  have hbase : 0<T^ρ/8 := by positivity
  have hpow : 0<(T^ρ/8)^N := pow_pos hbase N
  have hF := (hbT σ α hσ hα hroot v hv).2 0 N (-T*ℓ)
  simp only [iteratedDeriv_zero] at hF
  have hFp : (T^ρ/8)^N*
      ‖a03GaussianDualFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I) (-T*ℓ)‖≤C 0 N*T^ε :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbase.le hfreq N) (norm_nonneg _)).trans hF
  have hnorm : ‖a03GaussianDualFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I) (-T*ℓ)‖≤
      (C 0 N*T^ε)/(T^ρ/8)^N := (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hFp)
  rw [a03_gaussian_actual_dual_time_exact_rescaling Φ hTp σ α _ ha hb,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hTp]
  calc
    _ ≤ T*((C 0 N*T^ε)/(T^ρ/8)^N) := mul_le_mul_of_nonneg_left hnorm hTp.le
    _ = (C 0 N*8^N)*T^(1+ε-ρ*(N:ℝ)) := by
      rw [div_pow,← Real.rpow_natCast,← Real.rpow_mul hTp.le,
        Real.rpow_sub hTp,Real.rpow_add hTp,Real.rpow_one]
      field_simp
    _ ≤ (C 0 N*8^N)*T^(-M) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT hexp)
        (mul_nonneg (hC 0 N) (by positivity))

end
end Sechstmoment
