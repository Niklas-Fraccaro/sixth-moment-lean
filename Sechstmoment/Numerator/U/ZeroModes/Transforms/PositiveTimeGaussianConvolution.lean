import Sechstmoment.Numerator.U.Replacement.VStar.Contours
import Sechstmoment.Numerator.U.ZeroModes.Transforms.PositiveTimeMellinStripDecay

namespace Sechstmoment
open Complex Real Source Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff FourierTransform
noncomputable section
set_option maxHeartbeats 700000

def a03GaussianPositiveTimeMellinIntegral (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts)
    (A a b ξ : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫v : ℝ,
    Complex.exp (-(1+(v:ℂ)*I)*(A:ℂ))*(polarPoleKiller T σ (1+(v:ℂ)*I)/(1+(v:ℂ)*I))*
      mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I)

private theorem weighted_triangle (b ξ v : ℝ) :
    1+|ξ|≤(1+|b|)*(1+|ξ+b*v|)*(1+|v|) := by
  have htri : |ξ|≤|ξ+b*v|+|b| * |v| := by
    simpa only [add_sub_cancel_right,abs_mul] using abs_sub (ξ+b*v) (b*v)
  nlinarith only [htri,abs_nonneg b,abs_nonneg v,abs_nonneg (ξ+b*v),
    mul_nonneg (abs_nonneg b) (abs_nonneg (ξ+b*v)),
    mul_nonneg (abs_nonneg v) (abs_nonneg (ξ+b*v)),
    mul_nonneg (mul_nonneg (abs_nonneg b) (abs_nonneg (ξ+b*v))) (abs_nonneg v)]

theorem a03PolarLineOneDiv_bound (T : ℝ) (σ : MomentShifts) (v : ℝ) :
    ‖polarPoleKiller T σ (1+(v:ℂ)*I)/(1+(v:ℂ)*I)‖≤
      polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-(1/2)*v^2) := by
  have hg := polarPoleKiller_vertical_norm_le T σ 1 v
  have hz : (1:ℝ)≤‖(1:ℂ)+(v:ℂ)*I‖ := by simpa using Complex.re_le_norm ((1:ℂ)+(v:ℂ)*I)
  rw [norm_div]
  calc
    _≤‖polarPoleKiller T σ (1+(v:ℂ)*I)‖/1 :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hz
    _≤polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-v^2) := by
      simpa only [div_one,Complex.ofReal_one] using hg
    _≤_ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [sq_nonneg v]))
      (mul_nonneg (polarGaussianConstant_nonneg T σ 1) (by positivity))

theorem a03GaussianPositiveTimeMellinIntegral_full_height_decay {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,∀ σ : MomentShifts,∀ A ξ : ℝ,
      (1+|ξ|)^N*‖a03GaussianPositiveTimeMellinIntegral Φ T σ A a b ξ‖≤
        C*polarGaussianConstant T σ 1*Real.exp (-A) := by
  obtain ⟨D,hD,hdec⟩ := a03PositiveTimeMellin_full_height_decay hΦ hSupp a N
  let C := (1/(2*Real.pi))*(1+|b|)^N*D*gaussianTailConstant (N+48)
  have hGaus := gaussianTailConstant_nonneg (N+48)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro T σ A ξ
  have hCG := polarGaussianConstant_nonneg T σ 1
  have hpoint (v : ℝ) :
      (1+|ξ|)^N*‖Complex.exp (-(1+(v:ℂ)*I)*(A:ℂ))*
        (polarPoleKiller T σ (1+(v:ℂ)*I)/(1+(v:ℂ)*I))*
        mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I)‖≤
      ((1+|b|)^N*D*polarGaussianConstant T σ 1*Real.exp (-A))*
        ((1+|v|)^(N+48)*Real.exp (-(1/2)*v^2)) := by
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+|ξ|) (weighted_triangle b ξ v) N
    have hm := hdec (ξ+b*v)
    have he : ‖Complex.exp (-(1+(v:ℂ)*I)*(A:ℂ))‖=Real.exp (-A) := by
      rw [Complex.norm_exp]
      congr 1
      simp
    rw [norm_mul,norm_mul,he]
    calc
      _≤((1+|b|)*(1+|ξ+b*v|)*(1+|v|))^N*
        (Real.exp (-A)*(polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-(1/2)*v^2))*
          ‖mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I)‖) := by
        exact mul_le_mul hp (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (a03PolarLineOneDiv_bound T σ v) (Real.exp_pos _).le)
          (norm_nonneg _)) (by positivity) (by positivity)
      _=((1+|b|)^N*polarGaussianConstant T σ 1*Real.exp (-A))*
          ((1+|v|)^(N+48)*Real.exp (-(1/2)*v^2))*
          ((1+|ξ+b*v|)^N*‖mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I)‖) := by
        rw [mul_pow,mul_pow,pow_add]
        ring
      _≤_ := by
        apply (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
        ring
  have hmajor := (gaussian_polynomial_half_integrable (N+48)).const_mul
    ((1+|b|)^N*D*polarGaussianConstant T σ 1*Real.exp (-A))
  have hp0 : 0<(1+|ξ|)^N := pow_pos (by positivity) _
  have hintegral :
      (1+|ξ|)^N*‖∫v : ℝ,Complex.exp (-(1+(v:ℂ)*I)*(A:ℂ))*
        (polarPoleKiller T σ (1+(v:ℂ)*I)/(1+(v:ℂ)*I))*
        mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I)‖≤
      ((1+|b|)^N*D*polarGaussianConstant T σ 1*Real.exp (-A))*gaussianTailConstant (N+48) := by
    have hw (v : ℝ) : ‖((1+|ξ|)^N:ℝ) • (Complex.exp (-(1+(v:ℂ)*I)*(A:ℂ))*
        (polarPoleKiller T σ (1+(v:ℂ)*I)/(1+(v:ℂ)*I))*
        mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I))‖≤
      ((1+|b|)^N*D*polarGaussianConstant T σ 1*Real.exp (-A))*
        ((1+|v|)^(N+48)*Real.exp (-(1/2)*v^2)) := by
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hp0] using hpoint v
    have hh := norm_integral_le_of_norm_le hmajor (Eventually.of_forall hw)
    rw [integral_const_mul] at hh
    simpa only [integral_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hp0,gaussianTailConstant] using hh
  unfold a03GaussianPositiveTimeMellinIntegral
  rw [norm_mul,show ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]]
  calc
    _=(1/(2*Real.pi))*((1+|ξ|)^N*‖∫v : ℝ,Complex.exp (-(1+(v:ℂ)*I)*(A:ℂ))*
        (polarPoleKiller T σ (1+(v:ℂ)*I)/(1+(v:ℂ)*I))*
        mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I)‖) := by ring
    _≤_ := (mul_le_mul_of_nonneg_left hintegral (by positivity)).trans_eq (by dsimp [C]; ring)


theorem a03GaussianPositiveTimeMellinIntegral_strip_full_height_decay {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (A0 A1 b : ℝ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,∀ σ : MomentShifts,∀ A a : ℝ,a∈Icc A0 A1 → ∀ ξ : ℝ,
      (1+|ξ|)^N*‖a03GaussianPositiveTimeMellinIntegral Φ T σ A a b ξ‖≤
        C*polarGaussianConstant T σ 1*Real.exp (-A) := by
  obtain ⟨D,hD,hstrip⟩ := a03PositiveTimeMellin_strip_full_height_decay hΦ hSupp A0 A1 N
  let C := (1/(2*Real.pi))*(1+|b|)^N*D*gaussianTailConstant (N+48)
  have hGaus := gaussianTailConstant_nonneg (N+48)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro T σ A a ha ξ
  have hdec := hstrip a ha
  have hCG := polarGaussianConstant_nonneg T σ 1
  have hpoint (v : ℝ) :
      (1+|ξ|)^N*‖Complex.exp (-(1+(v:ℂ)*I)*(A:ℂ))*
        (polarPoleKiller T σ (1+(v:ℂ)*I)/(1+(v:ℂ)*I))*
        mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I)‖≤
      ((1+|b|)^N*D*polarGaussianConstant T σ 1*Real.exp (-A))*
        ((1+|v|)^(N+48)*Real.exp (-(1/2)*v^2)) := by
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+|ξ|) (weighted_triangle b ξ v) N
    have hm := hdec (ξ+b*v)
    have he : ‖Complex.exp (-(1+(v:ℂ)*I)*(A:ℂ))‖=Real.exp (-A) := by
      rw [Complex.norm_exp]
      congr 1
      simp
    rw [norm_mul,norm_mul,he]
    calc
      _≤((1+|b|)*(1+|ξ+b*v|)*(1+|v|))^N*
        (Real.exp (-A)*(polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-(1/2)*v^2))*
          ‖mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I)‖) := by
        exact mul_le_mul hp (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (a03PolarLineOneDiv_bound T σ v) (Real.exp_pos _).le)
          (norm_nonneg _)) (by positivity) (by positivity)
      _=((1+|b|)^N*polarGaussianConstant T σ 1*Real.exp (-A))*
          ((1+|v|)^(N+48)*Real.exp (-(1/2)*v^2))*
          ((1+|ξ+b*v|)^N*‖mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I)‖) := by
        rw [mul_pow,mul_pow,pow_add]
        ring
      _≤_ := by
        apply (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
        ring
  have hmajor := (gaussian_polynomial_half_integrable (N+48)).const_mul
    ((1+|b|)^N*D*polarGaussianConstant T σ 1*Real.exp (-A))
  have hp0 : 0<(1+|ξ|)^N := pow_pos (by positivity) _
  have hintegral :
      (1+|ξ|)^N*‖∫v : ℝ,Complex.exp (-(1+(v:ℂ)*I)*(A:ℂ))*
        (polarPoleKiller T σ (1+(v:ℂ)*I)/(1+(v:ℂ)*I))*
        mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I)‖≤
      ((1+|b|)^N*D*polarGaussianConstant T σ 1*Real.exp (-A))*gaussianTailConstant (N+48) := by
    have hw (v : ℝ) : ‖((1+|ξ|)^N:ℝ) • (Complex.exp (-(1+(v:ℂ)*I)*(A:ℂ))*
        (polarPoleKiller T σ (1+(v:ℂ)*I)/(1+(v:ℂ)*I))*
        mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I))‖≤
      ((1+|b|)^N*D*polarGaussianConstant T σ 1*Real.exp (-A))*
        ((1+|v|)^(N+48)*Real.exp (-(1/2)*v^2)) := by
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hp0] using hpoint v
    have hh := norm_integral_le_of_norm_le hmajor (Eventually.of_forall hw)
    rw [integral_const_mul] at hh
    simpa only [integral_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hp0,gaussianTailConstant] using hh
  unfold a03GaussianPositiveTimeMellinIntegral
  rw [norm_mul,show ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]]
  calc
    _=(1/(2*Real.pi))*((1+|ξ|)^N*‖∫v : ℝ,Complex.exp (-(1+(v:ℂ)*I)*(A:ℂ))*
        (polarPoleKiller T σ (1+(v:ℂ)*I)/(1+(v:ℂ)*I))*
        mellin Φ ((a:ℂ)+((ξ+b*v:ℝ):ℂ)*I)‖) := by ring
    _≤_ := (mul_le_mul_of_nonneg_left hintegral (by positivity)).trans_eq (by dsimp [C]; ring)

end
end Sechstmoment
