import Sechstmoment.Numerator.U.ZeroModes.RatioTimeFourierContour

/-! Arbitrary Fourier decay and positive Mellin spatial gains of the actual
ratio/time contour, uniformly for compact complex powers in the dual profile. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 700000

theorem a03RatioTimeFourierContour_uniform_frequency_decay {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c R : ℝ} (hc : 0<c) (hR : 0≤R) (b : ℝ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,∀ σ : MomentShifts,∀ A ξ : ℝ,∀ ρ : ℂ,‖ρ‖≤R →
      (1+|ξ|)^N*‖a03RatioTimeFourierContour Φ T σ c A b ξ ρ‖≤
        C*polarGaussianConstant T σ c*Real.exp (-c*A) := by
  obtain ⟨D,hD,hfreq⟩ := a03TimePowerProfile_fourier_decay hΦ hSupp
    (R:=R+|b| *c) (by positivity) N
  let H : ℝ := 1+R+|b| *(|c|+1)
  have hH : 0<H := by dsimp [H]; positivity
  let C : ℝ := (1/(2*Real.pi))*D*H^N*gaussianTailConstant (N+48)/c
  have hGauss := gaussianTailConstant_nonneg (N+48)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro T σ A ξ ρ hρ
  have hCG := polarGaussianConstant_nonneg T σ c
  have hp0 : 0<(1+|ξ|)^N := pow_pos (by positivity) _
  have hpoint (v : ℝ) :
      (1+|ξ|)^N*‖Complex.exp (-((c:ℂ)+(v:ℂ)*I)*(A:ℂ))*
        (polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I))*
        profileLaplaceTransform (a03ProfileProduct Φ
          (fun t : ℝ => (t:ℂ)^(ρ-(b:ℂ)*((c:ℂ)+(v:ℂ)*I)))) ((ξ:ℂ)*I)‖≤
      (D*H^N*polarGaussianConstant T σ c/c*Real.exp (-c*A))*
        ((1+|v|)^(N+48)*Real.exp (-(1/2)*v^2)) := by
    let z : ℂ := (c:ℂ)+(v:ℂ)*I
    let q : ℂ := ρ-(b:ℂ)*z
    have hz : ‖z‖≤|c|+|v| := by simpa [z] using Complex.norm_le_abs_re_add_abs_im z
    have hqRe : q.re≤R+|b| *c := by
      have hρRe := (Complex.re_le_norm ρ).trans hρ
      have hb := neg_le_abs b
      have hh := mul_le_mul_of_nonneg_right hb hc.le
      dsimp [q,z]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,
        Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
      linarith only [hρRe,hh]
    have hqn : ‖q‖≤R+|b| *(|c|+|v|) := by
      exact (norm_sub_le ρ ((b:ℂ)*z)).trans ((add_le_add hρ
        (by simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using mul_le_mul_of_nonneg_left hz (abs_nonneg b))))
    have hqH : 1+‖q‖≤H*(1+|v|) := by
      dsimp only [H]
      nlinarith only [hqn,hR,abs_nonneg b,abs_nonneg c,abs_nonneg v,
        mul_nonneg hR (abs_nonneg v),mul_nonneg (mul_nonneg (abs_nonneg b) (abs_nonneg c)) (abs_nonneg v)]
    have hpr := hfreq q hqRe ξ
    have hqp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+‖q‖) hqH N
    rw [mul_pow] at hqp
    have hf : (1+|ξ|)^N*‖profileLaplaceTransform (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^q)) ((ξ:ℂ)*I)‖≤
        D*H^N*(1+|v|)^N := hpr.trans ((mul_le_mul_of_nonneg_left hqp hD).trans_eq (by ring))
    have he : ‖Complex.exp (-z*(A:ℂ))‖=Real.exp (-c*A) := by
      rw [Complex.norm_exp]
      congr 1
      simp [z]
    change (1+|ξ|)^N*‖Complex.exp (-z*(A:ℂ))*(polarPoleKiller T σ z/z)*
      profileLaplaceTransform (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^q)) ((ξ:ℂ)*I)‖≤_
    rw [norm_mul,norm_mul,he]
    calc
      _=Real.exp (-c*A)*‖polarPoleKiller T σ z/z‖*((1+|ξ|)^N*
          ‖profileLaplaceTransform (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^q)) ((ξ:ℂ)*I)‖) := by ring
      _≤Real.exp (-c*A)*(polarGaussianConstant T σ c/c*(1+|v|)^48*Real.exp (-(1/2)*v^2))*
          (D*H^N*(1+|v|)^N) :=
        by
          have hh := mul_le_mul (a03PolarPositiveLineDiv_bound hc T σ v) hf (by positivity) (by positivity)
          have hhh := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-c*A)).le
          simpa only [mul_assoc,z] using hhh
      _=_ := by rw [pow_add]; ring
  have hmajor := (gaussian_polynomial_half_integrable (N+48)).const_mul
    (D*H^N*polarGaussianConstant T σ c/c*Real.exp (-c*A))
  have hw (v : ℝ) :
      ‖((1+|ξ|)^N:ℝ) • (Complex.exp (-((c:ℂ)+(v:ℂ)*I)*(A:ℂ))*
        (polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I))*
        profileLaplaceTransform (a03ProfileProduct Φ
          (fun t : ℝ => (t:ℂ)^(ρ-(b:ℂ)*((c:ℂ)+(v:ℂ)*I)))) ((ξ:ℂ)*I))‖≤
      (D*H^N*polarGaussianConstant T σ c/c*Real.exp (-c*A))*
        ((1+|v|)^(N+48)*Real.exp (-(1/2)*v^2)) := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hp0] using hpoint v
  have hi := norm_integral_le_of_norm_le hmajor (Eventually.of_forall hw)
  rw [integral_const_mul] at hi
  simp only [integral_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hp0] at hi
  unfold a03RatioTimeFourierContour
  rw [norm_mul,show ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]]
  calc
    _=(1/(2*Real.pi))*((1+|ξ|)^N*‖∫v : ℝ,Complex.exp (-((c:ℂ)+(v:ℂ)*I)*(A:ℂ))*
        (polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I))*
        profileLaplaceTransform (a03ProfileProduct Φ
          (fun t : ℝ => (t:ℂ)^(ρ-(b:ℂ)*((c:ℂ)+(v:ℂ)*I)))) ((ξ:ℂ)*I)‖) := by ring
    _≤_ := (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by dsimp only [C,gaussianTailConstant]; ring)

end
end Sechstmoment
