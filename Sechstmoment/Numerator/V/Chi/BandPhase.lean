import Sechstmoment.Analysis.Mellin.FourierCutoff
import Sechstmoment.Numerator.V.Arithmetic.Additive.PhaseTaylor


namespace Sechstmoment.Source
open Complex Real MeasureTheory Set
open scoped FourierTransform
noncomputable section

def noDPBandPhaseIntegrand (h : SchwartzMap ℝ ℂ) (H a c b ξ : ℝ) : ℂ :=
  noDPFourierCutoff h H ξ*(Real.exp (c*(b*ξ)):ℂ)*
    Complex.exp (I*((a*Real.exp (b*ξ):ℝ):ℂ))

def noDPBandLinearIntegrand (h : SchwartzMap ℝ ℂ) (H a b ξ : ℝ) : ℂ :=
  noDPFourierCutoff h H ξ*Complex.exp (I*(a:ℂ))*Complex.exp (I*((a*(b*ξ):ℝ):ℂ))

theorem noDPBandPhase_integrable (h : SchwartzMap ℝ ℂ) {H : ℝ}
    (hH : 0 < H) (a c b : ℝ) : Integrable (noDPBandPhaseIntegrand h H a c b) := by
  have hK : HasCompactSupport (noDPFourierCutoff h H) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (noDPFourierCutoff_tsupport h hH)
  apply Continuous.integrable_of_hasCompactSupport _ (hK.mul_right.mul_right)
  exact ((noDPFourierCutoff_contDiff h H).continuous.mul
    (by fun_prop : Continuous (fun ξ : ℝ => (Real.exp (c*(b*ξ)):ℂ)))).mul (by fun_prop)

theorem noDPBandLinear_integrable (h : SchwartzMap ℝ ℂ) {H : ℝ}
    (hH : 0 < H) (a b : ℝ) : Integrable (noDPBandLinearIntegrand h H a b) := by
  have hK : HasCompactSupport (noDPFourierCutoff h H) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (noDPFourierCutoff_tsupport h hH)
  apply Continuous.integrable_of_hasCompactSupport _ (hK.mul_right.mul_right)
  exact ((noDPFourierCutoff_contDiff h H).continuous.mul continuous_const).mul (by fun_prop)

theorem noDPBandLinear_integral (h : SchwartzMap ℝ ℂ) (H a b : ℝ) :
    (∫ ξ : ℝ, noDPBandLinearIntegrand h H a b ξ) =
      Complex.exp (I*(a:ℂ))*𝓕⁻ (noDPFourierCutoff h H) (a*b/(2*Real.pi)) := by
  rw [fourierInv_eq_fourier_neg,Real.fourier_eq',← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [Real.inner_apply,smul_eq_mul]
  have he : I*((a*(b*ξ):ℝ):ℂ) =
      (((-2*Real.pi*(ξ*(-(a*b/(2*Real.pi)))):ℝ):ℂ)*I) := by
    have hr : a*(b*ξ) = -2*Real.pi*(ξ*(-(a*b/(2*Real.pi)))) := by
      field_simp [Real.pi_ne_zero]
    rw [hr]
    ring
  unfold noDPBandLinearIntegrand
  rw [he]
  ring

theorem noDPBandPhase_error_pointwise (h : SchwartzMap ℝ ℂ)
    {H : ℝ} (hH : 0 < H) (a c b : ℝ)
    (hb : |b| * (2*H) ≤ 1) (hcb : |c| * |b| * (2*H) ≤ 1) (ξ : ℝ) :
    ‖noDPBandPhaseIntegrand h H a c b ξ-noDPBandLinearIntegrand h H a b ξ‖ ≤
      (2* |c| * |b|)*(|ξ| * ‖h ξ‖)+(|a| * b^2)*(|ξ|^2*‖h ξ‖) := by
  by_cases hξ : |ξ| ≤ 2*H
  · have hv : |b*ξ| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hξ (abs_nonneg _)).trans hb
    have hcv : |c*(b*ξ)| ≤ 1 := by
      rw [abs_mul,abs_mul]
      calc
        _ = (|c| * |b|)* |ξ| := by ring
        _ ≤ (|c| * |b|)*(2*H) := mul_le_mul_of_nonneg_left hξ (by positivity)
        _ ≤ 1 := hcb
    have he : noDPBandPhaseIntegrand h H a c b ξ-noDPBandLinearIntegrand h H a b ξ =
        noDPFourierCutoff h H ξ*
          ((Real.exp (c*(b*ξ)):ℂ)*Complex.exp (I*((a*Real.exp (b*ξ):ℝ):ℂ))-
            Complex.exp (I*(a:ℂ))*Complex.exp (I*((a*(b*ξ):ℝ):ℂ))) := by
      unfold noDPBandPhaseIntegrand noDPBandLinearIntegrand
      ring
    rw [he,norm_mul]
    calc
      _ ≤ ‖h ξ‖*(2* |c*(b*ξ)|+|a| * (b*ξ)^2) :=
        mul_le_mul (noDPFourierCutoff_norm h H ξ)
          (additive_weighted_exp_linearization a c (b*ξ) hv hcv) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by rw [abs_mul,abs_mul,mul_pow,sq_abs]; ring
  · have hzero := noDPFourierCutoff_zero h hH (le_of_lt (lt_of_not_ge hξ))
    simp only [noDPBandPhaseIntegrand,noDPBandLinearIntegrand,hzero,zero_mul,sub_self,norm_zero]
    positivity

theorem noDPBandPhase_error_integral (h : SchwartzMap ℝ ℂ)
    {H : ℝ} (hH : 0 < H) (a c b : ℝ)
    (hb : |b| * (2*H) ≤ 1) (hcb : |c| * |b| * (2*H) ≤ 1) :
    ‖(∫ ξ : ℝ, noDPBandPhaseIntegrand h H a c b ξ)-
      (∫ ξ : ℝ, noDPBandLinearIntegrand h H a b ξ)‖ ≤
      (2* |c| * |b|)*(∫ ξ : ℝ, |ξ| * ‖h ξ‖)+
        (|a| * b^2)*(∫ ξ : ℝ, |ξ|^2*‖h ξ‖) := by
  have h1 : Integrable (fun ξ : ℝ => |ξ| * ‖h ξ‖) := by
    simpa only [Real.norm_eq_abs,pow_one] using h.integrable_pow_mul volume 1
  have h2 : Integrable (fun ξ : ℝ => |ξ|^2*‖h ξ‖) := by
    simpa only [Real.norm_eq_abs] using h.integrable_pow_mul volume 2
  have hmajor := (h1.const_mul (2* |c| * |b|)).add (h2.const_mul (|a| * b^2))
  rw [← integral_sub (noDPBandPhase_integrable h hH a c b) (noDPBandLinear_integrable h hH a b)]
  apply (norm_integral_le_of_norm_le hmajor
    (Filter.Eventually.of_forall (noDPBandPhase_error_pointwise h hH a c b hb hcb))).trans_eq
  simp only [Pi.add_apply]
  rw [integral_add (h1.const_mul _) (h2.const_mul _),integral_const_mul,integral_const_mul]

theorem noDPBandPhase_time_scale_error (h : SchwartzMap ℝ ℂ)
    {T : ℝ} (hT : 0 < T) (a c : ℝ) (hc : |c| ≤ 2) :
    ‖(∫ ξ : ℝ, noDPBandPhaseIntegrand h (T/(100*Real.pi)) a c (-2*Real.pi/T) ξ)-
      (∫ ξ : ℝ, noDPBandLinearIntegrand h (T/(100*Real.pi)) a (-2*Real.pi/T) ξ)‖ ≤
      (8*Real.pi/T)*(∫ ξ : ℝ, |ξ| * ‖h ξ‖)+
        (|a| * (2*Real.pi/T)^2)*(∫ ξ : ℝ, |ξ|^2*‖h ξ‖) := by
  have hp : 0 < 100*Real.pi := by positivity
  have hH : 0 < T/(100*Real.pi) := div_pos hT hp
  have hbabs : |-2*Real.pi/T| = 2*Real.pi/T := by
    rw [abs_div,abs_mul,abs_neg,abs_of_pos Real.pi_pos,abs_of_pos hT]
    norm_num
  have hbprod : |-2*Real.pi/T| * (2*(T/(100*Real.pi))) = 1/25 := by
    rw [hbabs]
    field_simp [hT.ne',Real.pi_ne_zero]
    ring
  have hb : |-2*Real.pi/T| * (2*(T/(100*Real.pi))) ≤ 1 := by rw [hbprod]; norm_num
  have hcb : |c| * |-2*Real.pi/T| * (2*(T/(100*Real.pi))) ≤ 1 := by
    rw [mul_assoc,hbprod]
    linarith
  have H := noDPBandPhase_error_integral h hH a c (-2*Real.pi/T) hb hcb
  have hmoment : 0 ≤ ∫ ξ : ℝ, |ξ| * ‖h ξ‖ := integral_nonneg (fun _ => by positivity)
  apply H.trans
  rw [hbabs,show (-2*Real.pi/T)^2 = (2*Real.pi/T)^2 by ring]
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ hmoment
  calc
    2* |c| * (2*Real.pi/T) ≤ 2*2*(2*Real.pi/T) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (by positivity)
    _ = _ := by ring

end
end Sechstmoment.Source
