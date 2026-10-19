import Sechstmoment.Denominator.Balanced.GaussianMomentRegularity
import Sechstmoment.Denominator.Unbalanced.MomentDefinitions

/-! The actual chi correction is O(T⁻¹). Its pure time power is retained
until the physical time mean, where it tends uniformly to one. -/
namespace Sechstmoment
open Complex Real Filter Set MeasureTheory Source
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem d04CenteringFactor_eq_dual (T t : ℝ) (z : ℂ) :
    centeringFactor T t z = Complex.exp z *
      secondDualMultiplier t (rawSecondMomentShifts T ![z,0]) := by
  have hsym := zetaChi_one_sub_mul
    (by norm_num [criticalLinePoint] : 0 < (criticalLinePoint t).re)
    (by norm_num [criticalLinePoint] : (criticalLinePoint t).re < 1)
  have hi : zetaChi (1-criticalLinePoint t) = (criticalChi t)⁻¹ := by
    have hh : zetaChi (1-criticalLinePoint t) * criticalChi t = 1 := hsym
    calc
      _ = zetaChi (1-criticalLinePoint t)*(criticalChi t*(criticalChi t)⁻¹) := by
        rw [mul_inv_cancel₀ (criticalChi_ne_zero t), mul_one]
      _ = _ := by rw [← mul_assoc, hh, one_mul]
  simp only [centeringFactor, centeringShift, secondDualMultiplier,
    secondSourceZetaPoints, rawSecondMomentShifts, Matrix.cons_val_zero,
    Matrix.cons_val_one, div_eq_mul_inv, zero_mul, add_zero, hi, mul_assoc]

theorem d04CenteringPurePower_eq_dual {T t : ℝ} (ht : 0 < t) (z : ℂ) :
    d04CenteringPurePower T t z = Complex.exp z *
      secondDualPower t (rawSecondMomentShifts T ![z,0]) := by
  have hp : 0 < t/(2*Real.pi) := by positivity
  simp only [secondDualPower, rawSecondMomentShifts, Matrix.cons_val_zero,
    Matrix.cons_val_one, zero_div, add_zero]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, ← Complex.exp_add]
  unfold d04CenteringPurePower
  congr 1
  ring

theorem d04CenteringPurePower_eq_elementary {T τ : ℝ}
    (hT : 0 < T) (hτ : 0 < τ) (z : ℂ) :
    d04CenteringPurePower T (T*τ) z = elementaryCenteredPhase T τ z := by
  rw [d04CenteringPurePower_eq_dual (mul_pos hT hτ)]
  simp [secondDualPower, rawSecondMomentShifts, elementaryCenteredPhase, neg_div]

theorem d04CenteringPurePower_measurable (T : ℝ) (z : ℂ) :
    Measurable (fun t : ℝ => d04CenteringPurePower T t z) := by
  unfold d04CenteringPurePower
  exact Complex.continuous_exp.measurable.comp
    (measurable_const.mul (measurable_const.sub
      ((Complex.continuous_ofReal.measurable.comp
        (Real.measurable_log.comp (measurable_id.div_const _))).div_const _)))

theorem d04CenteringPurePower_dyadic_factorization {T τ : ℝ}
    (hT : 0 < T) (hτ : 0 < τ) (z : ℂ) :
    d04CenteringPurePower T (T*τ) z = d04CenteringPurePower T T z *
      (τ : ℂ)^(-z/(Real.log T : ℂ)) := by
  rw [d04CenteringPurePower_eq_dual (mul_pos hT hτ),
    d04CenteringPurePower_eq_dual hT,
    secondDualPower_dyadic_factorization hT hτ]
  simp [mul_assoc]

theorem d04CenteringPurePower_prefactor {T : ℝ}
    (hT : 0 < T) (hlog : Real.log T ≠ 0) (z : ℂ) :
    d04CenteringPurePower T T z =
      Complex.exp (z*(Real.log (2*Real.pi) : ℂ)/(Real.log T : ℂ)) := by
  unfold d04CenteringPurePower
  rw [Real.log_div hT.ne' (by positivity : (2*Real.pi:ℝ) ≠ 0)]
  push_cast
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr hlog]
  ring

theorem d04CenteringPower_uniform_error {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc T (2*T),
      ∀ z : ℂ, ‖z‖ ≤ R →
        ‖centeringFactor T t z-d04CenteringPurePower T t z‖ ≤ C/T := by
  obtain ⟨C,hC,h⟩ := secondDualMultiplier_uniform_normalized_power_error hR
  refine ⟨Real.exp R*C, by positivity, ?_⟩
  filter_upwards [h, eventually_gt_atTop (0:ℝ)] with T hT hTp
  intro t ht z hz
  have hτ : t/T ∈ Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hTp).mpr (by simpa using ht.1),
      (div_le_iff₀ hTp).mpr ht.2⟩
  have hzv : ∀ i : Fin 2, ‖(![z,0] : Fin 2 → ℂ) i‖ ≤ R := by
    intro i
    fin_cases i
    · exact hz
    · simpa using hR
  have hb := (hT (t/T) hτ ![z,0] hzv).1
  rw [show T*(t/T)=t by field_simp] at hb
  rw [d04CenteringFactor_eq_dual, d04CenteringPurePower_eq_dual (hTp.trans_le ht.1),
    ← mul_sub, norm_mul]
  have he : ‖Complex.exp z‖ ≤ Real.exp R := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm z).trans hz)
  exact (mul_le_mul he hb (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem d04CenteringPurePower_uniform_tendsto {R : ℝ}
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ τ ∈ Icc (1:ℝ) 2,
      ∀ z : ℂ, ‖z‖ ≤ R → ‖d04CenteringPurePower T (T*τ) z-1‖ < ε := by
  have hlim : Tendsto (fun T : ℝ =>
      (2*R*elementaryPhaseLogBound)/Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  filter_upwards [elementaryCenteredPhase_uniform_error_bound R,
    hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop (0:ℝ)]
    with T hT he hTp
  intro τ hτ z hz
  rw [d04CenteringPurePower_eq_elementary hTp (zero_lt_one.trans_le hτ.1)]
  exact (hT τ hτ z hz).trans_lt he

theorem d04CenteringPurePower_uniform_norm {R : ℝ} :
    ∀ᶠ T : ℝ in atTop, ∀ τ ∈ Icc (1:ℝ) 2,
      ∀ z : ℂ, ‖z‖ ≤ R → ‖d04CenteringPurePower T (T*τ) z‖ ≤ 2 := by
  filter_upwards [d04CenteringPurePower_uniform_tendsto (R:=R)
    (by norm_num : (0:ℝ)<1)] with T hT
  intro τ hτ z hz
  have hh := hT τ hτ z hz
  have hn : ‖d04CenteringPurePower T (T*τ) z‖ ≤
      ‖d04CenteringPurePower T (T*τ) z-1‖+1 := by
    convert norm_add_le (d04CenteringPurePower T (T*τ) z-1) (1:ℂ) using 1 <;> simp
  linarith

def d04PhysicalTimeMean (T : ℝ) (z : ℂ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ τ : ℝ, (Φ τ : ℂ)*d04CenteringPurePower T (T*τ) z

theorem d04PhysicalTimeMean_uniform_tendsto {R : ℝ}
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖d04PhysicalTimeMean T z Φ-(∫ τ : ℝ, Φ τ : ℂ)‖ < ε := by
  obtain ⟨P,hP,hb⟩ := d02Continuous_supported_norm_bound hΦ hΦs
  have hδ : 0 < ε/(P+1) := div_pos hε (by linarith)
  filter_upwards [d04CenteringPurePower_uniform_tendsto (R:=R) hδ]
    with T hT
  intro z hz
  have hzero (τ : ℝ) (hτ : τ ∉ Icc (1:ℝ) 2) : Φ τ=0 := by
    by_contra hn
    exact hτ (hΦs (subset_tsupport Φ hn))
  have heq : d04PhysicalTimeMean T z Φ-(∫ τ : ℝ, Φ τ : ℂ) =
      ∫ τ : ℝ, (Φ τ : ℂ)*(d04CenteringPurePower T (T*τ) z-1) := by
    have hmeas : Measurable (fun τ : ℝ =>
        (Φ τ : ℂ)*d04CenteringPurePower T (T*τ) z) :=
      (Complex.continuous_ofReal.comp hΦ).measurable.mul
        ((d04CenteringPurePower_measurable T z).comp (measurable_const.mul measurable_id))
    have hbound (τ : ℝ) (hτ : τ ∈ Icc (1:ℝ) 2) :
        ‖(Φ τ : ℂ)*d04CenteringPurePower T (T*τ) z‖ ≤ P*(ε/(P+1)+1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hn : ‖d04CenteringPurePower T (T*τ) z‖ ≤ ε/(P+1)+1 := by
        have hh := hT τ hτ z hz
        have hn := norm_add_le (d04CenteringPurePower T (T*τ) z-1) (1:ℂ)
        simp only [sub_add_cancel, norm_one] at hn
        linarith
      exact mul_le_mul (hb τ) hn (norm_nonneg _) hP
    have hi := d02Measurable_window_integrable hmeas
      (fun τ hτ => by rw [hzero τ hτ]; simp) hbound
    have hΦreal : Integrable Φ volume := hΦ.integrable_of_hasCompactSupport
      (HasCompactSupport.intro isCompact_Icc hzero)
    have hΦi : Integrable (fun τ : ℝ => (Φ τ : ℂ)) := hΦreal.ofReal
    rw [d04PhysicalTimeMean, ← integral_sub hi hΦi]
    apply integral_congr_ae
    filter_upwards [] with τ
    ring
  rw [heq]
  have hsupp : (∫ τ : ℝ, (Φ τ : ℂ)*(d04CenteringPurePower T (T*τ) z-1)) =
      ∫ τ in Icc (1:ℝ) 2, (Φ τ : ℂ)*(d04CenteringPurePower T (T*τ) z-1) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro τ hτ
    rw [hzero τ hτ]
    simp
  rw [hsupp]
  have hwindow : ∀ τ ∈ Icc (1:ℝ) 2,
      ‖(Φ τ : ℂ)*(d04CenteringPurePower T (T*τ) z-1)‖ ≤ P*(ε/(P+1)) := by
    intro τ hτ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hb τ) (hT τ hτ z hz).le (norm_nonneg _) hP
  have hn := norm_setIntegral_le_of_norm_le_const (μ:=volume)
    (s:=Icc (1:ℝ) 2) measure_Icc_lt_top hwindow
  have hB : P*(ε/(P+1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ (by linarith : 0<P+1)]
    nlinarith
  norm_num [Real.volume_real_Icc] at hn
  exact hn.trans_lt hB

theorem d04PhysicalTimeMean_tendsto (z : ℂ)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    Tendsto (fun T : ℝ => d04PhysicalTimeMean T z Φ) atTop
      (𝓝 (∫ τ : ℝ, Φ τ : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [d04PhysicalTimeMean_uniform_tendsto (R:=‖z‖) Φ hΦ hΦs hε]
    with T hT
  simpa only [dist_eq_norm] using hT z le_rfl

theorem d04PhysicalTimeMean_uniform_bounded {R : ℝ}
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ ⊆ Icc 1 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖d04PhysicalTimeMean T z Φ‖ ≤ C := by
  refine ⟨‖(∫ τ : ℝ, Φ τ : ℂ)‖+1, by positivity, ?_⟩
  filter_upwards [d04PhysicalTimeMean_uniform_tendsto (R:=R) Φ hΦ hΦs
    (by norm_num : (0:ℝ)<1)] with T hT
  intro z hz
  have hh := hT z hz
  have hn := norm_add_le (d04PhysicalTimeMean T z Φ-(∫ τ : ℝ, Φ τ : ℂ))
    (∫ τ : ℝ, Φ τ : ℂ)
  simp only [sub_add_cancel] at hn
  linarith

end
end Sechstmoment
