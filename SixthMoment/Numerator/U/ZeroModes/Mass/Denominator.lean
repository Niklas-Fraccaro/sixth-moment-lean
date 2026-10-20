import SixthMoment.Numerator.U.Diagonal.RawShiftFactorMass
import SixthMoment.Numerator.U.Replacement.TimeGammaErrorFourier
import SixthMoment.Numerator.U.ZeroModes.Mass.Smooth

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03ZeroModeRealQuadDenominator (α : MomentShifts) (z : ℂ) (x : Fin 4→ℝ) : ℂ :=
  ∏ j : Fin 4,(x j:ℂ)^(1/2+α j+z)

theorem a03ZeroModeRealQuadDenominator_inv_norm_eq (α : MomentShifts) (z : ℂ)
    (x : Fin 4→ℝ) (hx : ∀ j,0<x j) :
    ‖(a03ZeroModeRealQuadDenominator α z x)⁻¹‖=
      ∏ j : Fin 4,(x j)^(-(1/2+(α j).re+z.re)) := by
  unfold a03ZeroModeRealQuadDenominator
  rw [norm_inv,norm_prod,←Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx j)]
  simp only [Complex.add_re,Complex.div_ofNat_re,Complex.one_re]
  rw [Real.rpow_neg (hx j).le]

theorem a03ZeroModeRealQuadDenominator_inv_norm_le_product (α : MomentShifts) (z : ℂ)
    (hz : 0≤z.re) (x : Fin 4→ℝ) (hx : ∀ j,1≤x j) {r : ℝ}
    (hα : ∀ j,-r≤(α j).re) :
    ‖(a03ZeroModeRealQuadDenominator α z x)⁻¹‖≤
      (∏ j : Fin 4,x j)^r/Real.sqrt (∏ j : Fin 4,x j) := by
  have hxp (j : Fin 4) : 0<x j := zero_lt_one.trans_le (hx j)
  have hprod : 0<∏ j : Fin 4,x j := Finset.prod_pos (fun j _ => hxp j)
  calc
    _=∏ j : Fin 4,(x j)^(-(1/2+(α j).re+z.re)) :=
      a03ZeroModeRealQuadDenominator_inv_norm_eq α z x hxp
    _≤∏ j : Fin 4,(x j)^(r-1/2) := by
      apply Finset.prod_le_prod₀ (fun j _ => (Real.rpow_pos_of_pos (hxp j) _).le)
      intro j _
      apply Real.rpow_le_rpow_of_exponent_le (hx j)
      linarith [hα j]
    _=(∏ j : Fin 4,x j)^(r-1/2) :=
      Real.finsetProd_rpow Finset.univ x (fun j _ => (hxp j).le) (r-1/2)
    _=_ := by rw [Real.rpow_sub hprod,←Real.sqrt_eq_rpow]

theorem a03ZeroModeRealQuadDenominator_raw_inv_norm_le
    {T C κ R : ℝ} (hT : 0<T) (hlog : 1≤Real.log T) (hC : 1≤C) (hR : 0≤R)
    (σ : MomentShifts) (hσ : ∀ j,‖σ j‖≤R) (m : Fin 6) (z : ℂ) (hz : 0≤z.re)
    (x : Fin 4→ℝ) (hx : ∀ j,1≤x j) (hcut : (∏ j : Fin 4,x j)≤C*T^κ) :
    ‖(a03ZeroModeRealQuadDenominator (bblrSixShifts (rawMomentShifts T σ) m) z x)⁻¹‖≤
      Real.exp (R*(Real.log C+κ))/Real.sqrt (∏ j : Fin 4,x j) := by
  have hL : 0<Real.log T := zero_lt_one.trans_le hlog
  have hraw : ∀ j,‖bblrSixShifts (rawMomentShifts T σ) m j‖≤R/Real.log T := by
    apply bblrSixShifts_norm_le
    intro j
    rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_of_nonneg hL.le]
    exact div_le_div_of_nonneg_right (hσ j) hL.le
  have hprod : 0<∏ j : Fin 4,x j := Finset.prod_pos (fun j _ => zero_lt_one.trans_le (hx j))
  calc
    _≤(∏ j : Fin 4,x j)^(R/Real.log T)/Real.sqrt (∏ j : Fin 4,x j) :=
      a03ZeroModeRealQuadDenominator_inv_norm_le_product _ z hz x hx (fun j =>
        (abs_le.mp ((Complex.abs_re_le_norm _).trans (hraw j))).1)
    _≤_ := div_le_div_of_nonneg_right
      (bblrRawShift_product_rpow_le hT hlog hC hR hprod hcut) (Real.sqrt_nonneg _)

theorem a03ZeroModeReplacementFrequency_uniform_bound
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j,‖α j‖≤1/4) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ ξ : ℝ,
      ‖a03GaussianReplacementFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I) ξ‖≤C*T^(ε-1) := by
  obtain ⟨C,hC,hb⟩ := a03_gaussian_replacement_frequency_logarithmic_uniform_derivative_bounds
    hΦ hΦs hc hc1 hε hκ hθ
  refine ⟨C 0 0,hC 0 0,?_⟩
  filter_upwards [hb] with T hb
  intro σ α hα hroot v hv ξ
  simpa using hb σ α hα hroot v hv 0 0 ξ

theorem a03ZeroMode_real_replacement_kernel_uniform_bound
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ m : Fin 6, ∀ v : ℝ,|v|≤θ*Real.log T → ∀ x : Fin 4→ℝ,
      (∀ j,1≤x j) → (∏ j : Fin 4,x j)≤16*T^(2+η) → ∀ ξ : ℝ,
      ‖a03GaussianReplacementFrequencyProfile Φ T σ (bblrSixShifts (rawMomentShifts T σ) m)
        ((c:ℂ)+(v:ℂ)*I) ξ/
          a03ZeroModeRealQuadDenominator (bblrSixShifts (rawMomentShifts T σ) m) ((c:ℂ)+(v:ℂ)*I) x‖≤
            C*T^(ε-1)/Real.sqrt (∏ j : Fin 4,x j) := by
  obtain ⟨C,hC,hb⟩ := a03ZeroModeReplacementFrequency_uniform_bound hΦ hΦs hc hc1 hε hκ hθ
  let D : ℝ := Real.exp (R*(Real.log 16+(2+η)))
  refine ⟨C*D,by positivity,?_⟩
  filter_upwards [hb,rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    eventually_gt_atTop (0:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hb hsmall hT hlog
  intro σ hσ hroot m v hv x hx hcut ξ
  have hraw := hsmall σ hσ
  have hf := hb σ (bblrSixShifts (rawMomentShifts T σ) m)
    (bblrSixShifts_norm_le _ hraw m) hroot v hv ξ
  have hd := a03ZeroModeRealQuadDenominator_raw_inv_norm_le hT hlog (by norm_num : (1:ℝ)≤16) hR
    σ hσ m ((c:ℂ)+(v:ℂ)*I) (by simpa using hc.le) x hx hcut
  rw [div_eq_mul_inv,norm_mul]
  calc
    _≤(C*T^(ε-1))*(D/Real.sqrt (∏ j : Fin 4,x j)) :=
      mul_le_mul hf hd (norm_nonneg _) (by positivity)
    _=_ := by ring

end
end SixthMoment
