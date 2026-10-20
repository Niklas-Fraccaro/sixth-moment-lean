import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Sechstmoment.Numerator.V.DP.Input


namespace Sechstmoment.Source
open Complex MeasureTheory Set Polynomial Filter
open scoped Topology

noncomputable section

def dpNormalizedTriple (η : ℝ) (P : ℝ[X]) (β γ δ : ℂ) : ℂ :=
  ∫ x : ℝ in 0..1, ∫ v : ℝ in 0..(1-x), ∫ w : ℝ in 0..(1-x-v),
    ((Polynomial.eval (1-x-v-w : ℝ) P : ℝ) : ℂ)*
      Complex.exp ((η : ℂ)*(-β*x+γ*v+δ*w))

def dpNormalizedFourResidues (q η : ℝ) (P : ℝ[X]) (σ : MomentShifts) : ℂ :=
  Complex.exp ((q : ℂ)*(-σ 0-σ 2-σ 3))*(dpNormalizedTriple η P (σ 1) (σ 2) (σ 3))^2 /
      ((σ 1-σ 0)*(σ 0+σ 2)*(σ 0+σ 3)) +
    Complex.exp ((q : ℂ)*(-σ 1-σ 2-σ 3))*(dpNormalizedTriple η P (σ 0) (σ 2) (σ 3))^2 /
      ((σ 0-σ 1)*(σ 1+σ 2)*(σ 1+σ 3)) +
    Complex.exp ((q : ℂ)*(-σ 3))*(dpNormalizedTriple η P (σ 1) (-σ 0) (σ 3))^2 /
      ((σ 1+σ 2)*(σ 0+σ 2)*(σ 2-σ 3)) +
    Complex.exp ((q : ℂ)*(-σ 2))*(dpNormalizedTriple η P (σ 1) (σ 2) (-σ 0))^2 /
      ((σ 1+σ 3)*(σ 3-σ 2)*(σ 0+σ 3))

theorem dpTripleIntegral_normalized {T : ℝ} (hT : 1 < T) (η : ℝ)
    (P : ℝ[X]) (β γ δ : ℂ) :
    dpTripleIntegral (T^η) P (β/(Real.log T : ℂ)) (γ/(Real.log T : ℂ))
      (δ/(Real.log T : ℂ)) = dpNormalizedTriple η P β γ δ := by
  have hL : (Real.log T : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne'
  have he (x v w : ℝ) :
      (Real.log (T^η) : ℂ)*(- (β/(Real.log T : ℂ))*x+
        (γ/(Real.log T : ℂ))*v+(δ/(Real.log T : ℂ))*w) =
      (η : ℂ)*(-β*x+γ*v+δ*w) := by
    rw [Real.log_rpow (zero_lt_one.trans hT)]
    push_cast
    field_simp
  unfold dpTripleIntegral dpNormalizedTriple
  simp_rw [he]

private theorem exp_scaled (q L : ℝ) (μ : ℂ) :
    Complex.exp ((q : ℂ)*(μ/(L : ℂ))) =
      Complex.exp (((q/L : ℝ) : ℂ)*μ) := by
  congr 1
  push_cast
  ring

private theorem denominator_scaled (L a b c : ℂ) :
    (a/L)*(b/L)*(c/L) = (a*b*c)/L^3 := by
  simp only [div_eq_mul_inv]
  ring

private theorem residue_scaled (q L : ℝ) (μ a b c F : ℂ) :
    Complex.exp ((q : ℂ)*(μ/(L : ℂ)))*F^2 /
      ((a/(L : ℂ))*(b/(L : ℂ))*(c/(L : ℂ))) =
    (L : ℂ)^3*(Complex.exp (((q/L : ℝ) : ℂ)*μ)*F^2/(a*b*c)) := by
  rw [exp_scaled, denominator_scaled, div_div_eq_mul_div]
  ring

theorem dpFourResidues_endpoint_normalized {T : ℝ} (hT : 1 < T)
    (X η : ℝ) (P : ℝ[X]) (σ : MomentShifts) :
    dpFourResidues X (T^η) P (rawMomentShifts T σ) =
      (Real.log T : ℂ)^3 *
        dpNormalizedFourResidues (Real.log (X/(2*Real.pi))/Real.log T) η P σ := by
  have hL : (Real.log T : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne'
  have hn (z : ℂ) : -(z/(Real.log T : ℂ)) = (-z)/(Real.log T : ℂ) := by ring
  have ha (z w : ℂ) : z/(Real.log T : ℂ)+w/(Real.log T : ℂ) =
      (z+w)/(Real.log T : ℂ) := (add_div _ _ _).symm
  have hs (z w : ℂ) : z/(Real.log T : ℂ)-w/(Real.log T : ℂ) =
      (z-w)/(Real.log T : ℂ) := (sub_div _ _ _).symm
  unfold dpFourResidues dpNormalizedFourResidues rawMomentShifts
  simp only [hn, ha, hs]
  simp only [dpTripleIntegral_normalized hT, residue_scaled]
  ring

theorem dpFourResidues_normalized {T : ℝ} (hT : 1 < T)
    (η : ℝ) (P : ℝ[X]) (σ : MomentShifts) :
    dpFourResidues T (T^η) P (rawMomentShifts T σ) =
      (Real.log T : ℂ)^3 *
        dpNormalizedFourResidues (Real.log (T/(2*Real.pi))/Real.log T) η P σ :=
  dpFourResidues_endpoint_normalized hT T η P σ

theorem dpNormalizedFourResidues_continuous (η : ℝ) (P : ℝ[X]) (σ : MomentShifts) :
    Continuous (fun q : ℝ => dpNormalizedFourResidues q η P σ) := by
  unfold dpNormalizedFourResidues
  fun_prop

theorem dp_phase_log_ratio_tendsto :
    Tendsto (fun T : ℝ => Real.log (T/(2*Real.pi))/Real.log T) atTop (𝓝 1) := by
  have hi : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have ht : Tendsto (fun T : ℝ => 1-Real.log (2*Real.pi)*(Real.log T)⁻¹)
      atTop (𝓝 (1-Real.log (2*Real.pi)*0)) := tendsto_const_nhds.sub (tendsto_const_nhds.mul hi)
  simp only [mul_zero, sub_zero] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hT0 : T ≠ 0 := (zero_lt_one.trans hT).ne'
  have hπ : (2*Real.pi : ℝ) ≠ 0 := by positivity
  have hL : Real.log T ≠ 0 := (Real.log_pos hT).ne'
  rw [Real.log_div hT0 hπ]
  field_simp [hL]

theorem dpFourResidues_normalized_tendsto (η : ℝ) (P : ℝ[X]) (σ : MomentShifts) :
    Tendsto (fun T : ℝ => dpFourResidues T (T^η) P (rawMomentShifts T σ)/
      (Real.log T : ℂ)^3) atTop (𝓝 (dpNormalizedFourResidues 1 η P σ)) := by
  have ht := (dpNormalizedFourResidues_continuous η P σ).continuousAt.tendsto.comp
    dp_phase_log_ratio_tendsto
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hL : (Real.log T : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne'
  rw [dpFourResidues_normalized hT]
  simp only [Function.comp_apply]
  field_simp [hL]

theorem logNormalizedRemainder_tendsto (E : ℝ → ℂ) (C : ℝ)
    (hE : ∀ᶠ T : ℝ in atTop, ‖E T‖ ≤ C*T*(Real.log T)^8) :
    Tendsto (fun T : ℝ => E T/((T : ℂ)*(Real.log T : ℂ)^9)) atTop (𝓝 0) := by
  have hb : ∀ᶠ T : ℝ in atTop,
      ‖E T/((T : ℂ)*(Real.log T : ℂ)^9)‖ ≤ C/(Real.log T) := by
    filter_upwards [hE, eventually_gt_atTop (1 : ℝ)] with T hE hT
    have hT0 := zero_lt_one.trans hT
    have hL := Real.log_pos hT
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT0, abs_of_pos hL]
    calc
      _ ≤ (C*T*(Real.log T)^8)/(T*(Real.log T)^9) :=
        div_le_div_of_nonneg_right hE (by positivity)
      _ = C/Real.log T := by field_simp
  have hi : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hc : Tendsto (fun T : ℝ => C/Real.log T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hi
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _)) hb hc

theorem dpRawMainTerm_normalized {T : ℝ} (hT : 1 < T) (η : ℝ)
    (P : ℝ[X]) (Φ : ℝ → ℝ) (σ : MomentShifts) :
    dpRawMainTerm T η P Φ (rawMomentShifts T σ)/((T : ℂ)*(Real.log T : ℂ)^9) =
      (arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*(η : ℂ)^6*
        dpNormalizedFourResidues (Real.log (T/(2*Real.pi))/Real.log T) η P σ := by
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hT).ne'
  have hL : (Real.log T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne'
  unfold dpRawMainTerm
  rw [Real.log_rpow (zero_lt_one.trans hT), dpFourResidues_normalized hT]
  push_cast
  field_simp

theorem dpActualMoment_normalized_tendsto (hsource : DPv2Input)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (σ : MomentShifts) (hσ : DPSeparated σ) :
    Tendsto (fun T : ℝ => chiTwistedFourthMoment T (rawMomentShifts T σ)
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ /
        ((T : ℂ)*(Real.log T : ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*(η : ℂ)^6*
        dpNormalizedFourResidues 1 η P σ)) := by
  obtain ⟨C, _, hC⟩ := hsource η hη hηu P Φ hΦ {σ} isCompact_singleton
    (by intro σ' hσ'; simpa only [mem_singleton_iff.mp hσ'] using hσ)
  let E : ℝ → ℂ := fun T => chiTwistedFourthMoment T (rawMomentShifts T σ)
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ-
    dpRawMainTerm T η P Φ (rawMomentShifts T σ)
  have hE := logNormalizedRemainder_tendsto E C (hC.mono (fun T h => h σ (by simp)))
  have hM : Tendsto (fun T : ℝ => dpRawMainTerm T η P Φ (rawMomentShifts T σ)/
      ((T : ℂ)*(Real.log T : ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*(η : ℂ)^6*
        dpNormalizedFourResidues 1 η P σ)) := by
    have ht := ((dpNormalizedFourResidues_continuous η P σ).continuousAt.tendsto.comp
      dp_phase_log_ratio_tendsto).const_mul
      ((arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*(η : ℂ)^6)
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact (dpRawMainTerm_normalized hT η P Φ σ).symm
  have ht := hM.add hE
  simp only [add_zero] at ht
  apply ht.congr
  intro T
  dsimp [E]
  ring

end
end Sechstmoment.Source
