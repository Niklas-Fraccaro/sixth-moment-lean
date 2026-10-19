import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Sechstmoment.Numerator.V.DP.DPPhaseControl

/-!
# Own uniform smoothing of DP's actual sharp moment

The external input is only `DPv2SharpInput`. Endpoint phase replacement and
partial summation are own proofs; the resulting constant is uniform in a
bounded family of smooth weights and on compact separated shift sets.
-/
namespace Sechstmoment.Source
open Complex MeasureTheory Set Polynomial Filter
open scoped Topology
noncomputable section

theorem dpRawSharpMainTerm_phase_bound {T X C : ℝ} (hT : 1 < T)
    (hL : dpPhaseWindowConstant ≤ Real.log T) (hX : X ∈ Icc (T/4) (2*T))
    (hC : 0 ≤ C) (η : ℝ) (P : ℝ[X]) (σ : MomentShifts)
    (hslope : ∀ q ∈ Icc (0 : ℝ) 2, ‖dpNormalizedFourSlope q η P σ‖ ≤ C) :
    ‖dpRawSharpMainTerm T X η P σ-(X : ℂ)*dpLeadingDensity T η P σ‖ ≤
      (2*‖(arithmeticFactor : ℂ)‖*|η|^6*C*dpPhaseWindowConstant)*T*(Real.log T)^8 := by
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity : 0 < T/4) hX.1
  have hLp : 0 < Real.log T := Real.log_pos hT
  have hnorm := dpNormalizedFour_phase_lipschitz η P σ
    (dp_phase_endpoint_in_window hT hL hX) hslope
  have hn : ‖dpNormalizedFourResidues (Real.log (X/(2*Real.pi))/Real.log T) η P σ-
      dpNormalizedFourResidues 1 η P σ‖ ≤ C*dpPhaseWindowConstant/Real.log T := by
    calc
      _ ≤ C*|Real.log (X/(2*Real.pi))/Real.log T-1| := hnorm
      _ ≤ C*(dpPhaseWindowConstant/Real.log T) :=
        mul_le_mul_of_nonneg_left (dp_phase_endpoint_bound hT hX) hC
      _ = _ := by ring
  have he : dpRawSharpMainTerm T X η P σ-(X : ℂ)*dpLeadingDensity T η P σ =
      (X : ℂ)*(arithmeticFactor : ℂ)*(Real.log T : ℂ)^9*(η : ℂ)^6*
        (dpNormalizedFourResidues (Real.log (X/(2*Real.pi))/Real.log T) η P σ-
          dpNormalizedFourResidues 1 η P σ) := by
    rw [dpRawSharpMainTerm_normalized hT]
    unfold dpLeadingDensity
    ring
  rw [he]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hX0, abs_of_pos hLp]
  calc
    _ ≤ (2*T) * |arithmeticFactor| * (Real.log T)^9 * |η|^6 *
        (C*dpPhaseWindowConstant/Real.log T) := by
      apply mul_le_mul
      · gcongr
        exact hX.2
      · exact hn
      · exact norm_nonneg _
      · positivity
    _ = _ := by field_simp

theorem dpSharpMoment_linear_error_bound (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (K : Set MomentShifts) (hK : IsCompact K) (hsep : ∀ σ ∈ K, DPSeparated σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ X ∈ Icc T (2*T),
      ‖dpSharpMoment T X η P σ-(X : ℂ)*dpLeadingDensity T η P σ‖ ≤ C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,hsharp⟩ := hsource η hη hηu P K hK hsep
  obtain ⟨D,hD,hslope⟩ := dpNormalizedFourSlope_compact_bound η P K hK hsep
  let E := 2*‖(arithmeticFactor : ℂ)‖*|η|^6*D*dpPhaseWindowConstant
  have hE : 0 ≤ E := by
    have := dpPhaseWindowConstant_nonneg
    dsimp [E]
    positivity
  refine ⟨C+E, add_nonneg hC hE, ?_⟩
  filter_upwards [hsharp, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop dpPhaseWindowConstant)]
    with T hsharp hT hL σ hσ X hX
  have hX' : X ∈ Icc (T/4) (2*T) := ⟨by linarith [hX.1],hX.2⟩
  calc
    _ ≤ ‖dpSharpMoment T X η P σ-dpRawSharpMainTerm T X η P σ‖+
        ‖dpRawSharpMainTerm T X η P σ-(X : ℂ)*dpLeadingDensity T η P σ‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C*T*(Real.log T)^8+E*T*(Real.log T)^8 :=
      add_le_add (hsharp σ hσ X hX')
        (dpRawSharpMainTerm_phase_bound hT hL hX' hD η P σ (hslope σ hσ))
    _ = _ := by ring

theorem rawMomentShifts_strip_eventually (K : Set MomentShifts) (hK : IsCompact K) :
    ∀ᶠ T : ℝ in atTop, 1 < T ∧ ∀ σ ∈ K, ∀ j : Fin 4,
      |(rawMomentShifts T σ j).re| < 1/2 := by
  obtain ⟨R,hRpos,hR⟩ := hK.isBounded.exists_pos_norm_le
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (2*R))] with T hT hL
  refine ⟨hT,?_⟩
  intro σ hσ j
  have hLp := Real.log_pos hT
  have hj : ‖σ j‖ ≤ R := (norm_le_pi_norm σ j).trans (hR σ hσ)
  calc
    _ ≤ ‖rawMomentShifts T σ j‖ := Complex.abs_re_le_norm _
    _ = ‖σ j‖/Real.log T := by
      rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
    _ ≤ R/Real.log T := div_le_div_of_nonneg_right hj hLp.le
    _ < 1/2 := (div_lt_iff₀ hLp).mpr (by linarith)

theorem dpProfile_zero_above (η : ℝ) (P : ℝ[X]) :
    ∀ x, η < x → zeroExtendedPolynomialProfile η P x=0 := by
  intro x hx
  simp [zeroExtendedPolynomialProfile,not_lt_of_ge hx.le]

theorem dpActualMoment_uniform_smoothing (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (K : Set MomentShifts) (hK : IsCompact K) (hsep : ∀ σ ∈ K, DPSeparated σ)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → (∀ x, |deriv Φ x| ≤ B) →
      ‖chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ-
        (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpLeadingDensity T η P σ‖ ≤
          C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,hsharp⟩ := dpSharpMoment_linear_error_bound hsource η hη hηu P K hK hsep
  refine ⟨2*B*C,by positivity,?_⟩
  filter_upwards [hsharp,rawMomentShifts_strip_eventually K hK] with T hsharp hstrip σ hσ Φ hΦ hderiv
  let H : ℝ → ℂ := fun t => chiTwistedFourthIntegrand T t (rawMomentShifts T σ)
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) (fun _ => 1)
  have hH : Continuous H := chiTwistedFourthIntegrand_continuous hstrip.1 η _ _ _ _
    (hstrip.2 σ hσ) (dpProfile_zero_above η P) (dpProfile_zero_above η P) continuous_const
  have hE : 0 ≤ C*T*(Real.log T)^8 := by
    have hT0 : 0 < T := zero_lt_one.trans hstrip.1
    positivity
  have hb := dyadic_smoothing_error_bound hstrip.1 hB hE H hH (dpLeadingDensity T η P σ)
    (hsharp σ hσ) Φ hΦ hderiv
  rw [dyadic_weighted_centered_integral (zero_lt_one.trans hstrip.1) H hH _ Φ hΦ] at hb
  have he : (∫ t : ℝ, (Φ (t/T) : ℂ)*H t) =
      chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ := by
    unfold chiTwistedFourthMoment
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by simp [H,chiTwistedFourthIntegrand]; ring)
  rw [he] at hb
  convert hb using 1
  ring

end
end Sechstmoment.Source
