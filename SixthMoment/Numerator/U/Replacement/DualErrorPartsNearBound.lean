import SixthMoment.Numerator.U.Replacement.DualErrorPartsContour
import SixthMoment.Numerator.U.Replacement.WeightReplacementNearBound

namespace SixthMoment
open Complex Source Real MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology ENNReal
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_actual_dual_error_part_near_finite_grid_uniform_mass_bound
    {a b c e κ θ R η ρ : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (he : 2*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ phasePart : Bool, ∀ m : Fin 6, ∀ v : ℝ, |v|≤θ*Real.log T →
      ‖a03ActualDualErrorPartNearFiniteMellinGrid phasePart c T a b η ρ v f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m)‖≤C*T^e*actualSmoothNearGlobalMass T a b η ρ := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨C₀,hC₀,hb₀⟩ := rectangular_dual_error_part_actual_time_uniform_schwartz_bound hΦ hc hc1 he hκ hθ hR
  let D := F*G*Real.exp (R*(Real.log 16+(2+η)))
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨D*C₀ 0,mul_nonneg hD (hC₀ 0),?_⟩
  have hsmall := rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4)
  filter_upwards [hb₀,hsmall,eventually_gt_atTop (0:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hb₀ hraw hT hlog
  intro σ hσ hroot phasePart m v hv
  let α := bblrSixShifts (rawMomentShifts T σ) m
  have hα : ∀ j, ‖α j‖≤1/4 := bblrSixShifts_norm_le _ (hraw σ hσ) m
  have hq (u w : ℕ) (n : Fin 4→ℕ) :
      ‖∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
        rectangularDualErrorPartMellinKernel phasePart T σ (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤
      ‖a03ActualMellinStaticFactor T f g α u w n ((c:ℂ)+(v:ℂ)*I)‖*C₀ 0*T^e := by
    simpa only [pow_zero,one_mul,a03ActualMellinStaticFactor] using
      hb₀ σ σ α hσ hα hroot phasePart v hv f g u w n 0
  exact a03_replacement_near_grid_norm_le_raw_mass (a := a) (b := b) (η := η) (ρ := ρ)
    hT hlog hR hc.le (hC₀ 0) hF hG f g hfb hgb σ hσ m v _ hq

theorem a03_actual_dual_error_part_near_finite_contour_uniform_mass_bound
    {a b c e κ θ R η ρ : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (he : 2*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ phasePart : Bool, ∀ m : Fin 6,
      IntegrableOn (fun v : ℝ => a03ActualDualErrorPartNearFiniteMellinGrid phasePart c T a b η ρ v f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m)) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualDualErrorPartNearFiniteContour phasePart c T a b η ρ θ f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m)‖≤
        C*(1+Real.log T)*T^e*actualSmoothNearGlobalMass T a b η ρ := by
  obtain ⟨C,hC,hb⟩ := a03_actual_dual_error_part_near_finite_grid_uniform_mass_bound
    hf hg hΦ hc hc1 he hκ hθ hR (η := η) (ρ := ρ)
  let P : ℝ := 1/(2*Real.pi)
  have hP : 0≤P := by dsimp [P]; positivity
  refine ⟨2*θ*P*C,by positivity,?_⟩
  have hsmall := rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4)
  filter_upwards [hb,hsmall,eventually_ge_atTop (1:ℝ)] with T hb hraw hT
  intro σ hσ hroot phasePart m
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hL : 0≤Real.log T := Real.log_nonneg hT
  have hθL : 0≤θ*Real.log T := mul_nonneg hθ hL
  let B := C*T^e*actualSmoothNearGlobalMass T a b η ρ
  have hB : 0≤B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hTp.le _))
      (actualSmoothNearGlobalMass_nonneg T a b η ρ)
  let α := bblrSixShifts (rawMomentShifts T σ) m
  have hα : ∀ j, ‖α j‖≤1/4 := bblrSixShifts_norm_le _ (hraw σ hσ) m
  have hvbound (v : ℝ) (hv : v∈Icc (-θ*Real.log T) (θ*Real.log T)) :
      ‖a03ActualDualErrorPartNearFiniteMellinGrid phasePart c T a b η ρ v f g Φ σ α‖≤B :=
    hb σ hσ hroot phasePart m v (abs_le.mpr (by simpa only [neg_mul,Set.mem_Icc] using hv))
  have hm := a03ActualDualErrorPartNearFiniteMellinGrid_frequency_stronglyMeasurable
    phasePart hc T a b η ρ f g Φ hΦ σ α hα (hraw σ hσ)
  have hsfinite : volume (Icc (-θ*Real.log T) (θ*Real.log T))<∞ := isCompact_Icc.measure_lt_top
  have hi : IntegrableOn (fun v : ℝ => a03ActualDualErrorPartNearFiniteMellinGrid phasePart c T a b η ρ v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T)) := by
    apply IntegrableOn.of_bound hsfinite hm.aestronglyMeasurable B
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with v hv
    exact hvbound v hv
  refine ⟨hi,?_⟩
  have hmeasure : volume.real (Icc (-θ*Real.log T) (θ*Real.log T))=2*θ*Real.log T := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  have hint := norm_setIntegral_le_of_norm_le_const hsfinite hvbound
  rw [hmeasure] at hint
  have hconst : ‖(1/(2*Real.pi):ℂ)‖=P := by
    dsimp [P]
    rw [show (1/(2*Real.pi):ℂ)=((1/(2*Real.pi):ℝ):ℂ) by push_cast; rfl,
      Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  unfold a03ActualDualErrorPartNearFiniteContour
  rw [norm_mul,hconst]
  calc
    _≤P*(B*(2*θ*Real.log T)) := mul_le_mul_of_nonneg_left hint hP
    _=(2*θ*P*C)*(Real.log T)*T^e*actualSmoothNearGlobalMass T a b η ρ := by dsimp [B]; ring
    _≤_ := by
      gcongr
      · exact actualSmoothNearGlobalMass_nonneg T a b η ρ
      · linarith

end
end SixthMoment
