import Sechstmoment.Numerator.U.Diagonal.ActualSmoothNearGlobal
import Sechstmoment.Numerator.U.Diagonal.RawShiftFactorMass
import Sechstmoment.Numerator.U.Replacement.DualWeightReplacementContour

/-! Actual original and dual weight/phase errors are summed over the complete
retained near AFE grid. Genuine raw coefficients feed the proved near mass;
no weighted-error or moment-asymptotic hypothesis is introduced. -/
namespace Sechstmoment
open Complex Source Real MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology ENNReal
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_replacement_near_grid_norm_le_raw_mass
    {T R c a b η ρ e C F G : ℝ} (hT : 0<T) (hlog : 1≤Real.log T)
    (hR : 0≤R) (hc : 0≤c) (hC : 0≤C) (hF : 0≤F) (hG : 0≤G)
    (f g : ℝ→ℝ) (hf : ∀ x, ‖f x‖≤F) (hg : ∀ x, ‖g x‖≤G)
    (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖≤R) (m : Fin 6) (v : ℝ)
    (q : ℕ→ℕ→(Fin 4→ℕ)→ℂ)
    (hq : ∀ u w n, ‖q u w n‖≤
      ‖a03ActualMellinStaticFactor T f g (bblrSixShifts (rawMomentShifts T σ) m)
        u w n ((c:ℂ)+(v:ℂ)*I)‖*C*T^e) :
    ‖∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
      ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
        if a03ActualWeightReplacementNearSelection T ρ u w n then
          (rectangularAFESmoothWeight k n:ℂ)*q u w n else 0‖≤
      (F*G*Real.exp (R*(Real.log 16+(2+η)))*C)*T^e*actualSmoothNearGlobalMass T a b η ρ := by
  let D := F*G*Real.exp (R*(Real.log 16+(2+η)))*C
  have hD : 0≤D := by dsimp [D]; positivity
  have hpoint (u w : ℕ) (k n : Fin 4→ℕ) (hk : k∈rectangularAFEProductScaleGrid (T^(2+η))) :
      ‖if a03ActualWeightReplacementNearSelection T ρ u w n then
        (rectangularAFESmoothWeight k n:ℂ)*q u w n else 0‖≤
      D*T^e*(if a03ActualWeightReplacementNearSelection T ρ u w n then
        rectangularAFESmoothWeight k n*positiveNearFactorWeight (u+1) (w+1) (bblrAFEFactorPairs n) else 0) := by
    by_cases hn : a03ActualWeightReplacementNearSelection T ρ u w n
    · simp only [hn,ite_true]
      by_cases hw : rectangularAFESmoothWeight k n=0
      · simp [hw]
      · rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (rectangular_AFE_smooth_weight_nonneg k n)]
        have hs := a03ActualMellinStaticFactor_raw_grid_norm_le hT hlog hR hc
          f g hF hG hf hg σ hσ m k n hk hw u w v
        calc
          _≤rectangularAFESmoothWeight k n*
              (‖a03ActualMellinStaticFactor T f g (bblrSixShifts (rawMomentShifts T σ) m)
                u w n ((c:ℂ)+(v:ℂ)*I)‖*C*T^e) :=
            mul_le_mul_of_nonneg_left (hq u w n) (rectangular_AFE_smooth_weight_nonneg k n)
          _≤rectangularAFESmoothWeight k n*
              ((F*G*Real.exp (R*(Real.log 16+(2+η)))*
                positiveNearFactorWeight (u+1) (w+1) (bblrAFEFactorPairs n))*C*T^e) := by
            gcongr
            exact rectangular_AFE_smooth_weight_nonneg k n
          _=_ := by dsimp [D]; ring
    · simp [hn]
  calc
    _≤∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
          ‖if a03ActualWeightReplacementNearSelection T ρ u w n then
            (rectangularAFESmoothWeight k n:ℂ)*q u w n else 0‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro u _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro w _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => norm_sum_le _ _))
    _≤∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)), ∑ n∈rectangularAFESmoothBox k,
          D*T^e*(if a03ActualWeightReplacementNearSelection T ρ u w n then
            rectangularAFESmoothWeight k n*positiveNearFactorWeight (u+1) (w+1) (bblrAFEFactorPairs n) else 0) := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro w _
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.sum_le_sum (fun n _ => hpoint u w k n hk)
    _=_ := by
      unfold actualSmoothNearGlobalMass actualSmoothNearWeightedMass
      simp only [Finset.mul_sum]
      rfl

/-- Both actual near branches, including the true dual multiplier and its
phase error, inherit the complete proved raw arithmetic mass. -/
theorem a03_actual_weight_replacement_near_finite_grid_uniform_mass_bound
    {a b c e κ θ R η ρ : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (he : 2*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ m : Fin 6, ∀ v : ℝ, |v|≤θ*Real.log T →
      ‖a03ActualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m)‖+
      ‖a03ActualDualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m)‖≤C*T^e*actualSmoothNearGlobalMass T a b η ρ := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨C₀,hC₀,hb₀⟩ := rectangular_weight_replacement_actual_time_uniform_schwartz_bound hΦ hc hc1 he hκ hθ
  obtain ⟨C₁,hC₁,hb₁⟩ := rectangular_dual_replacement_actual_time_uniform_schwartz_bound hΦ hc hc1 he hκ hθ hR
  let D := F*G*Real.exp (R*(Real.log 16+(2+η)))
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨D*(C₀ 0+C₁ 0),mul_nonneg hD (add_nonneg (hC₀ 0) (hC₁ 0)),?_⟩
  have hsmall := rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4)
  filter_upwards [hb₀,hb₁,hsmall,eventually_gt_atTop (0:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hb₀ hb₁ hraw hT hlog
  intro σ hσ hroot m v hv
  let α := bblrSixShifts (rawMomentShifts T σ) m
  have hα : ∀ j, ‖α j‖≤1/4 := bblrSixShifts_norm_le _ (hraw σ hσ) m
  have hq₀ (u w : ℕ) (n : Fin 4→ℕ) :
      ‖∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
        rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤
      ‖a03ActualMellinStaticFactor T f g α u w n ((c:ℂ)+(v:ℂ)*I)‖*C₀ 0*T^e := by
    simpa only [pow_zero,one_mul,a03ActualMellinStaticFactor] using hb₀ σ α hα hroot v hv f g u w n 0
  have hq₁ (u w : ℕ) (n : Fin 4→ℕ) :
      ‖∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
        rectangularDualReplacementMellinKernel T σ (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤
      ‖a03ActualMellinStaticFactor T f g α u w n ((c:ℂ)+(v:ℂ)*I)‖*C₁ 0*T^e := by
    simpa only [pow_zero,one_mul,a03ActualMellinStaticFactor] using hb₁ σ σ α hσ hα hroot v hv f g u w n 0
  have h₀ := a03_replacement_near_grid_norm_le_raw_mass (a := a) (b := b) (η := η) (ρ := ρ)
    hT hlog hR hc.le (hC₀ 0) hF hG f g hfb hgb σ hσ m v _ hq₀
  have h₁ := a03_replacement_near_grid_norm_le_raw_mass (a := a) (b := b) (η := η) (ρ := ρ)
    hT hlog hR hc.le (hC₁ 0) hF hG f g hfb hgb σ hσ m v _ hq₁
  exact (add_le_add h₀ h₁).trans_eq (by dsimp [D]; ring)


/-- Both complete near Mellin contours are integrable and carry the genuine
full arithmetic mass, with only the actual contour-length logarithm lost. -/
theorem a03_actual_weight_replacement_near_finite_contour_uniform_mass_bound
    {a b c e κ θ R η ρ : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (he : 2*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ m₀ m₁ : Fin 6,
      IntegrableOn (fun v : ℝ => a03ActualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m₀)) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      IntegrableOn (fun v : ℝ => a03ActualDualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m₁)) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualWeightReplacementNearFiniteContour c T a b η ρ θ f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m₀)‖+
      ‖a03ActualDualWeightReplacementNearFiniteContour c T a b η ρ θ f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m₁)‖≤
        C*(1+Real.log T)*T^e*actualSmoothNearGlobalMass T a b η ρ := by
  obtain ⟨C,hC,hb⟩ := a03_actual_weight_replacement_near_finite_grid_uniform_mass_bound
    hf hg hΦ hc hc1 he hκ hθ hR (η := η) (ρ := ρ)
  let P : ℝ := 1/(2*Real.pi)
  have hP : 0≤P := by dsimp [P]; positivity
  refine ⟨4*θ*P*C,by positivity,?_⟩
  have hsmall := rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4)
  filter_upwards [hb,hsmall,eventually_ge_atTop (1:ℝ)] with T hb hraw hT
  intro σ hσ hroot m₀ m₁
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hL : 0≤Real.log T := Real.log_nonneg hT
  have hθL : 0≤θ*Real.log T := mul_nonneg hθ hL
  let B := C*T^e*actualSmoothNearGlobalMass T a b η ρ
  have hB : 0≤B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hTp.le _))
      (actualSmoothNearGlobalMass_nonneg T a b η ρ)
  let α₀ := bblrSixShifts (rawMomentShifts T σ) m₀
  let α₁ := bblrSixShifts (rawMomentShifts T σ) m₁
  have hα₀ : ∀ j, ‖α₀ j‖≤1/4 := bblrSixShifts_norm_le _ (hraw σ hσ) m₀
  have hα₁ : ∀ j, ‖α₁ j‖≤1/4 := bblrSixShifts_norm_le _ (hraw σ hσ) m₁
  have hv₀ (v : ℝ) (hv : v∈Icc (-θ*Real.log T) (θ*Real.log T)) :
      ‖a03ActualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ α₀‖≤B := by
    have h := hb σ hσ hroot m₀ v (abs_le.mpr (by simpa only [neg_mul,Set.mem_Icc] using hv))
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans h
  have hv₁ (v : ℝ) (hv : v∈Icc (-θ*Real.log T) (θ*Real.log T)) :
      ‖a03ActualDualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ α₁‖≤B := by
    have h := hb σ hσ hroot m₁ v (abs_le.mpr (by simpa only [neg_mul,Set.mem_Icc] using hv))
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans h
  have hm₀ := a03ActualWeightReplacementNearFiniteMellinGrid_frequency_stronglyMeasurable
    hc T a b η ρ f g Φ hΦ σ α₀ hα₀
  have hm₁ := a03ActualDualWeightReplacementNearFiniteMellinGrid_frequency_stronglyMeasurable
    hc T a b η ρ f g Φ hΦ σ α₁ hα₁ (hraw σ hσ)
  have hsfinite : volume (Icc (-θ*Real.log T) (θ*Real.log T))<∞ := isCompact_Icc.measure_lt_top
  have hi₀ : IntegrableOn (fun v : ℝ => a03ActualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ α₀)
      (Icc (-θ*Real.log T) (θ*Real.log T)) := by
    apply IntegrableOn.of_bound hsfinite hm₀.aestronglyMeasurable B
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with v hv
    exact hv₀ v hv
  have hi₁ : IntegrableOn (fun v : ℝ => a03ActualDualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ α₁)
      (Icc (-θ*Real.log T) (θ*Real.log T)) := by
    apply IntegrableOn.of_bound hsfinite hm₁.aestronglyMeasurable B
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with v hv
    exact hv₁ v hv
  refine ⟨hi₀,hi₁,?_⟩
  have hmeasure : volume.real (Icc (-θ*Real.log T) (θ*Real.log T))=2*θ*Real.log T := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  have h₀ := norm_setIntegral_le_of_norm_le_const hsfinite hv₀
  have h₁ := norm_setIntegral_le_of_norm_le_const hsfinite hv₁
  rw [hmeasure] at h₀ h₁
  have hconst : ‖(1/(2*Real.pi):ℂ)‖=P := by
    dsimp [P]
    rw [show (1/(2*Real.pi):ℂ)=((1/(2*Real.pi):ℝ):ℂ) by push_cast; rfl,
      Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  unfold a03ActualWeightReplacementNearFiniteContour a03ActualDualWeightReplacementNearFiniteContour
  rw [norm_mul,hconst,norm_mul,hconst]
  calc
    _≤P*(B*(2*θ*Real.log T))+P*(B*(2*θ*Real.log T)) :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ hP) (mul_le_mul_of_nonneg_left h₁ hP)
    _=(4*θ*P*C)*(Real.log T)*T^e*actualSmoothNearGlobalMass T a b η ρ := by dsimp [B]; ring
    _≤_ := by
      gcongr
      · exact actualSmoothNearGlobalMass_nonneg T a b η ρ
      · linarith

end
end Sechstmoment
