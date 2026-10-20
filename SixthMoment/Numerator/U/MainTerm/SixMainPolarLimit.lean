import SixthMoment.Numerator.U.Diagonal.ActualSixMainContour
import SixthMoment.Numerator.U.MainTerm.IntegratedProfileRemainder
import SixthMoment.Numerator.U.MainTerm.SixPrincipalLimit


namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem bblrSixMainTerms_eq_principal_add_actualRemainder {T a b δ : ℝ}
    (hT : 1 < T) (hδ : 0 < δ) (hδ1 : δ < 1/4) (σ : MomentShifts)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hρ : ∀ k : PurePolarIndex, purePolarRoot T σ k ≠ 0)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ)
    (hrest : Integrable (fun t : ℝ => ∑ m : Fin 6, (Φ (t/T):ℂ)*
      (t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)*
      actualIntegratedProfileRemainder T σ m (fun x => (f x:ℂ))
        (fun x => (g x:ℂ)) (Real.log T) δ (t/(2*π)))) :
    bblrSixMainTerms T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ =
      actualSixPrincipalMoment T σ (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ δ+
      actualSixProfileRemainderMoment T σ (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ δ := by
  rw [bblrSixMainTerms_eq_shiftedProfiles hT hδ hδ1 σ hα hρ f g Φ hf hg hΦ]
  unfold actualSixPrincipalMoment actualSixProfileRemainderMoment
  rw [← integral_add (actualSixPrincipalMoment_time_integrable
    (zero_lt_one.trans hT) σ (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ hΦ δ) hrest]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : 0 < t
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    have hs := actualProfilePrincipal_add_remainder_integral T σ m (x := t/(2*π)) (Real.log_pos hT)
      hδ hδ1 (div_pos ht (by positivity)) hα (fun ij => hρ (m,ij))
      (hf.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
      (Complex.ofRealCLM.contDiff.comp hf.1)
      (hg.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
      (Complex.ofRealCLM.contDiff.comp hg.1)
    change ((Φ (t/T):ℂ)*(t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m))*
      (((Real.log T:ℂ)/(2*π))^2*∫ y : ℝ × ℝ,
        actualProfileTransformProduct (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) (Real.log T) δ y*
          (polarMellinRemovedKernel T σ m ((δ:ℂ)+(y.1:ℂ)*I) ((δ:ℂ)+(y.2:ℂ)*I) 0+
            polarMellinRemainderIntegral T σ m ((δ:ℂ)+(y.1:ℂ)*I) ((δ:ℂ)+(y.2:ℂ)*I)
              (t/(2*π)) δ) ∂(volume.prod volume)) = _
    simp only [Function.comp_def] at hs
    rw [hs]
    dsimp [actualPrincipalProfileIntegral,actualPrincipalProfileLineKernel,
      actualIntegratedProfileRemainder,actualProfileTransformProduct]
    ring
  · have hz : Φ (t/T)=0 := by
      by_contra hn
      have hl := (hΦ.2 (subset_tsupport Φ hn)).1
      have htl : T ≤ t := by
        simpa only [one_mul] using (le_div_iff₀ (zero_lt_one.trans hT)).mp hl
      linarith
    simp only [hz,Complex.ofReal_zero,zero_mul,Finset.sum_const_zero,zero_add]

theorem actualSmoothSixProfileRemainderMoment_normalized_tendsto
    {R δ κ a b : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ)
    (hab : a+b < 1) (σ : MomentShifts) (hσ : ∀ j : Fin 4, ‖σ j‖ ≤ R)
    (hgap : ∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖)
    {f g : ℝ → ℝ} (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ =>
      actualSixProfileRemainderMoment T σ (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ δ/
        ((T:ℂ)*(Real.log T:ℂ)^9)) atTop (𝓝 0) := by
  apply logNormalizedRemainder_tendsto _ 1
  filter_upwards [actualSmoothSixProfileRemainderMoment_uniform_eventually_negligible
    hR hδ hδ1 hκ hab hf hg Φ hΦ 1 (by norm_num),
    eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hb hT hL
  have hp : 1 ≤ (Real.log T)^8 := one_le_pow₀ hL
  calc
    _ ≤ T := by simpa only [one_mul] using hb σ hσ hgap
    _ ≤ 1*T*(Real.log T)^8 := by nlinarith

theorem bblrSixMainTerms_fixed_separated_polar_limit {R c δ κ a b : ℝ}
    (hR : 0 ≤ R) (hc : 4*R+1 ≤ c) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ)
    (hab : a+b < 1) (σ : MomentShifts) (hσ : ∀ j : Fin 4, ‖σ j‖ ≤ R)
    (hgap : ∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ =>
      bblrSixMainTerms T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ/
        ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 (actualSixPrincipalPolarLimit σ (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ c)) := by
  have hρ : ∀ k : PurePolarIndex, normalizedPurePolarRoot σ k ≠ 0 := fun k =>
    norm_pos_iff.mp (hκ.trans_le (hgap k))
  have hp := actualSixPrincipalMoment_polar_limit hR hc hδ σ hσ hρ
    (hf.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hf.1)
    (hg.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hg.1) Φ hΦ
  have he := actualSmoothSixProfileRemainderMoment_normalized_tendsto
    hR hδ hδ1 hκ hab σ hσ hgap hf hg Φ hΦ
  have hs := hp.add he
  simp only [add_zero] at hs
  apply hs.congr'
  obtain ⟨C,_hC,hrest⟩ :=
    actualSmoothSixProfileRemainderMoment_uniform_eventually_integrable_power_bound
      hR hδ hδ1 hκ hab hf hg Φ hΦ
  filter_upwards [hrest,eventually_gt_atTop (1:ℝ),
    rawMomentShifts_uniform_eventually_small hR (show 0 < δ/4 by positivity)]
    with T hrest hT hα
  have hρT : ∀ k : PurePolarIndex, purePolarRoot T σ k ≠ 0 := by
    intro k
    rw [purePolarRoot_normalized]
    exact div_ne_zero (hρ k) (Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne')
  rw [bblrSixMainTerms_eq_principal_add_actualRemainder hT hδ hδ1 σ
    (hα σ hσ) hρT f g Φ hf hg hΦ (hrest σ hσ hgap).1,add_div]
  rfl

end
end SixthMoment
