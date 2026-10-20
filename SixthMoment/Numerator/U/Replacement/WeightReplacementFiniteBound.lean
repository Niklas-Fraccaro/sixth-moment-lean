import SixthMoment.Numerator.U.Replacement.WeightReplacementNearBound

namespace SixthMoment
open Complex Source Real MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology ENNReal
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_actual_weight_replacement_near_finite_contour_uniform_power_bound
    {a b c e κ θ R η ρ d q : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (he : 2*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hη : 0<η) (hd : 0<d)
    (hp : a+b+ρ+η/2+e+d≤q) (hr : 1/2+a+b+η/4+e+d≤q) :
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
        (bblrSixShifts (rawMomentShifts T σ) m₁)‖≤C*T^q := by
  obtain ⟨C,hC,hb⟩ := a03_actual_weight_replacement_near_finite_contour_uniform_mass_bound
    hf hg hΦ hc hc1 he hκ hθ hR (η := η) (ρ := ρ)
  obtain ⟨D,hD,hmass⟩ := actualSmoothNearGlobalMass_uniform_power_budget hη a b ρ
  let L : ℝ := ((7:ℕ).factorial:ℝ)/d^7*Real.exp d
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨2*C*D*L,by positivity,?_⟩
  filter_upwards [hb,hmass,eventually_ge_atTop (1:ℝ)] with T hb hm hT
  intro σ hσ hroot m₀ m₁
  obtain ⟨hi₀,hi₁,hnear⟩ := hb σ hσ hroot m₀ m₁
  refine ⟨hi₀,hi₁,?_⟩
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hlog : 0≤1+Real.log T := by linarith [Real.log_nonneg hT]
  have hpoly : (1+Real.log T)^7≤L*T^d := logarithmic_power_le_rpow hd hT 7
  have hCp : 0≤C*(1+Real.log T)*T^e := by positivity
  calc
    _≤C*(1+Real.log T)*T^e*actualSmoothNearGlobalMass T a b η ρ := hnear
    _≤C*(1+Real.log T)*T^e*(D*(1+Real.log T)^6*
        (T^(a+b+ρ+η/2)+T^(1/2+a+b+η/4))) := mul_le_mul_of_nonneg_left hm hCp
    _=(C*D)*(1+Real.log T)^7*(T^(a+b+ρ+η/2+e)+T^(1/2+a+b+η/4+e)) := by
      rw [Real.rpow_add hTp (a+b+ρ+η/2) e,Real.rpow_add hTp (1/2+a+b+η/4) e]
      ring
    _≤(C*D)*(L*T^d)*(T^(a+b+ρ+η/2+e)+T^(1/2+a+b+η/4+e)) := by gcongr
    _=(C*D*L)*(T^(a+b+ρ+η/2+e+d)+T^(1/2+a+b+η/4+e+d)) := by
      rw [Real.rpow_add hTp (a+b+ρ+η/2+e) d,Real.rpow_add hTp (1/2+a+b+η/4+e) d]
      ring
    _≤(C*D*L)*(T^q+T^q) := mul_le_mul_of_nonneg_left
      (add_le_add (Real.rpow_le_rpow_of_exponent_le hT hp)
        (Real.rpow_le_rpow_of_exponent_le hT hr)) (by positivity)
    _=_ := by ring

private theorem original_contour_near_add_far {T : ℝ} (hT : 0<T)
    (c a b η ρ θ : ℝ) (f g Φ : ℝ→ℝ) (σ α : MomentShifts)
    (h_near : IntegrableOn (fun v : ℝ => a03ActualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T)))
    (h_plus : IntegrableOn (fun v : ℝ => a03ActualWeightReplacementFarFiniteMellinGrid true c T a b η ρ v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T)))
    (h_minus : IntegrableOn (fun v : ℝ => a03ActualWeightReplacementFarFiniteMellinGrid false c T a b η ρ v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T))) :
    IntegrableOn (fun v : ℝ => a03ActualWeightReplacementFiniteMellinGrid c T a b η v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
    a03ActualWeightReplacementFiniteContour c T a b η θ f g Φ σ α=
      a03ActualWeightReplacementNearFiniteContour c T a b η ρ θ f g Φ σ α+
      a03ActualWeightReplacementFarFiniteContour true c T a b η ρ θ f g Φ σ α+
      a03ActualWeightReplacementFarFiniteContour false c T a b η ρ θ f g Φ σ α := by
  have he : (fun v : ℝ => a03ActualWeightReplacementFiniteMellinGrid c T a b η v f g Φ σ α)=
      (fun v : ℝ => a03ActualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ α+
        a03ActualWeightReplacementFarFiniteMellinGrid true c T a b η ρ v f g Φ σ α+
        a03ActualWeightReplacementFarFiniteMellinGrid false c T a b η ρ v f g Φ σ α) :=
    funext (fun v => a03ActualWeightReplacementFiniteMellinGrid_near_add_far hT c a b η ρ v f g Φ σ α)
  refine ⟨by rw [he]; exact (h_near.add h_plus).add h_minus,?_⟩
  unfold a03ActualWeightReplacementFiniteContour a03ActualWeightReplacementNearFiniteContour
    a03ActualWeightReplacementFarFiniteContour
  have hI := integral_add (h_near.add h_plus) h_minus
  simp only [Pi.add_apply] at hI
  rw [he,hI,integral_add h_near h_plus]
  ring

private theorem dual_contour_near_add_far {T : ℝ} (hT : 0<T)
    (c a b η ρ θ : ℝ) (f g Φ : ℝ→ℝ) (σ α : MomentShifts)
    (h_near : IntegrableOn (fun v : ℝ => a03ActualDualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T)))
    (h_plus : IntegrableOn (fun v : ℝ => a03ActualDualWeightReplacementFarFiniteMellinGrid true c T a b η ρ v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T)))
    (h_minus : IntegrableOn (fun v : ℝ => a03ActualDualWeightReplacementFarFiniteMellinGrid false c T a b η ρ v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T))) :
    IntegrableOn (fun v : ℝ => a03ActualDualWeightReplacementFiniteMellinGrid c T a b η v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
    a03ActualDualWeightReplacementFiniteContour c T a b η θ f g Φ σ α=
      a03ActualDualWeightReplacementNearFiniteContour c T a b η ρ θ f g Φ σ α+
      a03ActualDualWeightReplacementFarFiniteContour true c T a b η ρ θ f g Φ σ α+
      a03ActualDualWeightReplacementFarFiniteContour false c T a b η ρ θ f g Φ σ α := by
  have he : (fun v : ℝ => a03ActualDualWeightReplacementFiniteMellinGrid c T a b η v f g Φ σ α)=
      (fun v : ℝ => a03ActualDualWeightReplacementNearFiniteMellinGrid c T a b η ρ v f g Φ σ α+
        a03ActualDualWeightReplacementFarFiniteMellinGrid true c T a b η ρ v f g Φ σ α+
        a03ActualDualWeightReplacementFarFiniteMellinGrid false c T a b η ρ v f g Φ σ α) :=
    funext (fun v => a03ActualDualWeightReplacementFiniteMellinGrid_near_add_far hT c a b η ρ v f g Φ σ α)
  refine ⟨by rw [he]; exact (h_near.add h_plus).add h_minus,?_⟩
  unfold a03ActualDualWeightReplacementFiniteContour a03ActualDualWeightReplacementNearFiniteContour
    a03ActualDualWeightReplacementFarFiniteContour
  have hI := integral_add (h_near.add h_plus) h_minus
  simp only [Pi.add_apply] at hI
  rw [he,hI,integral_add h_near h_plus]
  ring

theorem a03_actual_weight_replacement_finite_contour_uniform_power_bound
    {a b c e κ θ R η ρ d q : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (he : 2*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hη : 0<η) (hρ : 0<ρ) (hρ1 : ρ≤1) (hd : 0<d)
    (hq : 0≤q) (hp : a+b+ρ+η/2+e+d≤q) (hr : 1/2+a+b+η/4+e+d≤q) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ m₀ m₁ : Fin 6,
      IntegrableOn (fun v : ℝ => a03ActualWeightReplacementFiniteMellinGrid c T a b η v f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m₀)) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      IntegrableOn (fun v : ℝ => a03ActualDualWeightReplacementFiniteMellinGrid c T a b η v f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m₁)) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualWeightReplacementFiniteContour c T a b η θ f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m₀)‖+
      ‖a03ActualDualWeightReplacementFiniteContour c T a b η θ f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m₁)‖≤C*T^q := by
  obtain ⟨N,hN,hnear⟩ := a03_actual_weight_replacement_near_finite_contour_uniform_power_bound
    hf hg hΦ hc hc1 he hκ hθ hR hη hd hp hr
  obtain ⟨P,hP,hpos⟩ := a03_actual_weight_replacement_far_finite_contour_uniform_rapid
    hf hg hΦ hc hc1 hη hκ hθ hρ hρ1 0
  obtain ⟨D,hD,hdual⟩ := a03_actual_dual_weight_replacement_far_finite_contour_uniform_rapid
    hf hg hΦ hc hc1 hη hκ hθ hR hρ hρ1 0
  refine ⟨N+2*P+2*D,by positivity,?_⟩
  have hsmall := rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4)
  filter_upwards [hnear,hpos,hdual,hsmall,eventually_ge_atTop (1:ℝ)] with T hn hp hd hraw hT
  intro σ hσ hroot m₀ m₁
  have hTp : 0<T := zero_lt_one.trans_le hT
  let α₀ := bblrSixShifts (rawMomentShifts T σ) m₀
  let α₁ := bblrSixShifts (rawMomentShifts T σ) m₁
  have hα₀ : ∀ j, ‖α₀ j‖≤1/4 := bblrSixShifts_norm_le _ (hraw σ hσ) m₀
  have hα₁ : ∀ j, ‖α₁ j‖≤1/4 := bblrSixShifts_norm_le _ (hraw σ hσ) m₁
  obtain ⟨hn₀,hn₁,hnb⟩ := hn σ hσ hroot m₀ m₁
  obtain ⟨hp₀,hpb₀⟩ := hp σ α₀ hα₀ hroot true
  obtain ⟨hm₀,hmb₀⟩ := hp σ α₀ hα₀ hroot false
  obtain ⟨hp₁,hpb₁⟩ := hd σ α₁ hσ hα₁ hroot true
  obtain ⟨hm₁,hmb₁⟩ := hd σ α₁ hσ hα₁ hroot false
  simp only [neg_zero,Real.rpow_zero,mul_one] at hpb₀ hmb₀ hpb₁ hmb₁
  obtain ⟨hi₀,he₀⟩ := original_contour_near_add_far hTp c a b η ρ θ f g Φ σ α₀ hn₀ hp₀ hm₀
  obtain ⟨hi₁,he₁⟩ := dual_contour_near_add_far hTp c a b η ρ θ f g Φ σ α₁ hn₁ hp₁ hm₁
  refine ⟨hi₀,hi₁,?_⟩
  rw [he₀,he₁]
  have tri (x y z : ℂ) : ‖x+y+z‖≤‖x‖+‖y‖+‖z‖ :=
    (norm_add_le (x+y) z).trans (add_le_add (norm_add_le x y) (le_refl ‖z‖))
  have htq : 1≤T^q := Real.one_le_rpow hT hq
  have hfar : 2*P+2*D≤(2*P+2*D)*T^q :=
    le_mul_of_one_le_right (by positivity) htq
  calc
    _≤(‖a03ActualWeightReplacementNearFiniteContour c T a b η ρ θ f g Φ σ α₀‖+
        ‖a03ActualWeightReplacementFarFiniteContour true c T a b η ρ θ f g Φ σ α₀‖+
        ‖a03ActualWeightReplacementFarFiniteContour false c T a b η ρ θ f g Φ σ α₀‖)+
      (‖a03ActualDualWeightReplacementNearFiniteContour c T a b η ρ θ f g Φ σ α₁‖+
        ‖a03ActualDualWeightReplacementFarFiniteContour true c T a b η ρ θ f g Φ σ α₁‖+
        ‖a03ActualDualWeightReplacementFarFiniteContour false c T a b η ρ θ f g Φ σ α₁‖) :=
      add_le_add (tri _ _ _) (tri _ _ _)
    _≤N*T^q+(2*P+2*D) := by linarith [hnb,hpb₀,hmb₀,hpb₁,hmb₁]
    _≤N*T^q+(2*P+2*D)*T^q := add_le_add le_rfl hfar
    _=_ := by ring


theorem a03_actual_weight_replacement_rectangular_contour_uniform_power_bound
    {a b κ R : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (ha : 0<a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (hκ : 0<κ) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ m₀ m₁ : Fin 6,
      ‖a03ActualWeightReplacementFiniteContour (rectangularSlack a b/128) T a b
        (rectangularSlack a b/16) 1 f g Φ σ (bblrSixShifts (rawMomentShifts T σ) m₀)‖+
      ‖a03ActualDualWeightReplacementFiniteContour (rectangularSlack a b/128) T a b
        (rectangularSlack a b/16) 1 f g Φ σ (bblrSixShifts (rawMomentShifts T σ) m₁)‖≤
        C*T^(rectangularFirstExponent a b (rectangularSlack a b)) := by
  let s := rectangularSlack a b
  have hs : 0<s := (rectangular_slack_bounds hab hrect).1
  have hsmax : s≤1/16 := by dsimp [s,rectangularSlack]; linarith
  have hc : 0<s/128 := by positivity
  have hc1 : s/128≤1 := by linarith
  have he : 2*(s/128)<s/16 := by linarith
  have hη : 0<s/16 := by positivity
  have hρ1 : s/16≤1 := by linarith
  have hd : 0<s/8 := by positivity
  have hq : 0≤rectangularFirstExponent a b s := by dsimp [rectangularFirstExponent]; linarith
  have hp : a+b+s/16+(s/16)/2+s/16+s/8≤rectangularFirstExponent a b s := by
    dsimp [rectangularFirstExponent]
    linarith
  have hr : 1/2+a+b+(s/16)/4+s/16+s/8≤rectangularFirstExponent a b s := by
    dsimp [rectangularFirstExponent]
    linarith
  obtain ⟨C,hC,hb⟩ := a03_actual_weight_replacement_finite_contour_uniform_power_bound
    hf hg hΦ hc hc1 he hκ (by norm_num : (0:ℝ)≤1) hR hη hη hρ1 hd hq hp hr
  refine ⟨C,hC,hb.mono ?_⟩
  intro T hT σ hσ hroot m₀ m₁
  exact (hT σ hσ hroot m₀ m₁).2.2

end
end SixthMoment
