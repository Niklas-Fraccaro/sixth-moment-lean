import Sechstmoment.Numerator.U.Replacement.DualErrorPartsNearBound

/-! Separate full retained dual weight and dual phase errors, with actual
arithmetic coefficients, time integration and Mellin integration completed. -/
namespace Sechstmoment
open Complex Source Real MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology ENNReal
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_actual_dual_error_part_near_finite_contour_uniform_power_bound
    {a b c e κ θ R η ρ d q : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (he : 2*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hη : 0<η) (hd : 0<d)
    (hp : a+b+ρ+η/2+e+d≤q) (hr : 1/2+a+b+η/4+e+d≤q) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ phasePart : Bool, ∀ m : Fin 6,
      IntegrableOn (fun v : ℝ => a03ActualDualErrorPartNearFiniteMellinGrid phasePart c T a b η ρ v f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m)) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualDualErrorPartNearFiniteContour phasePart c T a b η ρ θ f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m)‖≤C*T^q := by
  obtain ⟨C,hC,hb⟩ := a03_actual_dual_error_part_near_finite_contour_uniform_mass_bound
    hf hg hΦ hc hc1 he hκ hθ hR (η := η) (ρ := ρ)
  obtain ⟨D,hD,hmass⟩ := actualSmoothNearGlobalMass_uniform_power_budget hη a b ρ
  let L : ℝ := ((7:ℕ).factorial:ℝ)/d^7*Real.exp d
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨2*C*D*L,by positivity,?_⟩
  filter_upwards [hb,hmass,eventually_ge_atTop (1:ℝ)] with T hb hm hT
  intro σ hσ hroot phasePart m
  obtain ⟨hi,hnear⟩ := hb σ hσ hroot phasePart m
  refine ⟨hi,?_⟩
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

private theorem part_contour_near_add_far (phasePart : Bool) {T : ℝ} (hT : 0<T)
    (c a b η ρ θ : ℝ) (f g Φ : ℝ→ℝ) (σ α : MomentShifts)
    (h_near : IntegrableOn (fun v : ℝ => a03ActualDualErrorPartNearFiniteMellinGrid phasePart c T a b η ρ v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T)))
    (h_plus : IntegrableOn (fun v : ℝ => a03ActualDualErrorPartFarFiniteMellinGrid phasePart true c T a b η ρ v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T)))
    (h_minus : IntegrableOn (fun v : ℝ => a03ActualDualErrorPartFarFiniteMellinGrid phasePart false c T a b η ρ v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T))) :
    IntegrableOn (fun v : ℝ => a03ActualDualErrorPartFiniteMellinGrid phasePart c T a b η v f g Φ σ α)
      (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
    a03ActualDualErrorPartFiniteContour phasePart c T a b η θ f g Φ σ α=
      a03ActualDualErrorPartNearFiniteContour phasePart c T a b η ρ θ f g Φ σ α+
      a03ActualDualErrorPartFarFiniteContour phasePart true c T a b η ρ θ f g Φ σ α+
      a03ActualDualErrorPartFarFiniteContour phasePart false c T a b η ρ θ f g Φ σ α := by
  have he : (fun v : ℝ => a03ActualDualErrorPartFiniteMellinGrid phasePart c T a b η v f g Φ σ α)=
      (fun v : ℝ => a03ActualDualErrorPartNearFiniteMellinGrid phasePart c T a b η ρ v f g Φ σ α+
        a03ActualDualErrorPartFarFiniteMellinGrid phasePart true c T a b η ρ v f g Φ σ α+
        a03ActualDualErrorPartFarFiniteMellinGrid phasePart false c T a b η ρ v f g Φ σ α) :=
    funext (fun v => a03ActualDualErrorPartFiniteMellinGrid_near_add_far phasePart hT c a b η ρ v f g Φ σ α)
  refine ⟨by rw [he]; exact (h_near.add h_plus).add h_minus,?_⟩
  unfold a03ActualDualErrorPartFiniteContour a03ActualDualErrorPartNearFiniteContour
    a03ActualDualErrorPartFarFiniteContour
  have hI := integral_add (h_near.add h_plus) h_minus
  simp only [Pi.add_apply] at hI
  rw [he,hI,integral_add h_near h_plus]
  ring


/-- Uniform separate full dual weight/phase error. The Boolean selects an
individual error before every sum and integral is performed. -/
theorem a03_actual_dual_error_part_finite_contour_uniform_power_bound
    {a b c e κ θ R η ρ d q : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (he : 2*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hη : 0<η) (hρ : 0<ρ) (hρ1 : ρ≤1) (hd : 0<d)
    (hq : 0≤q) (hp : a+b+ρ+η/2+e+d≤q) (hr : 1/2+a+b+η/4+e+d≤q) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ phasePart : Bool, ∀ m : Fin 6,
      IntegrableOn (fun v : ℝ => a03ActualDualErrorPartFiniteMellinGrid phasePart c T a b η v f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m)) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualDualErrorPartFiniteContour phasePart c T a b η θ f g Φ σ
        (bblrSixShifts (rawMomentShifts T σ) m)‖≤C*T^q := by
  obtain ⟨N,hN,hnear⟩ := a03_actual_dual_error_part_near_finite_contour_uniform_power_bound
    hf hg hΦ hc hc1 he hκ hθ hR hη hd hp hr
  obtain ⟨P,hP,hfar⟩ := a03_actual_dual_error_part_far_finite_contour_uniform_rapid
    hf hg hΦ hc hc1 hη hκ hθ hR hρ hρ1 0
  refine ⟨N+2*P,by positivity,?_⟩
  have hsmall := rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4)
  filter_upwards [hnear,hfar,hsmall,eventually_ge_atTop (1:ℝ)] with T hn hp hraw hT
  intro σ hσ hroot phasePart m
  have hTp : 0<T := zero_lt_one.trans_le hT
  let α := bblrSixShifts (rawMomentShifts T σ) m
  have hα : ∀ j, ‖α j‖≤1/4 := bblrSixShifts_norm_le _ (hraw σ hσ) m
  obtain ⟨hn,hnb⟩ := hn σ hσ hroot phasePart m
  obtain ⟨hplus,hpb⟩ := hp σ α hσ hα hroot phasePart true
  obtain ⟨hminus,hmb⟩ := hp σ α hσ hα hroot phasePart false
  simp only [neg_zero,Real.rpow_zero,mul_one] at hpb hmb
  obtain ⟨hi,heq⟩ := part_contour_near_add_far phasePart hTp c a b η ρ θ f g Φ σ α hn hplus hminus
  refine ⟨hi,?_⟩
  rw [heq]
  have tri (x y z : ℂ) : ‖x+y+z‖≤‖x‖+‖y‖+‖z‖ :=
    (norm_add_le (x+y) z).trans (add_le_add (norm_add_le x y) (le_refl ‖z‖))
  have htq : 1≤T^q := Real.one_le_rpow hT hq
  have hfar : 2*P≤(2*P)*T^q := le_mul_of_one_le_right (by positivity) htq
  calc
    _≤‖a03ActualDualErrorPartNearFiniteContour phasePart c T a b η ρ θ f g Φ σ α‖+
        ‖a03ActualDualErrorPartFarFiniteContour phasePart true c T a b η ρ θ f g Φ σ α‖+
        ‖a03ActualDualErrorPartFarFiniteContour phasePart false c T a b η ρ θ f g Φ σ α‖ := tri _ _ _
    _≤N*T^q+2*P := by linarith [hnb,hpb,hmb]
    _≤N*T^q+(2*P)*T^q := add_le_add le_rfl hfar
    _=_ := by ring

/-- Concrete auxiliary choices bound each full retained dual error separately
on the genuine rectangular exponent, with one common uniform constant. -/
theorem a03_actual_dual_error_part_rectangular_contour_uniform_power_bound
    {a b κ R : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (ha : 0<a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (hκ : 0<κ) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ phasePart : Bool, ∀ m : Fin 6,
      ‖a03ActualDualErrorPartFiniteContour phasePart (rectangularSlack a b/128) T a b
        (rectangularSlack a b/16) 1 f g Φ σ (bblrSixShifts (rawMomentShifts T σ) m)‖≤
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
  obtain ⟨C,hC,hb⟩ := a03_actual_dual_error_part_finite_contour_uniform_power_bound
    hf hg hΦ hc hc1 he hκ (by norm_num : (0:ℝ)≤1) hR hη hη hρ1 hd hq hp hr
  refine ⟨C,hC,hb.mono ?_⟩
  intro T hT σ hσ hroot phasePart m
  exact (hT σ hσ hroot phasePart m).2

end
end Sechstmoment
