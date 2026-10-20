import SixthMoment.Numerator.U.Diagonal.ActualSmoothNearMass


namespace SixthMoment
open Real Source Filter Asymptotics
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def actualSmoothNearGlobalMass (T a b η ρ : ℝ) : ℝ :=
  ∑ u∈Finset.range ⌊T^a⌋₊, ∑ v∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)),
      actualSmoothNearWeightedMass T ρ u v k

theorem actualSmoothNearWeightedMass_nonneg (T ρ : ℝ) (u v : ℕ) (k : Fin 4→ℕ) :
    0≤actualSmoothNearWeightedMass T ρ u v k := by
  unfold actualSmoothNearWeightedMass
  apply Finset.sum_nonneg
  intro n _
  split_ifs
  · exact mul_nonneg (rectangular_AFE_smooth_weight_nonneg k n)
      (positiveNearFactorWeight_nonneg _ _ _)
  · exact le_rfl

theorem actualSmoothNearGlobalMass_nonneg (T a b η ρ : ℝ) :
    0≤actualSmoothNearGlobalMass T a b η ρ := by
  unfold actualSmoothNearGlobalMass
  exact Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ =>
    Finset.sum_nonneg (fun k _ => actualSmoothNearWeightedMass_nonneg T ρ u v k)))

theorem actualSmoothNearGlobalMass_le_card {T η ρ : ℝ}
    (hT : 1≤T) (hη : 0≤η) (a b : ℝ) :
    actualSmoothNearGlobalMass T a b η ρ≤
      (⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*
        ((rectangularAFEProductScaleGrid (T^(2+η))).card:ℝ)*
          (320*(bblrNearMassLogRadius T η)^2*
            (T^(ρ+η/2)+T^(1/2+η/4))) := by
  unfold actualSmoothNearGlobalMass
  calc
    _ ≤ ∑ u∈Finset.range ⌊T^a⌋₊, ∑ v∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+η)),
          320*(bblrNearMassLogRadius T η)^2*(T^(ρ+η/2)+T^(1/2+η/4)) := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro k hk
      exact (actualSmoothNearWeightedMass_le_mass T ρ u v k).trans
        (actualSmoothNearMass_le_power hT hη u v k hk)
    _ = _ := by simp; ring

theorem actualSmoothNearGlobalMass_uniform_power_budget {η : ℝ} (hη : 0<η)
    (a b ρ : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      actualSmoothNearGlobalMass T a b η ρ≤C*(1+Real.log T)^6*
        (T^(a+b+ρ+η/2)+T^(1/2+a+b+η/4)) := by
  obtain ⟨D,hD,hcard⟩ := rectangular_AFE_product_scale_grid_uniform_log_card hη
  refine ⟨320*D*(10+η)^2,by positivity,?_⟩
  filter_upwards [hcard,eventually_ge_atTop (1:ℝ)] with T hc hT
  have ht : 0<T := zero_lt_one.trans_le hT
  have hL : 0≤1+Real.log T := by linarith [Real.log_nonneg hT]
  have hR : 0≤bblrNearMassLogRadius T η := zero_le_one.trans
    (bblrNearMassLogRadius_one_le hT hη.le)
  have hR2 : (bblrNearMassLogRadius T η)^2≤(10+η)^2*(1+Real.log T)^2 := by
    have hb := bblrNearMassLogRadius_le_log hT hη.le
    have hs := pow_le_pow_left₀ hR hb 2
    simpa only [mul_pow] using hs
  have hna : (⌊T^a⌋₊:ℝ)≤T^a := Nat.floor_le (Real.rpow_nonneg ht.le _)
  have hnb : (⌊T^b⌋₊:ℝ)≤T^b := Nat.floor_le (Real.rpow_nonneg ht.le _)
  have hpow : 0≤T^(ρ+η/2)+T^(1/2+η/4) := by positivity
  calc
    _ ≤ (⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*
        ((rectangularAFEProductScaleGrid (T^(2+η))).card:ℝ)*
          (320*(bblrNearMassLogRadius T η)^2*
            (T^(ρ+η/2)+T^(1/2+η/4))) := actualSmoothNearGlobalMass_le_card hT hη.le a b
    _ ≤ (T^a*T^b)*(D*(1+Real.log T)^4)*
        (320*((10+η)^2*(1+Real.log T)^2)*(T^(ρ+η/2)+T^(1/2+η/4))) := by
      gcongr
    _ = (320*D*(10+η)^2)*(1+Real.log T)^6*
        (T^(a+b+ρ+η/2)+T^(1/2+a+b+η/4)) := by
      rw [show a+b+ρ+η/2=(a+b)+(ρ+η/2) by ring,
        show 1/2+a+b+η/4=(a+b)+(1/2+η/4) by ring,
        Real.rpow_add ht (a+b) (ρ+η/2),Real.rpow_add ht (a+b) (1/2+η/4),
        Real.rpow_add ht a b]
      ring

theorem one_add_log_pow_weighted_power_sum_isLittleO (n : ℕ) {e₁ e₂ : ℝ}
    (he₁ : e₁<1) (he₂ : e₂<1) :
    (fun T : ℝ => (1+Real.log T)^n*(T^e₁+T^e₂)) =o[atTop] (fun T : ℝ => T) := by
  have hbase : (fun T : ℝ => (Real.log T)^n*(T^e₁+T^e₂)) =o[atTop]
      (fun T : ℝ => T) := by
    simpa only [mul_add] using
      (polylog_mul_rpow_isLittleO_id n he₁).add (polylog_mul_rpow_isLittleO_id n he₂)
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖(1+Real.log T)^n*(T^e₁+T^e₂)‖≤
        (2:ℝ)^n*((Real.log T)^n*(T^e₁+T^e₂)) := by
    filter_upwards [eventually_gt_atTop (0:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hT hL
    have hlog : 0≤Real.log T := by linarith
    have hpow : 0≤T^e₁+T^e₂ := by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    have hb : (1+Real.log T)^n≤(2:ℝ)^n*(Real.log T)^n := by
      calc
        _ ≤ (2*Real.log T)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
        _ = _ := by rw [mul_pow]
    calc
      _ ≤ ((2:ℝ)^n*(Real.log T)^n)*(T^e₁+T^e₂) :=
        mul_le_mul_of_nonneg_right hb hpow
      _ = _ := by ring
  exact hbound.isBigO.trans_isLittleO (hbase.const_mul_left ((2:ℝ)^n))

theorem one_add_log_weighted_power_sum_isLittleO {e₁ e₂ : ℝ}
    (he₁ : e₁<1) (he₂ : e₂<1) :
    (fun T : ℝ => (1+Real.log T)^6*(T^e₁+T^e₂)) =o[atTop] (fun T : ℝ => T) := by
  have hbase : (fun T : ℝ => (Real.log T)^6*(T^e₁+T^e₂)) =o[atTop]
      (fun T : ℝ => T) := by
    simpa only [mul_add] using
      (polylog_mul_rpow_isLittleO_id 6 he₁).add (polylog_mul_rpow_isLittleO_id 6 he₂)
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖(1+Real.log T)^6*(T^e₁+T^e₂)‖≤
        64*((Real.log T)^6*(T^e₁+T^e₂)) := by
    filter_upwards [eventually_gt_atTop (0:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hT hL
    have hlog : 0≤Real.log T := by linarith
    have hpow : 0≤T^e₁+T^e₂ := by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    have hb : (1+Real.log T)^6≤64*(Real.log T)^6 := by
      calc
        _ ≤ (2*Real.log T)^6 := by gcongr; linarith
        _ = _ := by ring
    nlinarith
  exact hbound.isBigO.trans_isLittleO (hbase.const_mul_left 64)

theorem actualSmoothNearGlobalMass_isLittleO {η a b ρ : ℝ} (hη : 0<η)
    (he₁ : a+b+ρ+η/2<1) (he₂ : 1/2+a+b+η/4<1) :
    (fun T : ℝ => actualSmoothNearGlobalMass T a b η ρ) =o[atTop] (fun T : ℝ => T) := by
  obtain ⟨C,_hC,hbound⟩ := actualSmoothNearGlobalMass_uniform_power_budget hη a b ρ
  have hb : ∀ᶠ T : ℝ in atTop,
      ‖actualSmoothNearGlobalMass T a b η ρ‖≤C*((1+Real.log T)^6*
        (T^(a+b+ρ+η/2)+T^(1/2+a+b+η/4))) := by
    filter_upwards [hbound] with T hT
    rw [Real.norm_of_nonneg (actualSmoothNearGlobalMass_nonneg T a b η ρ)]
    simpa only [mul_assoc] using hT
  exact hb.isBigO.trans_isLittleO
    ((one_add_log_weighted_power_sum_isLittleO he₁ he₂).const_mul_left C)

theorem actualSmoothNearGlobalMass_scaled_isLittleO {η a b ρ ε : ℝ} (hη : 0<η)
    (m : ℕ) (he₁ : a+b+ρ+η/2+ε<1) (he₂ : 1/2+a+b+η/4+ε<1) :
    (fun T : ℝ => (1+Real.log T)^m*T^ε*actualSmoothNearGlobalMass T a b η ρ)
      =o[atTop] (fun T : ℝ => T) := by
  obtain ⟨C,_hC,hbound⟩ := actualSmoothNearGlobalMass_uniform_power_budget hη a b ρ
  have hb : ∀ᶠ T : ℝ in atTop,
      ‖(1+Real.log T)^m*T^ε*actualSmoothNearGlobalMass T a b η ρ‖≤
        C*((1+Real.log T)^(m+6)*
          (T^(a+b+ρ+η/2+ε)+T^(1/2+a+b+η/4+ε))) := by
    filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with T hmass hT
    have ht : 0<T := zero_lt_one.trans_le hT
    have hL : 0≤1+Real.log T := by linarith [Real.log_nonneg hT]
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
      (actualSmoothNearGlobalMass_nonneg T a b η ρ))]
    calc
      _ ≤ (1+Real.log T)^m*T^ε*
          (C*(1+Real.log T)^6*(T^(a+b+ρ+η/2)+T^(1/2+a+b+η/4))) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by
        rw [pow_add,Real.rpow_add ht (a+b+ρ+η/2) ε,
          Real.rpow_add ht (1/2+a+b+η/4) ε]
        ring
  exact hb.isBigO.trans_isLittleO
    ((one_add_log_pow_weighted_power_sum_isLittleO (m+6) he₁ he₂).const_mul_left C)

theorem actualSmoothNear_rectangle_parameters_exist {a b : ℝ}
    (hab : a≤b) (hrect : 3*a+5*b<2) :
    ∃ η ρ ε : ℝ, 0<η ∧ 0<ρ ∧ 0<ε ∧
      a+b+ρ+η/2+ε<1 ∧ 1/2+a+b+η/4+ε<1 := by
  let d : ℝ := (1/2-a-b)/8
  have hd : 0<d := by dsimp [d]; linarith
  refine ⟨d,d,d,hd,hd,hd,?_,?_⟩ <;> dsimp [d] <;> linarith

end
end SixthMoment
