import SixthMoment.Numerator.U.ZeroModes.Ratio.AmplifierMass

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioResidualAmplifierMass (T a b : ℝ) (f g : ℝ→ℝ) (η : ℝ) : ℝ :=
  a03ZeroModeRatioProfilePowerMass T a b f g (1/2+η) (1/2+η)+
  a03ZeroModeRatioProfilePowerMass T a b f g (1/4+η) (3/4+η)+
  a03ZeroModeRatioProfilePowerMass T a b f g (3/4+η) (1/4+η)

theorem a03ZeroModeRatioResidualAmplifierMass_nonneg (T a b : ℝ)
    (f g : ℝ→ℝ) (η : ℝ) : 0≤a03ZeroModeRatioResidualAmplifierMass T a b f g η := by
  unfold a03ZeroModeRatioResidualAmplifierMass
  exact add_nonneg (add_nonneg (a03ZeroModeRatioProfilePowerMass_nonneg _ _ _ _ _ _ _)
    (a03ZeroModeRatioProfilePowerMass_nonneg _ _ _ _ _ _ _))
      (a03ZeroModeRatioProfilePowerMass_nonneg _ _ _ _ _ _ _)

theorem a03ZeroModeRatioResidualAmplifierMass_uniform_bound {a b η : ℝ}
    (hab : a≤b) (hη : 0<η) (hη1 : η≤1/4)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,1≤T →
      a03ZeroModeRatioResidualAmplifierMass T a b f g η≤
        C*T^(a*(1/4+η)+b*(3/4+η)) := by
  obtain ⟨D,hD,hd⟩ := a03ZeroModeRatioProfilePowerMass_uniform_bound
    (by linarith : 0<(1/2:ℝ)+η) (by linarith : (1/2:ℝ)+η≤1)
    (by linarith : 0<(1/2:ℝ)+η) (by linarith : (1/2:ℝ)+η≤1)
    (by linarith : 1≤(1/2:ℝ)+η+(1/2+η)) f g hf hg
  obtain ⟨E,hE,he⟩ := a03ZeroModeRatioProfilePowerMass_uniform_bound
    (by linarith : 0<(1/4:ℝ)+η) (by linarith : (1/4:ℝ)+η≤1)
    (by linarith : 0<(3/4:ℝ)+η) (by linarith : (3/4:ℝ)+η≤1)
    (by linarith : 1≤(1/4:ℝ)+η+(3/4+η)) f g hf hg
  obtain ⟨F,hF,hf⟩ := a03ZeroModeRatioProfilePowerMass_uniform_bound
    (by linarith : 0<(3/4:ℝ)+η) (by linarith : (3/4:ℝ)+η≤1)
    (by linarith : 0<(1/4:ℝ)+η) (by linarith : (1/4:ℝ)+η≤1)
    (by linarith : 1≤(3/4:ℝ)+η+(1/4+η)) f g hf hg
  refine ⟨D+E+F,by positivity,?_⟩
  intro T hT
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hdexp : a*(1/2+η)+b*(1/2+η)≤a*(1/4+η)+b*(3/4+η) := by nlinarith
  have hfexp : a*(3/4+η)+b*(1/4+η)≤a*(1/4+η)+b*(3/4+η) := by nlinarith
  have hd' := (hd T hTp).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT hdexp) hD)
  have hf' := (hf T hTp).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT hfexp) hF)
  unfold a03ZeroModeRatioResidualAmplifierMass
  exact (add_le_add (add_le_add hd' (he T hTp)) hf').trans_eq (by ring)

theorem a03ZeroModeRatioResidualAmplifier_exponent_lt_one {a b : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) :
    0<rectangularSlack a b ∧ rectangularSlack a b≤1/16 ∧
      1/2+rectangularSlack a b+a*(1/4+rectangularSlack a b)+
        b*(3/4+rectangularSlack a b)<1 := by
  have hb : 0≤b := ha.trans hab
  have habsum : a+b<1/2 := by linarith
  have hη : 0<rectangularSlack a b := (rectangular_slack_bounds hab hlen).1
  have hηcap : rectangularSlack a b≤1/16 := by dsimp [rectangularSlack]; linarith
  refine ⟨hη,hηcap,?_⟩
  have hbase : a/4+3*b/4<3/8 := by linarith
  have hcost : rectangularSlack a b*(1+a+b)<3/32 := by
    nlinarith
  nlinarith

theorem a03ZeroModeRatioResidualAmplifierMass_isLittleO {a b : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (n : ℕ) :
    (fun T : ℝ => (Real.log T)^n*T^(1/2+rectangularSlack a b)*
      a03ZeroModeRatioResidualAmplifierMass T a b f g (rectangularSlack a b))
        =o[atTop] (fun T : ℝ => T) := by
  obtain ⟨hη,hη1,hexp⟩ := a03ZeroModeRatioResidualAmplifier_exponent_lt_one ha hab hlen
  obtain ⟨C,hC,hbnd⟩ := a03ZeroModeRatioResidualAmplifierMass_uniform_bound hab hη
    (by linarith) f g hf hg
  have ho := (polylog_mul_rpow_isLittleO_id n hexp).const_mul_left C
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖(Real.log T)^n*T^(1/2+rectangularSlack a b)*
        a03ZeroModeRatioResidualAmplifierMass T a b f g (rectangularSlack a b)‖≤
      ‖C*((Real.log T)^n*T^(1/2+rectangularSlack a b+
        a*(1/4+rectangularSlack a b)+b*(3/4+rectangularSlack a b)))‖ := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    have hTp : 0<T := zero_lt_one.trans_le hT
    have hLn : 0≤(Real.log T)^n := pow_nonneg (Real.log_nonneg hT) _
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hLn (Real.rpow_nonneg hTp.le _))
      (a03ZeroModeRatioResidualAmplifierMass_nonneg _ _ _ _ _ _)),
      Real.norm_of_nonneg (by positivity : 0≤C*((Real.log T)^n*
        T^(1/2+rectangularSlack a b+a*(1/4+rectangularSlack a b)+b*(3/4+rectangularSlack a b))))]
    calc
      _≤(Real.log T)^n*T^(1/2+rectangularSlack a b)*
          (C*T^(a*(1/4+rectangularSlack a b)+b*(3/4+rectangularSlack a b))) := by
        gcongr
        exact hbnd T hT
      _=_ := by
        rw [show 1/2+rectangularSlack a b+a*(1/4+rectangularSlack a b)+b*(3/4+rectangularSlack a b)=
          (1/2+rectangularSlack a b)+(a*(1/4+rectangularSlack a b)+b*(3/4+rectangularSlack a b)) by ring,
          Real.rpow_add hTp (1/2+rectangularSlack a b)
            (a*(1/4+rectangularSlack a b)+b*(3/4+rectangularSlack a b))]
        ring
  exact hbound.isBigO.trans_isLittleO ho.norm_left

end
end SixthMoment.Source
