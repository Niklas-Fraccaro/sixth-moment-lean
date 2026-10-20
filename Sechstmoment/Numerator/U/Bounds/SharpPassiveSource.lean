import Sechstmoment.Numerator.U.Bounds.SharpPassiveSourceBudget

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03SharpPassiveLoss (a b ε : ℝ) : ℝ := min ε (min (rectangularSlack a b) (1/16))

theorem a03SharpPassiveLoss_pos {a b ε : ℝ} (hab : a≤b) (hlen : 3*a+5*b<2) (hε : 0<ε) :
    0<a03SharpPassiveLoss a b ε := by
  exact lt_min hε (lt_min (rectangular_slack_bounds hab hlen).1 (by norm_num))

theorem a03_sharp_passive_physical_sub_linear_rectangular_budget_smaller
    (hinput : SeparatedQuadraticInput) {a b κ θ R η ε c : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (hη : 0<η) (hηε : η≤ε) (hηslack : η≤rectangularSlack a b) (hηcap : η≤1/16)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hc : 0<c) (hccap : c≤η/128) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ S≤η/128 ∧ 0<U ∧ U≤1/8 ∧ U≤η/128 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
      ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀j,‖σ j‖≤R) →
        (∀j,‖α j‖≤R/Real.log T) →(∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀dual : Bool,∀select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
        ‖a03ActualPassiveRatioSourceValueMoment select false dual Φ c T a b s u (η/1024) θ σ α f g-
          a03ActualPassiveRatioSourceLinearZeroMoment select dual Φ c T a b s u (η/1024) θ σ α f g‖≤
            C*(T^(rectangularFirstExponent a b ε)+T^(rectangularSecondExponent a b ε)) := by
  have hc1 : c≤1 := by linarith only [hccap,hηcap]
  have he : 12*c<η/8 := by linarith only [hccap,hη]
  have hker : 2*c<η/16 := by linarith only [hccap,hη]
  have hloss : 4*(η/1024)+η/8<rectangularSlack a b := by linarith only [hηslack,hη]
  obtain ⟨S0,U0,hS0,hS02,hS0cap,hU0,hU0cap,hF0⟩ :=
    a03_sharp_passive_physical_sub_Gamma_mass_budget_smaller false hinput ha hab hlen
      (by positivity : 0<η/1024) f g hf hg hΦ hΦs hc hc1 he hκ hθ hR hloss
  obtain ⟨S1,U1,hS1,hS12,hS1cap,hU1,hU1cap,hF1⟩ :=
    a03_sharp_passive_physical_sub_Gamma_mass_budget_smaller true hinput ha hab hlen
      (by positivity : 0<η/1024) f g hf hg hΦ hΦs hc hc1 he hκ hθ hR hloss
  let S := min (min S0 S1) (η/128)
  let U := min (min U0 U1) (η/128)
  have hSS0 : S≤S0 := (min_le_left _ _).trans (min_le_left _ _)
  have hSS1 : S≤S1 := (min_le_left _ _).trans (min_le_right _ _)
  have hUU0 : U≤U0 := (min_le_left _ _).trans (min_le_left _ _)
  have hUU1 : U≤U1 := (min_le_left _ _).trans (min_le_right _ _)
  have hSη : S≤η/128 := min_le_right _ _
  have hUη : U≤η/128 := min_le_right _ _
  refine ⟨S,U,lt_min (lt_min hS0 hS1) (by positivity),hSS0.trans_lt hS02,hSS0.trans hS0cap,hSη,
    lt_min (lt_min hU0 hU1) (by positivity),hUU0.trans hU0cap,hUη,?_⟩
  intro s u hs hsS hu huU
  have hs1 : s<1 := (hsS.trans hSS0).trans_lt hS02 |>.trans (by norm_num)
  have hscap : s≤1/8 := (hsS.trans hSS0).trans hS0cap
  have hucap : u≤1/8 := (huU.trans hUU0).trans hU0cap
  have hsη : s≤η/128 := hsS.trans hSη
  have huη : u≤η/128 := huU.trans hUη
  obtain ⟨C0,hC0,hB0⟩ := hF0 s u hs (hsS.trans hSS0) hu (huU.trans hUU0)
  obtain ⟨C1,hC1,hB1⟩ := hF1 s u hs (hsS.trans hSS1) hu (huU.trans hUU1)
  obtain ⟨CΓ,hCΓ,hΓ⟩ := a03_sharp_passive_Gamma_sub_linear_mass_budget
    (u:=u) hs.le hs1 f g hf hg hΦ hΦs hc hc1 hker hκ hθ hR (η/1024)
  obtain ⟨Ds,hDs,hSbound⟩ := a03_sharp_passive_source_global_mass_uniform_power
    ha hab hlen hs.le hscap hu hucap hθ hη hηε hsη huη f g hf hg
  obtain ⟨DΓ,hDΓ,hGbound⟩ := a03_sharp_passive_Gamma_global_mass_uniform_power
    ha (ha.trans hab) hs.le hu hθ hη hηε hsη huη f g hf hg
  obtain ⟨M,hM,hMass⟩ := a03_actual_passive_soft_source_global_majorant_bound
    ha hab hlen hs.le hscap hu hucap (by positivity : 0≤η/1024) hθ f g hf hg
  let C := (C0+C1)*Ds+CΓ*DΓ
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hB0,hB1,hΓ,hSbound,hGbound,hMass,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R))]
    with T hB0 hB1 hΓ hSB hGB hMT hT hlog hlogR
  intro σ α hσ hα hroot dual select
  have hαq : ∀j,‖α j‖≤1/4 := fun j =>
    (hα j).trans ((div_le_iff₀ (zero_lt_one.trans_le hlog)).mpr (by linarith))
  let E := T^(rectangularFirstExponent a b ε)+T^(rectangularSecondExponent a b ε)
  have hE : 0≤E := by dsimp [E]; positivity
  have hSource : ‖a03ActualPassiveRatioSourceValueMoment select false dual Φ c T a b s u (η/1024) θ σ α f g-
      a03ActualPassiveRatioSourceValueMoment select true dual Φ c T a b s u (η/1024) θ σ α f g‖≤
      ((C0+C1)*Ds)*E := by
    have hb : ‖a03ActualPassiveRatioSourceValueMoment select false dual Φ c T a b s u (η/1024) θ σ α f g-
        a03ActualPassiveRatioSourceValueMoment select true dual Φ c T a b s u (η/1024) θ σ α f g‖≤
        (C0+C1)*(T^(η/8)*a03ActualPassiveSoftSourceGlobalMajorant T a b s u (η/1024) θ f g) := by
      cases dual
      · exact ((hB0 σ α hσ hα hroot select).2.2).trans (by nlinarith only [mul_nonneg hC1 (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hT) _) hMT.1)])
      · exact ((hB1 σ α hσ hα hroot select).2.2).trans (by nlinarith only [mul_nonneg hC0 (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hT) _) hMT.1)])
    exact hb.trans ((mul_le_mul_of_nonneg_left hSB (add_nonneg hC0 hC1)).trans_eq (by dsimp [E]; ring))
  have hGamma : ‖a03ActualPassiveRatioSourceValueMoment select true dual Φ c T a b s u (η/1024) θ σ α f g-
      a03ActualPassiveRatioSourceLinearZeroMoment select dual Φ c T a b s u (η/1024) θ σ α f g‖≤(CΓ*DΓ)*E := by
    have hg0 := (hΓ σ α hσ hαq hα hroot dual select).2
    have hg1 := mul_le_mul_of_nonneg_left hGB hCΓ
    exact hg0.trans (hg1.trans (by dsimp [E]; nlinarith only [mul_nonneg (mul_nonneg hCΓ hDΓ) (Real.rpow_nonneg (zero_le_one.trans hT) (rectangularSecondExponent a b ε))]))
  calc
    _≤‖a03ActualPassiveRatioSourceValueMoment select false dual Φ c T a b s u (η/1024) θ σ α f g-
        a03ActualPassiveRatioSourceValueMoment select true dual Φ c T a b s u (η/1024) θ σ α f g‖+
      ‖a03ActualPassiveRatioSourceValueMoment select true dual Φ c T a b s u (η/1024) θ σ α f g-
        a03ActualPassiveRatioSourceLinearZeroMoment select dual Φ c T a b s u (η/1024) θ σ α f g‖ := norm_sub_le _ _ _
    _≤((C0+C1)*Ds)*E+(CΓ*DΓ)*E := add_le_add hSource hGamma
    _=C*E := by dsimp [C]; ring

end
end Sechstmoment
