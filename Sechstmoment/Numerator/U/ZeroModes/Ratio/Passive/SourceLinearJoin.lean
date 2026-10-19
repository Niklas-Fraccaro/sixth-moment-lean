import Sechstmoment.Numerator.U.ZeroModes.ActualFourRatioGammaLinearJoin
import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.SourceUniformMoment
import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.ZeroReplacementMoment

/-! One common genuine original/dual source factory controls every literal
selected passive physical source against its leading linear zero. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_passive_ratio_source_physical_sub_linear_uniform_slack_smaller
    (hinput : SeparatedQuadraticInput) {a b κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ∀ dual : Bool,∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
        IntegrableOn (fun v => a03ActualPassiveRatioSourceFiniteValue select false dual Φ (rectangularSlack a b/512)
          T a b s u (rectangularSlack a b/128) v σ α f g) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
        IntegrableOn (fun v => a03ActualPassiveRatioSourceLinearZeroFinite select dual Φ (rectangularSlack a b/512)
          T a b s u (rectangularSlack a b/128) v σ α f g) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
        ‖a03ActualPassiveRatioSourceValueMoment select false dual Φ (rectangularSlack a b/512)
            T a b s u (rectangularSlack a b/128) θ σ α f g-
          a03ActualPassiveRatioSourceLinearZeroMoment select dual Φ (rectangularSlack a b/512)
            T a b s u (rectangularSlack a b/128) θ σ α f g‖≤δ*T := by
  have hslack : 0<rectangularSlack a b := by unfold rectangularSlack; linarith
  have hc : 0<rectangularSlack a b/512 := by positivity
  have hc1 : rectangularSlack a b/512≤1 := by unfold rectangularSlack; linarith [ha.trans hab]
  have he : 12*(rectangularSlack a b/512)<rectangularSlack a b/16 := by linarith
  have hε : 0<rectangularSlack a b/128 := by positivity
  have hloss : 4*(rectangularSlack a b/128)+rectangularSlack a b/16<rectangularSlack a b := by linarith
  obtain ⟨S0,U0,hS0,hS02,hS0cap,hU0,hU0cap,hfalse⟩ :=
    a03_actual_passive_ratio_source_native_moment_sub_Gamma_zero_uniform_smaller false hinput
      ha hab hlen hε f g hf hg hΦ hΦs hc hc1 he hκ hθ hR hloss
  obtain ⟨S1,U1,hS1,_hS12,_hS1cap,hU1,_hU1cap,htrue⟩ :=
    a03_actual_passive_ratio_source_native_moment_sub_Gamma_zero_uniform_smaller true hinput
      ha hab hlen hε f g hf hg hΦ hΦs hc hc1 he hκ hθ hR hloss
  let S := min S0 S1
  let U := min U0 U1
  have hS : 0<S := lt_min hS0 hS1
  have hU : 0<U := lt_min hU0 hU1
  have hS2 : S<1/2 := (min_le_left _ _).trans_lt hS02
  have hScap : S≤1/8 := (min_le_left _ _).trans hS0cap
  have hUcap : U≤1/8 := (min_le_left _ _).trans hU0cap
  refine ⟨S,U,hS,hS2,hScap,hU,hUcap,?_⟩
  intro s u hs hss hu huu δ hδ
  have hs0 : s≤S0 := hss.trans (min_le_left _ _)
  have hs1 : s≤S1 := hss.trans (min_le_right _ _)
  have hu0 : u≤U0 := huu.trans (min_le_left _ _)
  have hu1 : u≤U1 := huu.trans (min_le_right _ _)
  have hscap : s≤1/8 := hss.trans hScap
  have hucap : u≤1/8 := huu.trans hUcap
  obtain ⟨_hc,_hc1,hreplaceε,hexp⟩ := a03_actual_four_ratio_replacement_slack_budget ha hab hlen hscap hucap
  filter_upwards [hfalse s u hs hs0 hu hu0 (δ/2) (by positivity),
    htrue s u hs hs1 hu hu1 (δ/2) (by positivity),
    a03_actual_passive_ratio_source_Gamma_zero_sub_linear_uniform_oT ha (ha.trans hab) hs.le
      (by linarith : s<1) f g hf hg hΦ hΦs hc hc1 hreplaceε hκ hθ hR hu hexp
      (rectangularSlack a b/128) (δ/2) (by positivity),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R))]
    with T hfalse htrue hreplace hlog hlogR
  intro σ α hσ hα hroot dual select
  have hαquarter : ∀ j,‖α j‖≤1/4 := fun j =>
    (hα j).trans ((div_le_iff₀ (zero_lt_one.trans_le hlog)).mpr (by linarith))
  have hsource : IntegrableOn (fun v => a03ActualPassiveRatioSourceFiniteValue select false dual Φ
      (rectangularSlack a b/512) T a b s u (rectangularSlack a b/128) v σ α f g)
      (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      IntegrableOn (fun v => a03ActualPassiveRatioSourceFiniteValue select true dual Φ
        (rectangularSlack a b/512) T a b s u (rectangularSlack a b/128) v σ α f g)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualPassiveRatioSourceValueMoment select false dual Φ (rectangularSlack a b/512)
          T a b s u (rectangularSlack a b/128) θ σ α f g-
        a03ActualPassiveRatioSourceValueMoment select true dual Φ (rectangularSlack a b/512)
          T a b s u (rectangularSlack a b/128) θ σ α f g‖≤(δ/2)*T := by
    cases dual
    · exact hfalse σ α hσ hα hroot select
    · exact htrue σ α hσ hα hroot select
  have hlinear := hreplace σ α hσ hαquarter hα hroot dual select
  refine ⟨hsource.1,hlinear.1,?_⟩
  calc
    _ = ‖(a03ActualPassiveRatioSourceValueMoment select false dual Φ (rectangularSlack a b/512)
        T a b s u (rectangularSlack a b/128) θ σ α f g-
      a03ActualPassiveRatioSourceValueMoment select true dual Φ (rectangularSlack a b/512)
        T a b s u (rectangularSlack a b/128) θ σ α f g)+
      (a03ActualPassiveRatioSourceValueMoment select true dual Φ (rectangularSlack a b/512)
        T a b s u (rectangularSlack a b/128) θ σ α f g-
      a03ActualPassiveRatioSourceLinearZeroMoment select dual Φ (rectangularSlack a b/512)
        T a b s u (rectangularSlack a b/128) θ σ α f g)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ δ*T := by linarith [hsource.2.2,hlinear.2]

end
end Sechstmoment
