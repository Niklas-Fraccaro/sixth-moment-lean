import Sechstmoment.Numerator.U.ZeroModes.Ratio.FourGammaZeroJoin

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_hard_Gamma_zero_sub_four_ratio_Gamma_zeros_uniform_smaller_branch (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource e c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hloss : 4*εsource+e<rectangularSlack a b) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ‖a03ActualSourceGammaZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s u θ σ f g-
          a03ActualFourRatioGammaZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s u εsource θ σ f g‖≤δ*T := by
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 := (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  obtain ⟨Sh,Uh,hSh,hSh2,hShcap,hUh,hUhcap,hh⟩ :=
    a03_actual_source_physical_moment_sub_Gamma_zero_uniform_smaller dual hinput ha hab hlen hεsource
      f g hf hg hΦc hΦs hc hc1 (by linarith : 4*c<e) hκ hθ hR hloss
  obtain ⟨Sr,Ur,hSr,_hSr2,_hSrcap,hUr,_hUrcap,hr⟩ :=
    a03_actual_source_physical_moment_sub_four_ratio_Gamma_zeros_uniform_smaller dual hinput
      ha hab hlen hεsource f g Φ hf hg hΦ hc hc1 he hκ hθ hR hloss
  let S := min Sh Sr
  let U := min Uh Ur
  refine ⟨S,U,lt_min hSh hSr,(min_le_left _ _).trans_lt hSh2,(min_le_left _ _).trans hShcap,
    lt_min hUh hUr,(min_le_left _ _).trans hUhcap,?_⟩
  intro s u hs hsS hu huU δ hδ
  have hsh : s≤Sh := hsS.trans (min_le_left _ _)
  have hsr : s≤Sr := hsS.trans (min_le_right _ _)
  have huh : u≤Uh := huU.trans (min_le_left _ _)
  have hur : u≤Ur := huU.trans (min_le_right _ _)
  filter_upwards [hh s u hs hsh hu huh (δ/2) (by positivity),
    hr s u hs hsr hu hur (δ/2) (by positivity)] with T hh hr
  intro σ hσ hroot
  have hh := (hh σ hσ hroot).2.2
  have hr := hr σ hσ hroot
  have halg (H P R : ℂ) : H-R=(H-P)+(P-R) := by ring
  rw [halg _ (a03ActualSourcePhysicalMoment dual (fun x => (Φ x:ℂ)) c T a b s u θ σ f g)]
  apply (norm_add_le _ _).trans
  rw [norm_sub_rev]
  exact (add_le_add hh hr).trans_eq (by ring)

theorem a03_actual_hard_Gamma_zero_sub_four_ratio_Gamma_zeros_uniform_smaller
    (hinput : SeparatedQuadraticInput) {a b εsource e c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hloss : 4*εsource+e<rectangularSlack a b) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
        ‖a03ActualSourceGammaZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s u θ σ f g-
          a03ActualFourRatioGammaZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s u εsource θ σ f g‖≤δ*T := by
  obtain ⟨S0,U0,hS0,hS02,hS0cap,hU0,hU0cap,h0⟩ :=
    a03_actual_hard_Gamma_zero_sub_four_ratio_Gamma_zeros_uniform_smaller_branch false
      hinput ha hab hlen hεsource f g Φ hf hg hΦ hc hc1 he hκ hθ hR hloss
  obtain ⟨S1,U1,hS1,_hS12,_hS1cap,hU1,_hU1cap,h1⟩ :=
    a03_actual_hard_Gamma_zero_sub_four_ratio_Gamma_zeros_uniform_smaller_branch true
      hinput ha hab hlen hεsource f g Φ hf hg hΦ hc hc1 he hκ hθ hR hloss
  let S := min S0 S1
  let U := min U0 U1
  refine ⟨S,U,lt_min hS0 hS1,(min_le_left _ _).trans_lt hS02,(min_le_left _ _).trans hS0cap,
    lt_min hU0 hU1,(min_le_left _ _).trans hU0cap,?_⟩
  intro s u hs hsS hu huU δ hδ
  filter_upwards [h0 s u hs (hsS.trans (min_le_left _ _)) hu (huU.trans (min_le_left _ _)) δ hδ,
    h1 s u hs (hsS.trans (min_le_right _ _)) hu (huU.trans (min_le_right _ _)) δ hδ] with T h0 h1
  intro σ hσ hroot dual
  cases dual
  · exact h0 σ hσ hroot
  · exact h1 σ hσ hroot

theorem a03_actual_hard_Gamma_zero_sub_four_ratio_Gamma_zeros_uniform_slack
    (hinput : SeparatedQuadraticInput) {a b κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ S U : ℝ,0<S ∧ S<1/2 ∧ S≤1/8 ∧ 0<U ∧ U≤1/8 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U →
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
        ‖a03ActualSourceGammaZeroMoment dual (fun x => (Φ x:ℂ)) (rectangularSlack a b/512) T a b s u θ σ f g-
          a03ActualFourRatioGammaZeroMoment dual (fun x => (Φ x:ℂ)) (rectangularSlack a b/512)
            T a b s u (rectangularSlack a b/128) θ σ f g‖≤δ*T := by
  have hslack : 0<rectangularSlack a b := by unfold rectangularSlack; linarith
  have hb : 0≤b := ha.trans hab
  apply a03_actual_hard_Gamma_zero_sub_four_ratio_Gamma_zeros_uniform_smaller
    (e:=rectangularSlack a b/16) hinput ha hab hlen
    (by positivity) f g Φ hf hg hΦ (by positivity) ?_ ?_ hκ hθ hR ?_
  · unfold rectangularSlack
    linarith
  · linarith
  · linarith

end
end Sechstmoment
