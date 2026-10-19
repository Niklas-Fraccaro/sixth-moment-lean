import Sechstmoment.Numerator.U.Sources.OffdiagonalMoment
import Sechstmoment.Numerator.U.ZeroModes.Replacement.Identity

/-! The proved genuine Gamma-zero replacement is attached to the literal
source Gamma zero moment, including its 1/(2*pi) contour prefactor. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualSourceLeadingZeroBlock (dual positive : Bool) (Φ : ℝ→ℂ)
    (c T s v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℂ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let α := a03SourceShifts dual T σ
  let p := phaseActualNearTensorData T σ α v A B H i.2 positive
  if phaseActualActiveNearBlock T A B H (T^(s-1)) f g i.2 then
    (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*
      a03EndpointPhysicalSortedZeroMode (a03ZeroModeLeadingKernel dual Φ c p) T A B H f g i.2
  else 0

def a03ActualSourceLeadingZeroFinite (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s η v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool,∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+η/2)) (T^(2+η)),a03ActualSourceLeadingZeroBlock dual positive Φ c T s v σ f g i

def a03ActualSourceLeadingZeroMoment (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s η θ : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∫ v in Icc (-θ*Real.log T) (θ*Real.log T),a03ActualSourceLeadingZeroFinite dual Φ c T a b s η v σ f g

def a03ActualFiniteLeadingZeroMoment (dual : Bool) (c T a b s η θ : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*a03ActualSourceLeadingZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s η θ σ f g

theorem a03ActualZeroModeGammaReplacementFinite_eq_source_sub_leading
    (dual : Bool) (Φ : ℝ→ℂ) (c T a b s η v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) :
    a03ActualZeroModeGammaReplacementFinite dual Φ c T a b s η v σ f g=
      a03ActualSourceFiniteValue true dual Φ c T a b s η v σ f g-
        a03ActualSourceLeadingZeroFinite dual Φ c T a b s η v σ f g := by
  unfold a03ActualZeroModeGammaReplacementFinite a03ActualSourceFiniteValue a03ActualSourceLeadingZeroFinite
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro positive _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold a03ActualZeroModeGammaReplacementBlock a03ActualSourceBlockValue a03ActualSourceLeadingZeroBlock
  dsimp only
  simp only [ite_true]
  split_ifs <;> ring

theorem a03_actual_source_Gamma_zero_sub_leading_uniform_oT
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s<1/2)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hη : 0<η)
    (hexp : (a+b)/2+s+η/2+ε<1) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      IntegrableOn (fun v => a03ActualSourceFiniteValue true dual Φ c T a b s η v σ f g)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      IntegrableOn (fun v => a03ActualSourceLeadingZeroFinite dual Φ c T a b s η v σ f g)
        (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      ‖a03ActualSourceGammaZeroMoment dual Φ c T a b s η θ σ f g-
        a03ActualSourceLeadingZeroMoment dual Φ c T a b s η θ σ f g‖≤δ*T := by
  intro δ hδ
  filter_upwards [a03_actual_gamma_zero_replacement_uniform_oT ha hab hlen hs0 hs f g hf hg hΦ hΦs
      hc hc1 hε hκ hθ hR hη hexp δ hδ,
    a03_actual_source_finite_values_integrableOn false hΦ hΦs hc hc1 (by linarith : 4*c<4*c+1)
      hκ hθ hR (by linarith : s<1) a b η f g,
    a03_actual_source_finite_values_integrableOn true hΦ hΦs hc hc1 (by linarith : 4*c<4*c+1)
      hκ hθ hR (by linarith : s<1) a b η f g] with T hr hi0 hi1
  intro σ hσ hroot dual
  have hr := hr σ hσ hroot dual
  have hi : IntegrableOn (fun v => a03ActualSourceFiniteValue true dual Φ c T a b s η v σ f g)
      (Icc (-θ*Real.log T) (θ*Real.log T)) := by cases dual; exact hi0 σ hσ hroot true; exact hi1 σ hσ hroot true
  have hl : IntegrableOn (fun v => a03ActualSourceLeadingZeroFinite dual Φ c T a b s η v σ f g)
      (Icc (-θ*Real.log T) (θ*Real.log T)) := by
    apply (hi.sub hr.1).congr
    exact ae_of_all _ fun v => by simp only [Pi.sub_apply]; rw [a03ActualZeroModeGammaReplacementFinite_eq_source_sub_leading]; ring
  refine ⟨hi,hl,?_⟩
  have he : a03ActualZeroModeGammaReplacementMoment dual Φ c T a b s η θ σ f g=
      a03ActualSourceGammaZeroMoment dual Φ c T a b s η θ σ f g-
        a03ActualSourceLeadingZeroMoment dual Φ c T a b s η θ σ f g := by
    unfold a03ActualZeroModeGammaReplacementMoment a03ActualSourceGammaZeroMoment a03ActualSourceLeadingZeroMoment
    simp_rw [a03ActualZeroModeGammaReplacementFinite_eq_source_sub_leading]
    exact integral_sub hi hl
  rw [←he]
  exact hr.2

theorem a03_actual_finite_Gamma_zero_sub_leading_uniform_oT
    {a b s : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s<1/2)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hη : 0<η)
    (hexp : (a+b)/2+s+η/2+ε<1) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ dual : Bool,
      ‖a03ActualFiniteGammaZeroMoment dual c T a b s η θ σ f g Φ-
        a03ActualFiniteLeadingZeroMoment dual c T a b s η θ σ f g Φ‖≤δ*T := by
  intro δ hδ
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 := (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  filter_upwards [a03_actual_source_Gamma_zero_sub_leading_uniform_oT ha hab hlen hs0 hs f g hf hg
    hΦc hΦs hc hc1 hε hκ hθ hR hη hexp δ hδ,eventually_gt_atTop (0:ℝ)] with T hb hT
  intro σ hσ hroot dual
  have hb := (hb σ hσ hroot dual).2.2
  have hconst : ‖(1/(2*Real.pi):ℂ)‖≤1 := by
    rw [norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    exact (div_le_one (by positivity : (0:ℝ)<2*Real.pi)).mpr (by linarith [Real.pi_gt_three])
  unfold a03ActualFiniteGammaZeroMoment a03ActualFiniteLeadingZeroMoment
  rw [←mul_sub,norm_mul]
  exact (mul_le_mul hconst hb (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)

end
end Sechstmoment
