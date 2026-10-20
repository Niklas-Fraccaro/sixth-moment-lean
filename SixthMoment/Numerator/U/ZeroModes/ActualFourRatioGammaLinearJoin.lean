import SixthMoment.Numerator.U.ZeroModes.Ratio.OffdiagonalGammaMoment
import SixthMoment.Numerator.U.ZeroModes.Ratio.ZeroReplacementMoment

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualFourRatioLinearZeroMoment (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s u εsource θ : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ m : Bool,∑ n : Bool,a03ActualRatioSourceLinearZeroMoment dual Φ c T a b s u εsource θ σ
    (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g

def a03ActualFiniteFourRatioLinearZeroMoment (dual : Bool) (c T a b s u εsource θ : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*a03ActualFourRatioLinearZeroMoment dual (fun x => (Φ x:ℂ))
    c T a b s u εsource θ σ f g

theorem a03_actual_four_ratio_Gamma_zero_sub_linear_uniform
    {a b s u εsource c ε κ θ R : ℝ} (ha : 0≤a) (hb : 0≤b) (hs0 : 0≤s) (hs : s<1) (hu : 0<u)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ)
    (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hexp : (a+b)/2+3*s+u/2+ε<1) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ‖(∑ dual : Bool,a03ActualFiniteFourRatioGammaZeroMoment dual c T a b s u εsource θ σ f g Φ)-
        ∑ dual : Bool,a03ActualFiniteFourRatioLinearZeroMoment dual c T a b s u εsource θ σ f g Φ‖≤δ*T := by
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 := (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  intro δ hδ
  filter_upwards [a03_actual_ratio_source_Gamma_zero_sub_linear_uniform_oT ha hb hs0 hs f g hf hg hΦc hΦs
      hc hc1 hε hκ hθ hR hu hexp εsource (δ/8) (by positivity),
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_gt_atTop (1:ℝ)] with T hbound hraw hlog hT
  intro σ hσ hroot
  have hconst : ‖(1/(2*Real.pi):ℂ)‖≤1 := by
    rw [norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    exact (div_le_one (by positivity : (0:ℝ)<2*Real.pi)).mpr (by linarith [Real.pi_gt_three])
  have hsingle (dual m n : Bool) :
      ‖a03ActualRatioSourceValueMoment true dual (fun x => (Φ x:ℂ)) c T a b s u εsource θ σ
          (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g-
        a03ActualRatioSourceLinearZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s u εsource θ σ
          (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g‖≤(δ/8)*T :=
    (hbound σ _ hσ (a03SourceChamberShifts_norm_le_quarter dual σ (hraw σ hσ) m n)
      (a03SourceChamberShifts_norm_le_raw_scale (zero_lt_one.trans_le hlog) dual σ hσ m n) hroot dual).2
  have hdual (dual : Bool) :
      ‖a03ActualFiniteFourRatioGammaZeroMoment dual c T a b s u εsource θ σ f g Φ-
        a03ActualFiniteFourRatioLinearZeroMoment dual c T a b s u εsource θ σ f g Φ‖≤(δ/2)*T := by
    unfold a03ActualFiniteFourRatioGammaZeroMoment a03ActualFiniteFourRatioLinearZeroMoment
      a03ActualFourRatioGammaZeroMoment a03ActualFourRatioLinearZeroMoment
    rw [←mul_sub,norm_mul]
    apply (mul_le_mul_of_nonneg_left (show ‖(∑ m : Bool,∑ n : Bool,a03ActualRatioSourceValueMoment true dual
        (fun x => (Φ x:ℂ)) c T a b s u εsource θ σ (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g)-
      ∑ m : Bool,∑ n : Bool,a03ActualRatioSourceLinearZeroMoment dual (fun x => (Φ x:ℂ))
        c T a b s u εsource θ σ (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g‖≤(δ/2)*T from ?_)
      (norm_nonneg _)).trans
    · exact (mul_le_mul_of_nonneg_right hconst (mul_nonneg (by positivity : 0≤δ/2) (zero_lt_one.trans hT).le)).trans_eq (one_mul _)
    · rw [←Finset.sum_sub_distrib]
      simp_rw [←Finset.sum_sub_distrib]
      calc
        _≤∑ m : Bool,‖∑ n : Bool,(a03ActualRatioSourceValueMoment true dual (fun x => (Φ x:ℂ))
          c T a b s u εsource θ σ (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g-
            a03ActualRatioSourceLinearZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s u εsource θ σ
              (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g)‖ := norm_sum_le _ _
        _≤∑ _m : Bool,∑ _n : Bool,(δ/8)*T := by
          apply Finset.sum_le_sum
          intro m _
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => hsingle dual m n))
        _=(δ/2)*T := by simp only [Fintype.sum_bool]; ring
  rw [←Finset.sum_sub_distrib]
  calc
    _≤∑ dual : Bool,‖a03ActualFiniteFourRatioGammaZeroMoment dual c T a b s u εsource θ σ f g Φ-
      a03ActualFiniteFourRatioLinearZeroMoment dual c T a b s u εsource θ σ f g Φ‖ := norm_sum_le _ _
    _≤∑ _dual : Bool,(δ/2)*T := Finset.sum_le_sum (fun dual _ => hdual dual)
    _=δ*T := by simp only [Fintype.sum_bool]; ring

theorem a03_actual_four_ratio_replacement_slack_budget {a b s u : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs : s≤1/8) (hu : u≤1/8) :
    0<rectangularSlack a b/512 ∧ rectangularSlack a b/512≤1 ∧
      2*(rectangularSlack a b/512)<rectangularSlack a b/16 ∧
      (a+b)/2+3*s+u/2+rectangularSlack a b/16<1 := by
  have hb := ha.trans hab
  unfold rectangularSlack
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem a03_actual_four_ratio_Gamma_zero_sub_linear_uniform_slack
    {a b s u κ θ R : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (hs0 : 0≤s) (hs : s≤1/8) (hu0 : 0<u) (hu : u≤1/8)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ‖(∑ dual : Bool,a03ActualFiniteFourRatioGammaZeroMoment dual (rectangularSlack a b/512)
          T a b s u (rectangularSlack a b/128) θ σ f g Φ)-
        ∑ dual : Bool,a03ActualFiniteFourRatioLinearZeroMoment dual (rectangularSlack a b/512)
          T a b s u (rectangularSlack a b/128) θ σ f g Φ‖≤δ*T := by
  obtain ⟨hc,hc1,he,hexp⟩ := a03_actual_four_ratio_replacement_slack_budget ha hab hlen hs hu
  exact a03_actual_four_ratio_Gamma_zero_sub_linear_uniform
    (ε:=rectangularSlack a b/16) ha (ha.trans hab) hs0 (by linarith : s<1) hu0
    f g Φ hf hg hΦ hc hc1 he hκ hθ hR hexp

end
end SixthMoment
