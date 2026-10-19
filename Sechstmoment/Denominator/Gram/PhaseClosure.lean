import Sechstmoment.Denominator.Gram.NonstationaryChiDecay
import Sechstmoment.Denominator.Gram.PhaseCauchy
import Sechstmoment.Denominator.Gram.PhaseRegularity

/-! The two literal extreme denominator phases vanish. The proof retains
every amplifier and one-sided series index, derives a uniform residual-chi
Fourier saving, and then extracts every finite polynomial shift derivative. -/
namespace Sechstmoment
open Complex Real Set Filter MeasureTheory Polynomial Metric
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem d06ExtremeOneSidedMoment_uniform_power_bound
    (a : Fin 4 → ℝ) (haS : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0≤R) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : Fin 2 → ℂ,(∀ i,‖σ i‖≤R) →
      ‖d06ExtremeOneSidedMoment T σ ρ Φ‖≤C*T^(-2+(∑ i,a i)/2) := by
  have hΦC : ContDiff ℝ ∞ (fun y => (Φ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ
  have hΦCs : tsupport (fun y => (Φ y : ℂ))⊆Icc (1:ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦs
  obtain ⟨D,hD,hdec⟩ := d06_chi_time_power_profile_fourier_decay hΦC hΦCs hR haS 9
  have hb : ∀ i : Fin 4,∃ M : ℝ,0≤M ∧ ∀ x,|ρ i x|≤M :=
    fun i => d02Continuous_supported_norm_bound (hρ i) (hρs i)
  choose M hM hm using hb
  let F : ℝ := ∑ i,M i
  have hF : 0≤F := Finset.sum_nonneg (fun i _ => hM i)
  have hρF : ∀ i x,|ρ i x|≤F := by
    intro i x
    exact (hm i x).trans (Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ i))
  have hcap : ∀ i x,a i<x → ρ i x=0 := by
    intro i x hx
    by_contra hn
    exact (not_le_of_gt hx) (hρs i (subset_tsupport (ρ i) hn)).2
  let C : ℝ := 9*D*Real.exp R*F^4*2^4
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hdec,d04CenteringPurePower_uniform_norm (R:=R),
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (max 1 (2*R)))] with T hd hp hT hL
  intro σ hσ
  have hL1 : 1≤Real.log T := (le_max_left _ _).trans hL
  have hRL : 2*R≤Real.log T := (le_max_right _ _).trans hL
  have ht : 0<T := zero_lt_one.trans hT
  let τ : ℂ := -σ 0/(Real.log T : ℂ)
  have hτ : ‖τ‖≤R := by
    dsimp [τ]
    rw [norm_div,norm_neg,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans hL1)]
    exact (div_le_self (norm_nonneg _) hL1).trans (hσ 0)
  have hfourier : ∀ h∈d04ProfileBox T a,∀ n : ℕ × ℕ,
      ‖a03ProfileTimeFourier (d06ChiTimePowerProfile T (fun y => (Φ y : ℂ)) τ) T
        (d06OneSidedModelFrequency h n)‖≤D*T^(-8:ℝ) := by
    intro h hh n
    convert hd τ hτ _ (d06OneSidedModelFrequency_lower_bound hT a h hh n) using 1 <;>
      first | rfl | norm_num
  have hmT := d06ExtremeModelFourierSum_bound_of_frequency_bound
    (A:=8) hT hR hF hD (Real.log_pos hT) hRL a ρ hρF σ hσ τ
      (fun y => (Φ y : ℂ)) hfourier
  have hpT := hp 1 (by norm_num : (1:ℝ)∈Icc 1 2) (σ 0) (hσ 0)
  simp only [mul_one] at hpT
  rw [d06ExtremeOneSidedMoment_fourier_identity hT hR hRL a ρ hcap σ hσ hΦ hΦs,norm_mul]
  exact (mul_le_mul hpT hmT (norm_nonneg _) (by norm_num : (0:ℝ)≤2)).trans_eq (by
    dsimp [C,τ]
    rw [show (6:ℝ)+(∑ i,a i)/2-8 = -2+(∑ i,a i)/2 by ring]
    ring)

theorem d06ExtremeOneSidedMoment_normalized_uniform_small
    (a : Fin 4 → ℝ) (haS : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    {R η : ℝ} (hR : 0≤R) (hη : 0<η) :
    ∀ᶠ T : ℝ in atTop,∀ σ : Fin 2 → ℂ,(∀ i,‖σ i‖≤R) →
      ‖d06ExtremeOneSidedMoment T σ ρ Φ/(T*(Real.log T)^9 : ℂ)‖<η := by
  obtain ⟨C,_hC,hbound⟩ := d06ExtremeOneSidedMoment_uniform_power_bound
    a haS ρ hρ hρs hΦ hΦs hR
  exact d02PowerHeight_normalized_uniform_small
    (fun T σ => d06ExtremeOneSidedMoment T σ ρ Φ) (fun σ => ∀ i,‖σ i‖≤R)
    (by linarith : -2+(∑ i,a i)/2<1) hbound hη

theorem d06ExtremeMinusShiftedMoment_normalized_uniform_small
    (a : Fin 4 → ℝ) (ha : ∀ i,0<a i) (haS : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    {R η : ℝ} (hR : 0≤R) (hη : 0<η) :
    ∀ᶠ T : ℝ in atTop,∀ σ : Fin 2 → ℂ,(∀ i,‖σ i‖≤R) →
      ‖d06ExtremeMinusShiftedMoment T σ ρ Φ/(T*(Real.log T)^9 : ℂ)‖<η := by
  have hhalf : 0<η/2 := by positivity
  filter_upwards [d06ExtremeMomentError_normalized_uniform_small
    a ha haS ρ hρ hρs Φ hΦ.continuous hΦs hR hhalf,
    d06ExtremeOneSidedMoment_normalized_uniform_small a haS ρ hρ hρs hΦ hΦs hR hhalf,
    d06ExtremeMomentError_eventually_eq_difference R ρ a hρs Φ hΦ hΦs]
    with T he hm hd
  intro σ hσ
  have heq : d06ExtremeMinusShiftedMoment T σ ρ Φ/(T*(Real.log T)^9 : ℂ)=
      d06ExtremeMomentError T σ ρ Φ/(T*(Real.log T)^9 : ℂ)+
        d06ExtremeOneSidedMoment T σ ρ Φ/(T*(Real.log T)^9 : ℂ) := by
    rw [hd σ hσ]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans_lt ((add_lt_add (he σ hσ) (hm σ hσ)).trans_eq (by ring))

theorem d06ExtremeMinusShiftedMoment_normalized_tendsto
    (a : Fin 4 → ℝ) (ha : ∀ i,0<a i) (haS : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    (σ : Fin 2 → ℂ) :
    Tendsto (fun T : ℝ => d06ExtremeMinusShiftedMoment T σ ρ Φ/
      (T*(Real.log T)^9 : ℂ)) atTop (𝓝 0) := by
  let R : ℝ := ‖σ 0‖+‖σ 1‖
  have hR : 0≤R := by dsimp [R]; positivity
  have hσ : ∀ i,‖σ i‖≤R := by
    intro i
    fin_cases i <;> dsimp [R] <;> linarith [norm_nonneg (σ 0),norm_nonneg (σ 1)]
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [d06ExtremeMinusShiftedMoment_normalized_uniform_small
    a ha haS ρ hρ hρs hΦ hΦs hR hη] with T hT
  simpa only [dist_eq_norm,sub_zero] using hT σ hσ

theorem d06ExtremeMinusPolynomialMoment_normalized_tendsto
    (a : Fin 4 → ℝ) (ha : ∀ i,0<a i) (haS : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2)
    (p q : ℝ[X]) :
    Tendsto (fun T : ℝ => d06ExtremeMinusPolynomialMoment T p q ρ Φ/
      (T*(Real.log T)^9 : ℂ)) atTop (𝓝 0) := by
  have hb : ∀ᶠ T : ℝ in atTop,∀ z∈sphere (0:ℂ) 1,∀ w∈sphere (0:ℂ) 1,
      ‖d06ExtremeMinusShiftedMoment T ![z,w] ρ Φ/(T*(Real.log T)^9 : ℂ)‖≤1 := by
    filter_upwards [d06ExtremeMinusShiftedMoment_normalized_uniform_small
      a ha haS ρ hρ hρs hΦ hΦs (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)<1)]
      with T hT
    intro z hz w hw
    apply (hT ![z,w] ?_).le
    intro i
    fin_cases i
    · exact (mem_sphere_zero_iff_norm.mp hz).le
    · exact (mem_sphere_zero_iff_norm.mp hw).le
  have hl : ∀ z∈sphere (0:ℂ) 1,∀ w∈sphere (0:ℂ) 1,
      Tendsto (fun T : ℝ => d06ExtremeMinusShiftedMoment T ![z,w] ρ Φ/
        (T*(Real.log T)^9 : ℂ)) atTop (𝓝 ((fun _ _ : ℂ => (0:ℂ)) z w)) := by
    intro z _ w _
    exact d06ExtremeMinusShiftedMoment_normalized_tendsto a ha haS ρ hρ hρs hΦ hΦs ![z,w]
  have hz (r : ℝ[X]) : d02PolynomialCircle r (fun _ => 0)=0 := by
    simp [d02PolynomialCircle,d02CircleExtract,Polynomial.sum_def,circleIntegral]
  simpa only [hz] using
    d06ExtremeMinusPolynomialMoment_tendsto_of_pointwise_shifted p q ρ a hρs
      Φ hΦ hΦs (fun _ _ => 0) 1 hb hl

theorem d06ExtremeMinusVanishing_closed : D06ExtremeMinusVanishing := by
  intro a ha haS ρ hρ hρs Φ hΦ hΦs p q _hp _hq
  exact d06ExtremeMinusPolynomialMoment_normalized_tendsto a ha haS ρ hρ hρs hΦ hΦs p q

theorem d06ExtremePlusVanishing_closed : D06ExtremePlusVanishing :=
  d06ExtremePlusVanishing_of_minus d06ExtremeMinusVanishing_closed

end
end Sechstmoment
