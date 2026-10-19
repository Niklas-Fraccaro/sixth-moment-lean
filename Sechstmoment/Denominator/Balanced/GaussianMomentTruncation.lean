import Sechstmoment.Denominator.Balanced.ActualGaussianTruncation
import Sechstmoment.Denominator.Balanced.ActualMomentComparison
import Sechstmoment.Denominator.Balanced.NormalizedHeightBudget

/-! The actual infinite Gaussian height moment can be replaced by its
literal pair-product cutoff before the six-index Fourier calculation. -/
namespace Sechstmoment
open Complex Real Source MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section

def d02BalancedGaussianFiniteMoment (T : ℝ) (σ : SecondMomentShifts)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) (δ : ℝ) : ℂ :=
  ∫ t : ℝ,(Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*
    d02CenteredGaussianFinitePair T t σ (T^(1+δ))

theorem d02ActualGaussianFinitePair_time_measurable (α : SecondMomentShifts) (X : ℝ) :
    Measurable (fun t : ℝ => d02ActualGaussianFinitePair t α X) := by
  unfold d02ActualGaussianFinitePair
  exact Finset.measurable_sum _ (fun n _ => d02ActualGaussianSummand_time_measurable α n)

theorem d02CenteredGaussianFinitePair_time_measurable (T X : ℝ) (σ : SecondMomentShifts) :
    Measurable (fun t : ℝ => d02CenteredGaussianFinitePair T t σ X) := by
  unfold d02CenteredGaussianFinitePair secondDualPower
  apply measurable_const.mul
  apply (d02ActualGaussianFinitePair_time_measurable _ X).add
  exact (d02Measurable_cpow_const
    (Complex.measurable_ofReal.comp (measurable_id.div_const (2*Real.pi))) _).mul
    (d02ActualGaussianFinitePair_time_measurable _ X)

/-- On the physical window, a negative square power of the left endpoint
is at most four times the same power of the actual height. -/
theorem d02_window_inverse_square {T t : ℝ} (hT : 0<T) (ht : t∈Icc T (2*T)) :
    T^(-2:ℝ)≤4*t^(-2:ℝ) := by
  have htp : 0<t := hT.trans_le ht.1
  have hhalf : t/2≤T := by linarith [ht.2]
  calc
    _ ≤ (t/2)^(-2:ℝ) := Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by norm_num)
    _ = _ := by
      have htE : t^(-2:ℝ)=(t^2)⁻¹ := by rw [Real.rpow_neg htp.le,Real.rpow_two]
      have h2E : (2:ℝ)^(-2:ℝ)=1/4 := by norm_num
      rw [Real.div_rpow htp.le (by norm_num : (0:ℝ)≤2) (-2:ℝ),htE,h2E]
      ring

/-- Both Gaussian halves have a derived, uniform physical height tail
budget.  The finite integrability receipt follows from the proved infinite
moment integrability and the same measurable tail domination. -/
theorem d02BalancedGaussianMoment_truncation_uniform_bound {R ε δ : ℝ}
    (hR : 0≤R) (hε : 0<ε) (hε1 : ε≤1/4) (hδ : 0<δ)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i,Continuous (ρ i)) (hs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : SecondMomentShifts,(∀ j,‖σ j‖≤R) →
      Integrable (fun t : ℝ => (Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*
        d02CenteredGaussianFinitePair T t σ (T^(1+δ))) ∧
      ‖d02BalancedGaussianMoment T σ ρ Φ-d02BalancedGaussianFiniteMoment T σ ρ Φ δ‖≤
        C*T^(-1+(∑ i,a i)/2) := by
  have hM : ∀ i,∃ M : ℝ,0≤M ∧ ∀ x,|ρ i x|≤M :=
    fun i => d02Continuous_supported_norm_bound (hρ i) (hs i)
  choose M hM hρM using hM
  obtain ⟨P,hP,hΦP⟩ := d02Continuous_supported_norm_bound hΦ hΦs
  obtain ⟨K,hK,hpoint⟩ := d02CenteredGaussianPair_truncation_arbitrary_power
    (B := 2) hR hε hε1 hδ (by norm_num)
  have hprod : 0≤∏ i,2*M i :=
    Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (hM i)
  refine ⟨P*(∏ i,2*M i)*(4*K),by positivity,?_⟩
  filter_upwards [hpoint,d02CenteredGaussianMoment_eventually_integrable
    hR hε hε1 a ρ hρ hs Φ hΦ hΦs,eventually_gt_atTop (1:ℝ)] with T hp hfull hT
  intro σ hσ
  have hTp : 0<T := zero_lt_one.trans hT
  let E : ℝ → ℂ := fun t => d02CenteredGaussianPair T t σ-
    d02CenteredGaussianFinitePair T t σ (T^(1+δ))
  let F : ℝ → ℂ := fun t => (Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*E t
  have hcap : ∀ i x,a i<x → ρ i x=0 := by
    intro i x hx
    by_contra hne
    exact (not_le_of_gt hx) (hs i (subset_tsupport (ρ i) hne)).2
  have hΦzero : ∀ x,x∉Icc (1:ℝ) 2 → Φ x=0 := by
    intro x hx
    by_contra hne
    exact hx (hΦs (subset_tsupport Φ hne))
  have hEm : Measurable E := (d02CenteredGaussianPair_time_measurable T σ).sub
    (d02CenteredGaussianFinitePair_time_measurable T (T^(1+δ)) σ)
  have hFm : Measurable F := (((Complex.measurable_ofReal.comp
    (hΦ.measurable.comp (measurable_id.div_const T))).mul
      (d02BalancedAmplifier_time_measurable T ρ)).mul hEm)
  have hErr : Integrable F := by
    apply d02Measurable_window_integrable (u := T) (v := 2*T)
      (B := P*((∏ i,2*M i)*T^((∑ i,a i)/2))*(K*T^(-2:ℝ))) hFm
    · intro t ht
      have hnot : t/T∉Icc (1:ℝ) 2 := by
        intro h
        exact ht ⟨by simpa only [one_mul] using (le_div_iff₀ hTp).mp h.1,
          (div_le_iff₀ hTp).mp h.2⟩
      simp only [F,hΦzero _ hnot,Complex.ofReal_zero,zero_mul]
    · intro t ht
      dsimp [F]
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      have ha0 : 0≤(∏ i,2*M i)*T^((∑ i,a i)/2) :=
        mul_nonneg hprod (Real.rpow_nonneg hTp.le _)
      exact mul_le_mul (mul_le_mul (hΦP _)
        (d02BalancedAmplifier_norm_le hT t a M hM ρ hρM hcap) (norm_nonneg _) hP)
        (hp t ht σ hσ) (norm_nonneg _) (mul_nonneg hP ha0)
  have hfinite : Integrable (fun t : ℝ => (Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*
      d02CenteredGaussianFinitePair T t σ (T^(1+δ))) := by
    apply ((hfull σ hσ).sub hErr).congr
    exact Eventually.of_forall fun t => by dsimp [F,E]; ring
  refine ⟨hfinite,?_⟩
  have he : d02BalancedGaussianMoment T σ ρ Φ-d02BalancedGaussianFiniteMoment T σ ρ Φ δ =
      ∫ t : ℝ,F t := by
    unfold d02BalancedGaussianMoment d02BalancedGaussianFiniteMoment
    rw [←integral_sub (hfull σ hσ) hfinite]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by dsimp [F,E]; ring
  rw [he]
  apply d02BalancedMoment_pointwise_error_bound hT (by norm_num : (-1:ℝ)≤1)
    (by positivity : 0≤4*K) hP a M hM ρ hρM hcap Φ hΦP hΦzero E
  intro t ht
  have hp' := hp t ht σ hσ
  change ‖E t‖≤(4*K)*t^((-1:ℝ)-1)
  calc
    _ ≤ K*T^(-2:ℝ) := hp'
    _ ≤ K*(4*t^(-2:ℝ)) := mul_le_mul_of_nonneg_left (d02_window_inverse_square hTp ht) hK
    _ = _ := by rw [show (-1:ℝ)-1=-2 by norm_num]; ring

/-- The derived tail budget vanishes uniformly in the actual denominator
normalization. Finite physical-time integrability remains a conclusion. -/
theorem d02BalancedGaussianMoment_truncation_normalized_uniform {R ε δ : ℝ}
    (hR : 0≤R) (hε : 0<ε) (hε1 : ε≤1/4) (hδ : 0<δ)
    (a : Fin 4 → ℝ) (hS : (∑ i,a i)<1) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i,Continuous (ρ i)) (hs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {η : ℝ} (hη : 0<η) :
    ∀ᶠ T : ℝ in atTop,∀ σ : SecondMomentShifts,(∀ j,‖σ j‖≤R) →
      Integrable (fun t : ℝ => (Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*
        d02CenteredGaussianFinitePair T t σ (T^(1+δ))) ∧
      ‖(d02BalancedGaussianMoment T σ ρ Φ-d02BalancedGaussianFiniteMoment T σ ρ Φ δ)/
        (T*(Real.log T)^9:ℂ)‖<η := by
  obtain ⟨C,_hC,hbound⟩ := d02BalancedGaussianMoment_truncation_uniform_bound
    hR hε hε1 hδ a ρ hρ hs Φ hΦ hΦs
  have hSmall := d02PowerHeight_normalized_uniform_small
    (fun T σ => d02BalancedGaussianMoment T σ ρ Φ-d02BalancedGaussianFiniteMoment T σ ρ Φ δ)
    (fun σ => ∀ j,‖σ j‖≤R) (C := C) (e := -1+(∑ i,a i)/2)
    (by linarith : -1+(∑ i,a i)/2<1)
    (hbound.mono (fun T hT σ hσ => (hT σ hσ).2)) hη
  filter_upwards [hbound,hSmall] with T hInt hNorm
  intro σ hσ
  exact ⟨(hInt σ hσ).1,hNorm σ hσ⟩

/-- The actual infinite-to-finite Gaussian error tends to zero for every
fixed original shift in a bounded box. No saving estimate is assumed. -/
theorem d02BalancedGaussianMoment_truncation_normalized_tendsto {R ε δ : ℝ}
    (hR : 0≤R) (hε : 0<ε) (hε1 : ε≤1/4) (hδ : 0<δ)
    (a : Fin 4 → ℝ) (hS : (∑ i,a i)<1) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i,Continuous (ρ i)) (hs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (σ : SecondMomentShifts) (hσ : ∀ j,‖σ j‖≤R) :
    Tendsto (fun T : ℝ =>
      (d02BalancedGaussianMoment T σ ρ Φ-d02BalancedGaussianFiniteMoment T σ ρ Φ δ)/
        (T*(Real.log T)^9:ℂ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  filter_upwards [d02BalancedGaussianMoment_truncation_normalized_uniform
    hR hε hε1 hδ a hS ρ hρ hs Φ hΦ hΦs hη] with T hT
  simpa only [dist_zero_right] using (hT σ hσ).2

/-- Every fixed original shift determines a finite box automatically. -/
theorem d02BalancedGaussianMoment_truncation_normalized_tendsto_fixed_shifts {ε δ : ℝ}
    (hε : 0<ε) (hε1 : ε≤1/4) (hδ : 0<δ)
    (a : Fin 4 → ℝ) (hS : (∑ i,a i)<1) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i,Continuous (ρ i)) (hs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (σ : SecondMomentShifts) :
    Tendsto (fun T : ℝ =>
      (d02BalancedGaussianMoment T σ ρ Φ-d02BalancedGaussianFiniteMoment T σ ρ Φ δ)/
        (T*(Real.log T)^9:ℂ)) atTop (𝓝 0) := by
  let R := ‖σ 0‖+‖σ 1‖
  have hR : 0≤R := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hσ : ∀ j,‖σ j‖≤R := by
    intro j
    fin_cases j
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  exact d02BalancedGaussianMoment_truncation_normalized_tendsto
    hR hε hε1 hδ a hS ρ hρ hs Φ hΦ hΦs σ hσ

/-- One eventual bound controls the normalized truncation error on the
whole shift box, and the literal finite height integrand is integrable. -/
theorem d02BalancedGaussianMoment_truncation_normalized_eventually_norm_le_one {R ε δ : ℝ}
    (hR : 0≤R) (hε : 0<ε) (hε1 : ε≤1/4) (hδ : 0<δ)
    (a : Fin 4 → ℝ) (hS : (∑ i,a i)<1) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i,Continuous (ρ i)) (hs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2) :
    ∀ᶠ T : ℝ in atTop,∀ σ : SecondMomentShifts,(∀ j,‖σ j‖≤R) →
      Integrable (fun t : ℝ => (Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*
        d02CenteredGaussianFinitePair T t σ (T^(1+δ))) ∧
      ‖(d02BalancedGaussianMoment T σ ρ Φ-d02BalancedGaussianFiniteMoment T σ ρ Φ δ)/
        (T*(Real.log T)^9:ℂ)‖≤1 := by
  filter_upwards [d02BalancedGaussianMoment_truncation_normalized_uniform
    hR hε hε1 hδ a hS ρ hρ hs Φ hΦ hΦs (by norm_num : (0:ℝ)<1)] with T hT
  intro σ hσ
  exact ⟨(hT σ hσ).1,(hT σ hσ).2.le⟩

end
end Sechstmoment
