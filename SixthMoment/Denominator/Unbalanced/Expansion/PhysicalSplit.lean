import SixthMoment.Denominator.Unbalanced.CenteringPower
import SixthMoment.Denominator.Unbalanced.Expansion.MomentSplit
import SixthMoment.Denominator.Unbalanced.OffDiagonalClosure

namespace SixthMoment
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def d04OneSidedTimeExponent (T : ℝ) (z : ℂ) : ℂ := -z/(Real.log T : ℂ)

theorem d04OneSidedTimeExponent_norm_le {T R : ℝ} (hL : 1≤Real.log T)
    (_hR : 0≤R) (z : ℂ) (hz : ‖z‖≤R) : ‖d04OneSidedTimeExponent T z‖≤R := by
  unfold d04OneSidedTimeExponent
  rw [norm_div,norm_neg,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans hL)]
  exact (div_le_self (norm_nonneg z) hL).trans hz

theorem d04OneSidedShiftedMoment_physical_partition {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : Fin 2 → ℂ) (hσ : ∀ j,‖σ j‖≤R)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1 : ℝ) 2) :
    d04OneSidedShiftedMoment T σ ρ Φ=
      ((T : ℂ)*d04PhysicalTimeMean T (σ 0) Φ)*d04OneSidedModelDiagonalSum T a ρ σ+
        d04CenteringPurePower T T (σ 0)*
          d04OneSidedModelOffDiagonal T a ρ σ (d04OneSidedTimeExponent T (σ 0))
            (fun y => (Φ y : ℂ)) := by
  have ht : 0<T := zero_lt_one.trans hT
  let τ : ℂ := d04OneSidedTimeExponent T (σ 0)
  let β : ℂ := d04CenteringPurePower T T (σ 0)
  have hΦC : ContDiff ℝ ∞ (fun y => (Φ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ
  have hΦCs : tsupport (fun y => (Φ y : ℂ))⊆Icc (1 : ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦs
  have hfactor (t : ℝ) : (Φ (t/T) : ℂ)*d04CenteringPurePower T t (σ 0)=
      β*((Φ (t/T) : ℂ)*((t/T : ℝ) : ℂ)^τ) := by
    by_cases hz : Φ (t/T)=0
    · rw [hz]
      simp
    · have hy := hΦs (subset_tsupport Φ hz)
      have hyp : 0<t/T := zero_lt_one.trans_le hy.1
      have hf := d04CenteringPurePower_dyadic_factorization ht hyp (σ 0)
      rw [show T*(t/T)=t by field_simp] at hf
      rw [hf]
      dsimp [β,τ,d04OneSidedTimeExponent]
      ring
  have hmean : d04PhysicalTimeMean T (σ 0) Φ=
      β*∫ y : ℝ,(Φ y : ℂ)*(y : ℂ)^τ := by
    unfold d04PhysicalTimeMean
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      by_cases hz : Φ y=0
      · rw [hz]; simp
      · have hyp : 0<y := zero_lt_one.trans_le (hΦs (subset_tsupport Φ hz)).1
        rw [d04CenteringPurePower_dyadic_factorization ht hyp (σ 0)]
        dsimp [β,τ,d04OneSidedTimeExponent]
        ring
  have he : d04OneSidedShiftedMoment T σ ρ Φ=
      β*(∫ t : ℝ,(Φ (t/T) : ℂ)*((t/T : ℝ) : ℂ)^τ*
        d04UnbalancedAmplifier T t ρ*d04OneSidedCenteredPair T t σ) := by
    unfold d04OneSidedShiftedMoment
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [hfactor t]
      ring
  rw [he,d04OneSided_model_timePower_diagonal_partition hT hR (Real.log_pos hT) hRL
    a ρ hcap σ hσ hΦC hΦCs τ, hmean]
  ring

theorem d04OneSidedShiftedMoment_normalized_physical_partition {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : Fin 2 → ℂ) (hσ : ∀ j,‖σ j‖≤R)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1 : ℝ) 2) :
    d04OneSidedShiftedMoment T σ ρ Φ/(T*(Real.log T)^9 : ℂ)=
      d04PhysicalTimeMean T (σ 0) Φ*(d04OneSidedModelDiagonalSum T a ρ σ/(Real.log T : ℂ)^9)+
        d04CenteringPurePower T T (σ 0)*
          (d04OneSidedModelOffDiagonal T a ρ σ (d04OneSidedTimeExponent T (σ 0))
            (fun y => (Φ y : ℂ))/(T*(Real.log T)^9 : ℂ)) := by
  rw [d04OneSidedShiftedMoment_physical_partition hT hR hRL a ρ hcap σ hσ hΦ hΦs]
  have ht : (T : ℂ)≠0 := by exact_mod_cast (zero_lt_one.trans hT).ne'
  have hl : (Real.log T : ℂ)≠0 := by exact_mod_cast (Real.log_pos hT).ne'
  field_simp [ht,hl]

theorem d04CenteringPurePower_base_tendsto (z : ℂ) :
    Tendsto (fun T : ℝ => d04CenteringPurePower T T z) atTop (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [d04CenteringPurePower_uniform_tendsto (R:=‖z‖) hη] with T hT
  have hh := hT 1 (by norm_num) z le_rfl
  simpa only [mul_one,dist_eq_norm] using hh

theorem d04OneSidedShiftedMoment_normalized_tendsto
    (a : Fin 4 → ℝ) (ha : ∀ j,0<a j) (haS : (∑ j,a j)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ j,Continuous (ρ j))
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1 : ℝ) 2)
    (σ : Fin 2 → ℂ) :
    Tendsto (fun T : ℝ => d04OneSidedShiftedMoment T σ ρ Φ/(T*(Real.log T)^9 : ℂ))
      atTop (𝓝 ((arithmeticFactor : ℂ)*(∫ y : ℝ,Φ y : ℂ)*d04UnbalancedShiftedEdgeIntegral ρ σ)) := by
  let R : ℝ := ‖σ 0‖+‖σ 1‖
  have hR : 0≤R := by dsimp [R]; positivity
  have hσ : ∀ j,‖σ j‖≤R := by
    intro j
    fin_cases j <;> dsimp [R] <;> linarith [norm_nonneg (σ 0),norm_nonneg (σ 1)]
  have hcap : ∀ j x,a j<x → ρ j x=0 := by
    intro j x hx
    by_contra hn
    exact (not_lt_of_ge (hρs j (subset_tsupport (ρ j) hn)).2) hx
  have hρcap : ∀ j x,ρ j x≠0 → x∈Icc 0 (a j) :=
    fun j x hx => hρs j (subset_tsupport (ρ j) hx)
  have haP : a 0+a 1+a 2<1 := by
    simp only [Fin.sum_univ_four] at haS
    linarith [ha 3]
  have hΦC : ContDiff ℝ ∞ (fun y => (Φ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ
  have hΦCs : tsupport (fun y => (Φ y : ℂ))⊆Icc (1 : ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦs
  have hτ : ∀ᶠ T : ℝ in atTop,‖d04OneSidedTimeExponent T (σ 0)‖≤R := by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with T hL
    exact d04OneSidedTimeExponent_norm_le hL hR _ (hσ 0)
  have hoff := d04_oneSided_model_offDiagonal_normalized_tendsto hΦC hΦCs a
    (fun j => (ha j).le) haP ρ hρ hρs (fun _ => σ)
    (fun T => d04OneSidedTimeExponent T (σ 0)) hR hR (Eventually.of_forall fun _ => hσ) hτ
  have hmain := (d04PhysicalTimeMean_tendsto (σ 0) Φ hΦ.continuous hΦs).mul
    (d04OneSidedModel_diagonal_limit a ρ σ hρ hρcap (ha 3).le haS)
  have herr := (d04CenteringPurePower_base_tendsto (σ 0)).mul hoff
  have hlim := hmain.add herr
  simp only [mul_zero,add_zero] at hlim
  have htgt : (∫ y : ℝ,Φ y : ℂ)*((arithmeticFactor : ℂ)*d04UnbalancedShiftedEdgeIntegral ρ σ)=
      (arithmeticFactor : ℂ)*(∫ y : ℝ,Φ y : ℂ)*d04UnbalancedShiftedEdgeIntegral ρ σ := by ring
  rw [htgt] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (2*R))] with T hT hRL
  exact (d04OneSidedShiftedMoment_normalized_physical_partition hT hR hRL
    a ρ hcap σ hσ hΦ hΦs).symm

theorem d04OneSidedShiftedMoment_normalized_eventually_uniformly_bounded
    (a : Fin 4 → ℝ) (ha : ∀ j,0<a j) (haS : (∑ j,a j)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ j,Continuous (ρ j))
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1 : ℝ) 2)
    {R : ℝ} (hR : 0≤R) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ T : ℝ in atTop,∀ σ : Fin 2 → ℂ,(∀ j,‖σ j‖≤R) →
      ‖d04OneSidedShiftedMoment T σ ρ Φ/(T*(Real.log T)^9 : ℂ)‖≤B := by
  have hcap : ∀ j x,a j<x → ρ j x=0 := by
    intro j x hx
    by_contra hn
    exact (not_lt_of_ge (hρs j (subset_tsupport (ρ j) hn)).2) hx
  have hρcap : ∀ j x,ρ j x≠0 → x∈Icc 0 (a j) :=
    fun j x hx => hρs j (subset_tsupport (ρ j) hx)
  have haP : a 0+a 1+a 2<1 := by
    simp only [Fin.sum_univ_four] at haS
    linarith [ha 3]
  have hΦC : ContDiff ℝ ∞ (fun y => (Φ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ
  have hΦCs : tsupport (fun y => (Φ y : ℂ))⊆Icc (1 : ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦs
  obtain ⟨B,hB,hdiag⟩ := d04OneSidedModel_diagonal_eventually_uniformly_bounded
    a ρ hρ hρcap (ha 3).le haS hR
  obtain ⟨C,hC,hmean⟩ := d04PhysicalTimeMean_uniform_bounded (R:=R) Φ hΦ.continuous hΦs
  have hoff := d04_oneSided_model_offDiagonal_normalized_uniform_small hΦC hΦCs a
    (fun j => (ha j).le) haP ρ hρ hρs hR hR (by norm_num : (0 : ℝ)<1)
  refine ⟨C*B+3,by positivity,?_⟩
  filter_upwards [hdiag,hmean,hoff,d04CenteringPurePower_uniform_norm (R:=R),
    eventually_gt_atTop (1 : ℝ),Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (max 1 (2*R)))] with T hd hm ho hp hT hL
  intro σ hσ
  have hτ := d04OneSidedTimeExponent_norm_le ((le_max_left _ _).trans hL) hR _ (hσ 0)
  have hoffT := (ho σ _ hσ hτ).le
  have hpref := hp 1 (by norm_num) (σ 0) (hσ 0)
  rw [mul_one] at hpref
  rw [d04OneSidedShiftedMoment_normalized_physical_partition hT hR
    ((le_max_right _ _).trans hL) a ρ hcap σ hσ hΦ hΦs]
  calc
    _ ≤ ‖d04PhysicalTimeMean T (σ 0) Φ*
        (d04OneSidedModelDiagonalSum T a ρ σ/(Real.log T : ℂ)^9)‖+
        ‖d04CenteringPurePower T T (σ 0)*
          (d04OneSidedModelOffDiagonal T a ρ σ (d04OneSidedTimeExponent T (σ 0))
            (fun y => (Φ y : ℂ))/(T*(Real.log T)^9 : ℂ))‖ := norm_add_le _ _
    _ ≤ C*B+2*1 := by
      rw [norm_mul,norm_mul]
      exact add_le_add
        (mul_le_mul (hm _ (hσ 0)) (hd σ hσ) (norm_nonneg _) hC)
        (mul_le_mul hpref hoffT (norm_nonneg _) (by norm_num))
    _ ≤ _ := by linarith

end
end SixthMoment
