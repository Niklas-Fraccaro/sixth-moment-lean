import Sechstmoment.Denominator.Gram.PhaseDefinitions
import Sechstmoment.Denominator.Unbalanced.MomentComparison

namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem d06AllPositiveMoment_uniform_window_error_bound {T d C P : ℝ}
    (hT : 1<T) (hP : 0≤P)
    (a M : Fin 4 → ℝ) (hM : ∀ i,0≤M i)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i x,|ρ i x|≤M i)
    (hcap : ∀ i x,a i<x → ρ i x=0)
    (Φ : ℝ → ℝ) (hΦ : ∀ x,|Φ x|≤P)
    (hΦs : ∀ x,x∉Icc 1 2 → Φ x=0)
    (E : ℝ → ℂ) (hE : ∀ t∈Icc T (2*T),‖E t‖≤C*T^d) :
    ‖∫ t : ℝ,(Φ (t/T):ℂ)*d06AllPositiveAmplifier T t ρ*E t‖≤
      (P*(∏ i,2*M i)*C)*T^(d+1+(∑ i,a i)/2) := by
  have hTp : 0<T := zero_lt_one.trans hT
  have hsupp : (∫ t : ℝ,(Φ (t/T):ℂ)*d06AllPositiveAmplifier T t ρ*E t)=
      ∫ t in Icc T (2*T),(Φ (t/T):ℂ)*d06AllPositiveAmplifier T t ρ*E t := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hnot : t/T∉Icc 1 2 := by
      intro h
      apply ht
      exact ⟨by simpa only [one_mul] using (le_div_iff₀ hTp).mp h.1,
        (div_le_iff₀ hTp).mp h.2⟩
    rw [hΦs _ hnot]
    simp
  rw [hsupp]
  have hb (t : ℝ) (ht : t∈Icc T (2*T)) :
      ‖(Φ (t/T):ℂ)*d06AllPositiveAmplifier T t ρ*E t‖≤
        P*((∏ i,2*M i)*T^((∑ i,a i)/2))*(C*T^d) := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have ha0 : 0≤(∏ i,2*M i)*T^((∑ i,a i)/2) := mul_nonneg
      (Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (hM i))
      (Real.rpow_nonneg hTp.le _)
    exact mul_le_mul
      (mul_le_mul (hΦ _) (d06AllPositiveAmplifier_norm_le hT t a M hM ρ hρ hcap)
        (norm_nonneg _) hP) (hE t ht) (norm_nonneg _) (mul_nonneg hP ha0)
  apply (norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top hb).trans_eq
  rw [Real.volume_real_Icc,max_eq_left (by linarith)]
  have hp : T^((∑ i,a i)/2)*T^d*T=T^(d+1+(∑ i,a i)/2) := by
    conv_lhs => arg 2; rw [← Real.rpow_one T]
    rw [← Real.rpow_add hTp,← Real.rpow_add hTp]
    congr 1
    ring
  calc
    _ = (P*(∏ i,2*M i)*C)*(T^((∑ i,a i)/2)*T^d*T) := by ring
    _ = _ := by rw [hp]

theorem d06ExtremeMomentError_uniform_power_bound {R ε : ℝ}
    (hR : 0≤R) (hε : 0<ε) (hε1 : ε≤1/4)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i,Continuous (ρ i)) (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : Fin 2 → ℂ,(∀ i,‖σ i‖≤R) →
        ‖d06ExtremeMomentError T σ ρ Φ‖≤C*T^(1/2+2*ε+(∑ i,a i)/2) := by
  obtain ⟨K,hK,hpoint⟩ := d04ActualPair_oneSided_uniform_error hR hε hε1
  have hm : ∀ i : Fin 4,∃ M : ℝ,0≤M ∧ ∀ x,|ρ i x|≤M :=
    fun i => d02Continuous_supported_norm_bound (hρ i) (hρs i)
  choose M hM hρM using hm
  obtain ⟨P,hP,hΦP⟩ := d02Continuous_supported_norm_bound hΦ hΦs
  have hcap : ∀ i x,a i<x → ρ i x=0 := by
    intro i x hx
    by_contra hn
    exact (not_le_of_gt hx) (hρs i (subset_tsupport (ρ i) hn)).2
  have hcut : ∀ x,x∉Icc (1:ℝ) 2 → Φ x=0 := by
    intro x hx
    by_contra hn
    exact hx (hΦs (subset_tsupport Φ hn))
  refine ⟨P*(∏ i,2*M i)*K,mul_nonneg
    (mul_nonneg hP (Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (hM i))) hK,?_⟩
  filter_upwards [hpoint,eventually_gt_atTop (1:ℝ)] with T hpointT hT
  intro σ hσ
  have hb := d06AllPositiveMoment_uniform_window_error_bound
    (d:=-1/2+2*ε) hT hP a M hM ρ hρM hcap Φ hΦP hcut
    (fun t => (criticalChi t)⁻¹*(d04ActualUnbalancedPair T t σ-
      d04CenteringPurePower T t (σ 0)*d04OneSidedCenteredPair T t σ))
    (fun t ht => by
      rw [norm_mul,norm_inv,criticalChi_norm,inv_one,one_mul]
      exact hpointT t ht σ hσ)
  simpa only [d06ExtremeMomentError,d04ActualUnbalancedPair,mul_assoc,
    show (-1/2+2*ε)+1+(∑ i,a i)/2=1/2+2*ε+(∑ i,a i)/2 by ring] using hb

theorem d06ExtremeMomentError_normalized_uniform_small
    (a : Fin 4 → ℝ) (ha : ∀ i,0<a i) (haS : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {R η : ℝ} (hR : 0≤R) (hη : 0<η) :
    ∀ᶠ T : ℝ in atTop,∀ σ : Fin 2 → ℂ,(∀ i,‖σ i‖≤R) →
      ‖d06ExtremeMomentError T σ ρ Φ/(T*(Real.log T)^9 : ℂ)‖<η := by
  let ε : ℝ := (1-(∑ i,a i))/8
  have hε : 0<ε := by dsimp [ε]; linarith
  have hS0 : 0≤∑ i,a i := Finset.sum_nonneg (fun i _ => (ha i).le)
  have hε1 : ε≤1/4 := by dsimp [ε]; linarith
  obtain ⟨C,_hC,hbound⟩ := d06ExtremeMomentError_uniform_power_bound
    hR hε hε1 a ρ hρ hρs Φ hΦ hΦs
  exact d02PowerHeight_normalized_uniform_small
    (fun T σ => d06ExtremeMomentError T σ ρ Φ) (fun σ => ∀ i,‖σ i‖≤R)
    (by dsimp [ε]; linarith : 1/2+2*ε+(∑ i,a i)/2<1) hbound hη

theorem d06ExtremeMomentError_normalized_tendsto
    (a : Fin 4 → ℝ) (ha : ∀ i,0<a i) (haS : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (σ : Fin 2 → ℂ) :
    Tendsto (fun T : ℝ => d06ExtremeMomentError T σ ρ Φ/
      (T*(Real.log T)^9 : ℂ)) atTop (𝓝 0) := by
  let R : ℝ := ‖σ 0‖+‖σ 1‖
  have hR : 0≤R := by dsimp [R]; positivity
  have hσ : ∀ i,‖σ i‖≤R := by
    intro i
    fin_cases i <;> dsimp [R] <;> linarith [norm_nonneg (σ 0),norm_nonneg (σ 1)]
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [d06ExtremeMomentError_normalized_uniform_small
    a ha haS ρ hρ hρs Φ hΦ hΦs hR hη] with T hT
  simpa only [dist_eq_norm,sub_zero] using hT σ hσ

end
end Sechstmoment
