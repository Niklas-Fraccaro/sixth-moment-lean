import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Sechstmoment.Denominator.Balanced.MomentErrorBudget
import Sechstmoment.Denominator.Unbalanced.MomentDefinitions

namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section

theorem d04UnbalancedAmplifier_norm_le {T : ℝ} (hT : 1 < T) (t : ℝ)
    (a M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i x, |ρ i x| ≤ M i) (hcap : ∀ i x, a i < x → ρ i x = 0) :
    ‖d04UnbalancedAmplifier T t ρ‖ ≤ (∏ i, 2*M i)*T^((∑ i, a i)/2) := by
  have hb (i : Fin 4) (s : ℂ) (hs : s.re=1/2) :=
    d02_profileDirichletSum_norm_le hT (hM i) (ρ i) (hρ i) (hcap i) s hs
  have hup : (criticalLinePoint t).re=1/2 := by simp [criticalLinePoint]
  have hlo : (1-criticalLinePoint t).re=1/2 := by simp [criticalLinePoint]; norm_num
  unfold d04UnbalancedAmplifier
  simp only [norm_mul]
  calc
    _ ≤ (2*M 0*T^(a 0/2))*(2*M 1*T^(a 1/2))*
        (2*M 2*T^(a 2/2))*(2*M 3*T^(a 3/2)) := by
      have hB (i : Fin 4) : 0≤2*M i*T^(a i/2) :=
        mul_nonneg (mul_nonneg (by norm_num) (hM i))
          (Real.rpow_nonneg (zero_lt_one.trans hT).le _)
      exact mul_le_mul
        (mul_le_mul (mul_le_mul (hb 0 _ hup) (hb 1 _ hup)
          (norm_nonneg _) (hB 0)) (hb 2 _ hup) (norm_nonneg _)
          (mul_nonneg (hB 0) (hB 1))) (hb 3 _ hlo) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (hB 0) (hB 1)) (hB 2))
    _ = _ := by
      simp only [Fin.prod_univ_four, Fin.sum_univ_four]
      have hTp : 0<T := zero_lt_one.trans hT
      rw [show (a 0+a 1+a 2+a 3)/2 = a 0/2+a 1/2+a 2/2+a 3/2 by ring]
      simp only [Real.rpow_add hTp]
      ring

theorem d04UnbalancedMoment_pointwise_error_bound {T c C P : ℝ}
    (hT : 1<T) (hc : c≤1) (hC : 0≤C) (hP : 0≤P)
    (a M : Fin 4 → ℝ) (hM : ∀ i, 0≤M i)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i x, |ρ i x|≤M i)
    (hcap : ∀ i x, a i<x → ρ i x=0)
    (Φ : ℝ → ℝ) (hΦ : ∀ x, |Φ x|≤P)
    (hΦs : ∀ x, x∉Icc 1 2 → Φ x=0)
    (E : ℝ → ℂ) (hE : ∀ t∈Icc T (2*T), ‖E t‖≤C*t^(c-1)) :
    ‖∫ t : ℝ, (Φ (t/T):ℂ)*d04UnbalancedAmplifier T t ρ*E t‖ ≤
      (P*(∏ i, 2*M i)*C)*T^(c+(∑ i, a i)/2) := by
  have hTp : 0<T := zero_lt_one.trans hT
  have hsupp : (∫ t : ℝ, (Φ (t/T):ℂ)*d04UnbalancedAmplifier T t ρ*E t) =
      ∫ t in Icc T (2*T), (Φ (t/T):ℂ)*d04UnbalancedAmplifier T t ρ*E t := by
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
      ‖(Φ (t/T):ℂ)*d04UnbalancedAmplifier T t ρ*E t‖ ≤
        P*((∏ i,2*M i)*T^((∑ i,a i)/2))*(C*T^(c-1)) := by
    rw [norm_mul, norm_mul, Complex.norm_real,Real.norm_eq_abs]
    have ha0 : 0≤(∏ i,2*M i)*T^((∑ i,a i)/2) := mul_nonneg
      (Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (hM i))
      (Real.rpow_nonneg hTp.le _)
    exact mul_le_mul
      (mul_le_mul (hΦ _) (d04UnbalancedAmplifier_norm_le hT t a M hM ρ hρ hcap)
        (norm_nonneg _) hP)
      ((hE t ht).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hTp ht.1 (by linarith)) hC))
      (norm_nonneg _) (mul_nonneg hP ha0)
  apply (norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top hb).trans_eq
  rw [Real.volume_real_Icc, max_eq_left (by linarith)]
  have hp : T^((∑ i,a i)/2)*T^(c-1)*T = T^(c+(∑ i,a i)/2) := by
    conv_lhs => arg 2; rw [← Real.rpow_one T]
    rw [← Real.rpow_add hTp, ← Real.rpow_add hTp]
    congr 1
    ring
  calc
    _ = (P*(∏ i,2*M i)*C)*(T^((∑ i,a i)/2)*T^(c-1)*T) := by ring
    _ = _ := by rw [hp]

theorem d04UnbalancedMoment_uniform_window_error_bound {T d C P : ℝ}
    (hT : 1<T) (hP : 0≤P)
    (a M : Fin 4 → ℝ) (hM : ∀ i, 0≤M i)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i x, |ρ i x|≤M i)
    (hcap : ∀ i x, a i<x → ρ i x=0)
    (Φ : ℝ → ℝ) (hΦ : ∀ x, |Φ x|≤P)
    (hΦs : ∀ x, x∉Icc 1 2 → Φ x=0)
    (E : ℝ → ℂ) (hE : ∀ t∈Icc T (2*T), ‖E t‖≤C*T^d) :
    ‖∫ t : ℝ, (Φ (t/T):ℂ)*d04UnbalancedAmplifier T t ρ*E t‖ ≤
      (P*(∏ i, 2*M i)*C)*T^(d+1+(∑ i, a i)/2) := by
  have hTp : 0<T := zero_lt_one.trans hT
  have hsupp : (∫ t : ℝ, (Φ (t/T):ℂ)*d04UnbalancedAmplifier T t ρ*E t) =
      ∫ t in Icc T (2*T), (Φ (t/T):ℂ)*d04UnbalancedAmplifier T t ρ*E t := by
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
      ‖(Φ (t/T):ℂ)*d04UnbalancedAmplifier T t ρ*E t‖ ≤
        P*((∏ i,2*M i)*T^((∑ i,a i)/2))*(C*T^d) := by
    rw [norm_mul, norm_mul, Complex.norm_real,Real.norm_eq_abs]
    have ha0 : 0≤(∏ i,2*M i)*T^((∑ i,a i)/2) := mul_nonneg
      (Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (hM i))
      (Real.rpow_nonneg hTp.le _)
    exact mul_le_mul
      (mul_le_mul (hΦ _) (d04UnbalancedAmplifier_norm_le hT t a M hM ρ hρ hcap)
        (norm_nonneg _) hP)
      (hE t ht)
      (norm_nonneg _) (mul_nonneg hP ha0)
  apply (norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top hb).trans_eq
  rw [Real.volume_real_Icc, max_eq_left (by linarith)]
  have hp : T^((∑ i,a i)/2)*T^d*T = T^(d+1+(∑ i,a i)/2) := by
    conv_lhs => arg 2; rw [← Real.rpow_one T]
    rw [← Real.rpow_add hTp, ← Real.rpow_add hTp]
    congr 1
    ring
  calc
    _ = (P*(∏ i,2*M i)*C)*(T^((∑ i,a i)/2)*T^d*T) := by ring
    _ = _ := by rw [hp]

end
end Sechstmoment
