import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import SixthMoment.Denominator.Balanced.ZetaGaussianMomentError

namespace SixthMoment
open Complex Real Source MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section

theorem d02Measurable_cpow_const {f : ℝ → ℂ} (hf : Measurable f) (τ : ℂ) :
    Measurable (fun t => (f t)^τ) := by
  classical
  simp_rw [Complex.cpow_def]
  exact Measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const
    (Complex.measurable_exp.comp ((Complex.measurable_log.comp hf).mul_const τ))

theorem d02ActualPairCoefficient_time_continuous (α : SecondMomentShifts) (n : ℕ × ℕ) :
    Continuous (fun t : ℝ => d02ActualPairCoefficient
      (secondSourceZetaPoints t 0+α 0) (secondSourceZetaPoints t 1+α 1) n) := by
  have hm : (n.1+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero n.1
  have hn : (n.2+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero n.2
  unfold d02ActualPairCoefficient
  apply continuous_const.div
  · apply Continuous.mul
    · apply Continuous.const_cpow _ (Or.inl hm)
      unfold secondSourceZetaPoints criticalLinePoint
      simp only [Matrix.cons_val_zero]
      fun_prop
    · apply Continuous.const_cpow _ (Or.inl hn)
      unfold secondSourceZetaPoints criticalLinePoint
      simp only [Matrix.cons_val_one]
      fun_prop
  · exact fun t => mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hm))
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hn))

theorem d02ActualGaussianSummand_time_measurable (α : SecondMomentShifts) (n : ℕ × ℕ) :
    Measurable (fun t : ℝ => d02ActualGaussianSummand
      (secondSourceZetaPoints t 0+α 0) (secondSourceZetaPoints t 1+α 1) t n) := by
  unfold d02ActualGaussianSummand d02GaussianV0
  apply (d02ActualPairCoefficient_time_continuous α n).measurable.mul
  apply Complex.measurable_ofReal.comp
  apply d02GaussianTail_antitone.measurable.comp
  exact (Real.measurable_log.comp (measurable_const.div measurable_id)).div_const 2

theorem d02ActualGaussianPair_time_measurable (α : SecondMomentShifts) :
    Measurable (fun t : ℝ => d02ActualGaussianPair t α) :=
  Measurable.tsum (d02ActualGaussianSummand_time_measurable α)

theorem d02ProfileDirichletSum_time_measurable (T : ℝ) (ρ : ℝ → ℝ) (j : Fin 2) :
    Measurable (fun t : ℝ => profileDirichletSum T ρ (secondSourceZetaPoints t j)) := by
  unfold profileDirichletSum
  apply Measurable.tsum
  intro n
  have hn : (n+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero n
  apply measurable_const.div
  apply Continuous.measurable
  apply Continuous.const_cpow _ (Or.inl hn)
  fin_cases j
  · unfold secondSourceZetaPoints criticalLinePoint
    fun_prop
  · unfold secondSourceZetaPoints criticalLinePoint
    fun_prop

theorem d02BalancedAmplifier_time_measurable (T : ℝ) (ρ : Fin 4 → ℝ → ℝ) :
    Measurable (fun t : ℝ => d02BalancedAmplifier T t ρ) := by
  exact (((d02ProfileDirichletSum_time_measurable T (ρ 0) 0).mul
    (d02ProfileDirichletSum_time_measurable T (ρ 1) 0)).mul
    (d02ProfileDirichletSum_time_measurable T (ρ 2) 1)).mul
    (d02ProfileDirichletSum_time_measurable T (ρ 3) 1)

theorem d02Measurable_window_integrable {F : ℝ → ℂ} {u v B : ℝ}
    (hF : Measurable F) (hzero : ∀ t,t∉Icc u v → F t=0)
    (hbound : ∀ t∈Icc u v,‖F t‖≤B) : Integrable F := by
  have hi : IntegrableOn F (Icc u v) := by
    apply (integrableOn_const (C := B) measure_Icc_lt_top.ne).mono'
      hF.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hbound t ht
  convert hi.integrable_indicator measurableSet_Icc using 1
  ext t
  by_cases ht : t∈Icc u v
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht,hzero t ht]

theorem d02CenteredGaussianPair_time_measurable (T : ℝ) (σ : SecondMomentShifts) :
    Measurable (fun t : ℝ => d02CenteredGaussianPair T t σ) := by
  unfold d02CenteredGaussianPair secondDualPower
  apply measurable_const.mul
  apply (d02ActualGaussianPair_time_measurable _).add
  exact (d02Measurable_cpow_const
    (Complex.measurable_ofReal.comp (measurable_id.div_const (2*Real.pi))) _).mul
    (d02ActualGaussianPair_time_measurable _)

theorem d02GaussianPairMoment_integrable {T ε : ℝ} (hT : 1<T)
    (hε : 0<ε) (hε1 : ε≤1/4) (α : SecondMomentShifts) (hα : ∀ j,‖α j‖≤ε)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i,Continuous (ρ i)) (hs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2) (τ : ℂ) :
    Integrable (fun t : ℝ => (Φ (t/T):ℂ)*((t/T:ℝ):ℂ)^τ*
      d02BalancedAmplifier T t ρ*d02ActualGaussianPair t α) := by
  have hM : ∀ i,∃ M : ℝ,0≤M ∧ ∀ x,|ρ i x|≤M :=
    fun i => d02Continuous_supported_norm_bound (hρ i) (hs i)
  choose M hM hρM using hM
  obtain ⟨P,hP,hΦP⟩ := d02Continuous_supported_norm_bound hΦ hΦs
  obtain ⟨G,hG,hmass⟩ := d02ActualGaussianPair_uniform_norm hε hε1
  have hTp : 0<T := zero_lt_one.trans hT
  let B : ℝ := P*2^‖τ‖*((∏ i,2*M i)*T^((∑ i,a i)/2))*(G*(2*T)^(1/2+2*ε))
  let F : ℝ → ℂ := fun t => (Φ (t/T):ℂ)*((t/T:ℝ):ℂ)^τ*
    d02BalancedAmplifier T t ρ*d02ActualGaussianPair t α
  have hFm : Measurable F := by
    exact (((Complex.measurable_ofReal.comp (hΦ.measurable.comp
      (measurable_id.div_const T))).mul (d02Measurable_cpow_const
        (Complex.measurable_ofReal.comp (measurable_id.div_const T)) τ)).mul
      (d02BalancedAmplifier_time_measurable T ρ)).mul
      (d02ActualGaussianPair_time_measurable α)
  have hzero (t : ℝ) (ht : t∉Icc T (2*T)) : F t=0 := by
    have hnot : t/T∉Icc (1:ℝ) 2 := by
      intro h
      exact ht ⟨by simpa only [one_mul] using (le_div_iff₀ hTp).mp h.1,
        (div_le_iff₀ hTp).mp h.2⟩
    have hz : Φ (t/T)=0 := by
      by_contra hne
      exact hnot (hΦs (subset_tsupport Φ hne))
    simp only [F,hz,Complex.ofReal_zero,zero_mul]
  have hbound (t : ℝ) (ht : t∈Icc T (2*T)) : ‖F t‖≤B := by
    have htp : 0<t := hTp.trans_le ht.1
    have hratio : t/T∈Icc (1:ℝ) 2 :=
      ⟨(le_div_iff₀ hTp).mpr (by simpa using ht.1),(div_le_iff₀ hTp).mpr ht.2⟩
    have hpower : ‖((t/T:ℝ):ℂ)^τ‖≤2^‖τ‖ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos htp hTp)]
      exact (Real.rpow_le_rpow_of_exponent_le hratio.1
        (Complex.re_le_norm τ)).trans (Real.rpow_le_rpow (by positivity) hratio.2 (norm_nonneg τ))
    have hcap : ∀ i x,a i<x → ρ i x=0 := by
      intro i x hx
      by_contra hne
      exact (not_le_of_gt hx) (hs i (subset_tsupport (ρ i) hne)).2
    dsimp [F,B]
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have ha0 : 0≤(∏ i,2*M i)*T^((∑ i,a i)/2) := mul_nonneg
      (Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (hM i))
      (Real.rpow_nonneg hTp.le _)
    exact mul_le_mul (mul_le_mul (mul_le_mul (hΦP _) hpower (norm_nonneg _) hP)
      (d02BalancedAmplifier_norm_le hT t a M hM ρ hρM hcap) (norm_nonneg _)
      (mul_nonneg hP (by positivity)))
      ((hmass t htp α hα).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow htp.le ht.2 (by linarith : 0≤(1/2:ℝ)+2*ε)) hG))
      (norm_nonneg _) (mul_nonneg (mul_nonneg hP (by positivity)) ha0)
  exact d02Measurable_window_integrable hFm hzero hbound

theorem d02CenteredGaussianMoment_eventually_integrable {R ε : ℝ}
    (hR : 0≤R) (hε : 0<ε) (hε1 : ε≤1/4)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i,Continuous (ρ i)) (hs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2) :
    ∀ᶠ T : ℝ in atTop,∀ σ : SecondMomentShifts,(∀ j,‖σ j‖≤R) →
      Integrable (fun t : ℝ => (Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*
        d02CenteredGaussianPair T t σ) := by
  have hM : ∀ i,∃ M : ℝ,0≤M ∧ ∀ x,|ρ i x|≤M :=
    fun i => d02Continuous_supported_norm_bound (hρ i) (hs i)
  choose M hM hρM using hM
  obtain ⟨P,hP,hΦP⟩ := d02Continuous_supported_norm_bound hΦ hΦs
  obtain ⟨G,hG,hmass⟩ := d02ActualGaussianPair_uniform_norm hε hε1
  filter_upwards [d02RawSecondMomentShifts_eventually_small (R := R) hε,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (1:ℝ))] with T hsmall hT hL
  intro σ hσ
  have hTp : 0<T := zero_lt_one.trans hT
  let α := rawSecondMomentShifts T σ
  let β := d02DualSecondMomentShifts α
  have hα : ∀ j,‖α j‖≤ε := hsmall σ hσ
  have hβ : ∀ j,‖β j‖≤ε := d02DualSecondMomentShifts_norm_le hα
  let N : ℝ := G*(2*T)^(1/2+2*ε)
  have hN : 0≤N := by dsimp [N]; positivity
  have hbox : 0≤secondDualBoxConstant R := by unfold secondDualBoxConstant; positivity
  let B : ℝ := P*((∏ i,2*M i)*T^((∑ i,a i)/2))*Real.exp R*
    (N+secondDualBoxConstant R*N)
  apply d02Measurable_window_integrable (B := B)
    (((Complex.measurable_ofReal.comp (hΦ.measurable.comp
      (measurable_id.div_const T))).mul (d02BalancedAmplifier_time_measurable T ρ)).mul
      (d02CenteredGaussianPair_time_measurable T σ))
  · intro t ht
    change (Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*d02CenteredGaussianPair T t σ = 0
    have hnot : t/T∉Icc (1:ℝ) 2 := by
      intro h
      exact ht ⟨by simpa only [one_mul] using (le_div_iff₀ hTp).mp h.1,
        (div_le_iff₀ hTp).mp h.2⟩
    have hz : Φ (t/T)=0 := by
      by_contra hne
      exact hnot (hΦs (subset_tsupport Φ hne))
    simp only [hz,Complex.ofReal_zero,zero_mul]
  · intro t ht
    change ‖(Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*d02CenteredGaussianPair T t σ‖ ≤ B
    have htp : 0<t := hTp.trans_le ht.1
    have hτ : t/T∈Icc (1:ℝ) 2 :=
      ⟨(le_div_iff₀ hTp).mpr (by simpa using ht.1),(div_le_iff₀ hTp).mpr ht.2⟩
    have hp : ‖secondDualPower t α‖≤secondDualBoxConstant R := by
      have h := secondDualPower_normalized_box_norm_le hTp hR hL hτ σ hσ
      have htd : T*(t/T)=t := by field_simp [hTp.ne']
      rw [htd] at h
      exact h
    have hpair (γ : SecondMomentShifts) (hγ : ∀ j,‖γ j‖≤ε) :
        ‖d02ActualGaussianPair t γ‖≤N :=
      (hmass t htp γ hγ).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow htp.le ht.2 (by linarith : 0≤(1/2:ℝ)+2*ε)) hG)
    have hcenter : ‖d02CenteredGaussianPair T t σ‖≤
        Real.exp R*(N+secondDualBoxConstant R*N) := by
      unfold d02CenteredGaussianPair
      rw [norm_mul]
      apply mul_le_mul (d02ZetaCentering_norm_le σ hσ) _ (norm_nonneg _) (by positivity)
      exact (norm_add_le _ _).trans (add_le_add (hpair α hα) (by
        rw [norm_mul]
        exact mul_le_mul hp (hpair β hβ) (norm_nonneg _) hbox))
    have hcap : ∀ i x,a i<x → ρ i x=0 := by
      intro i x hx
      by_contra hne
      exact (not_le_of_gt hx) (hs i (subset_tsupport (ρ i) hne)).2
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ P*((∏ i,2*M i)*T^((∑ i,a i)/2))*
          (Real.exp R*(N+secondDualBoxConstant R*N)) := by
        have ha0 : 0≤(∏ i,2*M i)*T^((∑ i,a i)/2) := mul_nonneg
          (Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (hM i))
          (Real.rpow_nonneg hTp.le _)
        exact mul_le_mul (mul_le_mul (hΦP _)
          (d02BalancedAmplifier_norm_le hT t a M hM ρ hρM hcap) (norm_nonneg _) hP)
          hcenter (norm_nonneg _) (mul_nonneg hP ha0)
      _ = B := by dsimp [B]; ring

end
end SixthMoment
