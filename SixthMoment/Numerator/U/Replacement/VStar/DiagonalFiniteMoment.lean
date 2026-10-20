import SixthMoment.Numerator.U.Replacement.VStar.DiagonalBounds

namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def rectangularVStarPairArrayIntegrand (T a b : ℝ) (f g Φ : ℝ→ℝ)
    (E : ℕ→ℕ→ℝ→ℂ) (t : ℝ) : ℂ :=
  ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
    rectangularMomentPairWeight T f g Φ u w t*E u w t

theorem rectangular_VStar_pair_weight_zero_outside {T : ℝ} (hT : 0<T)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) (u w : ℕ) (t : ℝ)
    (ht : t∉Icc T (2*T)) : rectangularMomentPairWeight T f g Φ u w t=0 := by
  have hz : Φ (t/T)=0 := by
    by_contra hn
    have hs := hΦ.2 (subset_tsupport Φ hn)
    apply ht
    exact ⟨by nlinarith [(le_div_iff₀ hT).mp hs.1],by nlinarith [(div_le_iff₀ hT).mp hs.2]⟩
  simp [rectangularMomentPairWeight,hz]

theorem rectangular_VStar_pair_weight_norm_le {T F G P : ℝ}
    (hF : 0≤F) (hG : 0≤G) (hP : 0≤P) (f g Φ : ℝ→ℝ)
    (hfb : ∀ x, ‖f x‖≤F) (hgb : ∀ x, ‖g x‖≤G) (hΦb : ∀ x, ‖Φ x‖≤P)
    (u w : ℕ) (t : ℝ) : ‖rectangularMomentPairWeight T f g Φ u w t‖≤P*F*G := by
  have hden (n : ℕ) (s : ℂ) (hs : 0≤s.re) : 1≤‖(n+1:ℂ)^s‖ := by
    rw [show (n+1:ℂ)=((n+1:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<(n+1:ℝ))]
    exact Real.one_le_rpow (by norm_cast; omega) hs
  have hterm (M : ℝ) (hM : 0≤M) (p : ℝ→ℝ) (hp : ∀ x, ‖p x‖≤M)
      (n : ℕ) (s : ℂ) (hs : 0≤s.re) :
      ‖(p (Real.log (n+1:ℝ)/Real.log T):ℂ)/(n+1:ℂ)^s‖≤M := by
    rw [norm_div,Complex.norm_real]
    exact (div_le_self (norm_nonneg _) (hden n s hs)).trans (hp _)
  unfold rectangularMomentPairWeight
  rw [norm_mul,norm_mul,Complex.norm_real]
  exact mul_le_mul (mul_le_mul (hΦb _) (hterm F hF f hfb u _ (by norm_num [criticalLinePoint]))
    (norm_nonneg _) hP) (hterm G hG g hgb w _ (by norm_num [criticalLinePoint]))
      (norm_nonneg _) (mul_nonneg hP hF)

theorem rectangular_VStar_pair_array_norm_le {T F G P C e : ℝ} (hT : 0<T)
    (hF : 0≤F) (hG : 0≤G) (hP : 0≤P) (hC : 0≤C) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hfb : ∀ x, ‖f x‖≤F) (hgb : ∀ x, ‖g x‖≤G) (hΦb : ∀ x, ‖Φ x‖≤P)
    (E : ℕ→ℕ→ℝ→ℂ) (t : ℝ) (hb : ∀ u w, ‖E u w t‖≤C*T^e) :
    ‖rectangularVStarPairArrayIntegrand T a b f g Φ E t‖≤(P*F*G*C)*T^(a+b+e) := by
  have hp (u w : ℕ) : ‖rectangularMomentPairWeight T f g Φ u w t*E u w t‖≤(P*F*G)*(C*T^e) := by
    rw [norm_mul]
    exact mul_le_mul (rectangular_VStar_pair_weight_norm_le hF hG hP f g Φ hfb hgb hΦb u w t)
      (hb u w) (norm_nonneg _) (by positivity)
  unfold rectangularVStarPairArrayIntegrand
  calc
    _ ≤ ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊, (P*F*G)*(C*T^e) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro u _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun w _ => hp u w))
    _ = (⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*((P*F*G)*(C*T^e)) := by simp; ring
    _ ≤ T^a*T^b*((P*F*G)*(C*T^e)) := by
      gcongr
      · exact Nat.floor_le (Real.rpow_nonneg hT.le _)
      · exact Nat.floor_le (Real.rpow_nonneg hT.le _)
    _ = (P*F*G*C)*(T^a*T^b*T^e) := by ring
    _ = _ := by rw [←Real.rpow_add hT,←Real.rpow_add hT]

theorem rectangular_VStar_pair_array_stronglyMeasurable (T a b : ℝ) (f g Φ : ℝ→ℝ)
    (hΦ : SmoothDyadicWeight Φ) (E : ℕ→ℕ→ℝ→ℂ) (hE : ∀ u w, StronglyMeasurable (E u w)) :
    StronglyMeasurable (rectangularVStarPairArrayIntegrand T a b f g Φ E) := by
  have he : rectangularVStarPairArrayIntegrand T a b f g Φ E=
      ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        fun t : ℝ => rectangularMomentPairWeight T f g Φ u w t*E u w t := by
    funext t
    simp only [rectangularVStarPairArrayIntegrand,Finset.sum_apply]
  rw [he]
  apply Finset.stronglyMeasurable_sum
  intro u _
  apply Finset.stronglyMeasurable_sum
  intro w _
  exact (rectangular_moment_pair_weight_continuous T f g Φ hΦ u w).stronglyMeasurable.mul (hE u w)

theorem rectangular_VStar_pair_array_zero_outside {T : ℝ} (hT : 0<T) (a b : ℝ)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) (E : ℕ→ℕ→ℝ→ℂ)
    (t : ℝ) (ht : t∉Icc T (2*T)) : rectangularVStarPairArrayIntegrand T a b f g Φ E t=0 := by
  unfold rectangularVStarPairArrayIntegrand
  simp only [rectangular_VStar_pair_weight_zero_outside hT f g Φ hΦ _ _ t ht,zero_mul,Finset.sum_const_zero]

theorem rectangular_VStar_pair_array_integrable {T F G P C e : ℝ} (hT : 0<T)
    (hF : 0≤F) (hG : 0≤G) (hP : 0≤P) (hC : 0≤C) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hfb : ∀ x, ‖f x‖≤F) (hgb : ∀ x, ‖g x‖≤G)
    (hΦ : SmoothDyadicWeight Φ) (hΦb : ∀ x, ‖Φ x‖≤P)
    (E : ℕ→ℕ→ℝ→ℂ) (hE : ∀ u w, StronglyMeasurable (E u w))
    (hb : ∀ t∈Icc T (2*T), ∀ u w, ‖E u w t‖≤C*T^e) :
    Integrable (rectangularVStarPairArrayIntegrand T a b f g Φ E) := by
  have hm : AEStronglyMeasurable (rectangularVStarPairArrayIntegrand T a b f g Φ E) volume :=
    (rectangular_VStar_pair_array_stronglyMeasurable T a b f g Φ hΦ E hE).aestronglyMeasurable
  have hi : IntegrableOn (rectangularVStarPairArrayIntegrand T a b f g Φ E) (Icc T (2*T)) :=
    Measure.integrableOn_of_bounded (measure_Icc_lt_top.ne) hm
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht =>
        rectangular_VStar_pair_array_norm_le hT hF hG hP hC a b f g Φ hfb hgb hΦb E t (hb t ht))
  exact hi.integrable_of_forall_notMem_eq_zero
    (rectangular_VStar_pair_array_zero_outside hT a b f g Φ hΦ E)

theorem rectangular_VStar_pair_array_integral_norm_le {T F G P C e : ℝ} (hT : 0<T)
    (hF : 0≤F) (hG : 0≤G) (hP : 0≤P) (hC : 0≤C) (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hfb : ∀ x, ‖f x‖≤F) (hgb : ∀ x, ‖g x‖≤G)
    (hΦ : SmoothDyadicWeight Φ) (hΦb : ∀ x, ‖Φ x‖≤P)
    (E : ℕ→ℕ→ℝ→ℂ) (hb : ∀ t∈Icc T (2*T), ∀ u w, ‖E u w t‖≤C*T^e) :
    ‖∫ t : ℝ, rectangularVStarPairArrayIntegrand T a b f g Φ E t‖≤(P*F*G*C)*T^(1+a+b+e) := by
  have hset : (∫ t : ℝ, rectangularVStarPairArrayIntegrand T a b f g Φ E t)=
      ∫ t in Icc T (2*T), rectangularVStarPairArrayIntegrand T a b f g Φ E t := by
    rw [←integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t∈Icc T (2*T)
    · simp [ht]
    · simp [ht,rectangular_VStar_pair_array_zero_outside hT a b f g Φ hΦ E t ht]
  rw [hset]
  have hi := norm_setIntegral_le_of_norm_le_const
    (measure_Icc_lt_top (μ := volume) (a := T) (b := 2*T))
    (fun t ht => rectangular_VStar_pair_array_norm_le hT hF hG hP hC a b f g Φ hfb hgb hΦb E t (hb t ht))
  have hv : volume.real (Icc T (2*T))=T := by
    rw [Real.volume_real_Icc]
    simp only [show 2*T-T=T by ring,max_eq_left hT.le]
  rw [hv] at hi
  calc
    _ ≤ ((P*F*G*C)*T^(a+b+e))*T := hi
    _ = (P*F*G*C)*(T^(a+b+e)*T^(1:ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [←Real.rpow_add hT]; congr 1; ring


theorem rectangularVStarSelectedFiniteRemainderMoment_uniform_rapid
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ diagonal : Bool,
      Integrable (rectangularVStarSelectedFiniteRemainderIntegrand diagonal c T a b σ f g Φ
        (T^(2+η)) (θ*Real.log T)) ∧
      ‖rectangularVStarSelectedFiniteRemainderMoment diagonal c T a b σ f g Φ
        (T^(2+η)) (θ*Real.log T)‖≤C*T^(-M) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨P,hP,hΦb⟩ := rectangular_supported_weight_bounded Φ hΦ
  obtain ⟨C,hC,hb⟩ := bblrVStarSelectedFiniteRemainder_uniform_rapid_bound
    hc hc1 hη hθ K δ hδ hroot (1+a+b+M)
  obtain ⟨D,hD,hd⟩ := bblrDualLeadingMultiplier_uniform_normalized_bound K hK
  refine ⟨P*F*G*(C*(1+D)),by positivity,?_⟩
  filter_upwards [hb,hd,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T hb hd hsmall hT
  intro σ hσ diagonal
  let E : ℕ→ℕ→ℝ→ℂ := fun u w t =>
    bblrVStarSelectedFiniteRemainder diagonal c T σ (rawMomentShifts T σ) u w t
      (T^(2+η)) (θ*Real.log T)+
      bblrDualLeadingMultiplier T σ (t/T)*
        bblrVStarSelectedFiniteRemainder diagonal c T σ (bblrSixShifts (rawMomentShifts T σ) 1) u w t
          (T^(2+η)) (θ*Real.log T)
  have hα := hsmall σ hσ
  have hE : ∀ u w, StronglyMeasurable (E u w) := by
    intro u w
    exact (bblrVStarSelectedFiniteRemainder_time_stronglyMeasurable hc diagonal T σ _ hα u w _ _).add
      ((bblrDualLeadingMultiplier_time_measurable T σ).stronglyMeasurable.mul
        (bblrVStarSelectedFiniteRemainder_time_stronglyMeasurable hc diagonal T σ _
          (bblrSixShifts_norm_le _ hα 1) u w _ _))
  have hbound : ∀ t∈Icc T (2*T), ∀ u w, ‖E u w t‖≤(C*(1+D))*T^(-(1+a+b+M)) := by
    intro t ht u w
    dsimp [E]
    calc
      _≤‖bblrVStarSelectedFiniteRemainder diagonal c T σ (rawMomentShifts T σ) u w t
          (T^(2+η)) (θ*Real.log T)‖+
        ‖bblrDualLeadingMultiplier T σ (t/T)*
          bblrVStarSelectedFiniteRemainder diagonal c T σ (bblrSixShifts (rawMomentShifts T σ) 1) u w t
            (T^(2+η)) (θ*Real.log T)‖ := norm_add_le _ _
      _≤C*T^(-(1+a+b+M))+D*(C*T^(-(1+a+b+M))) := by
        rw [norm_mul]
        gcongr
        · exact hb σ hσ _ hα t ht diagonal u w
        · exact hd σ hσ t ht
        · exact hb σ hσ _ (bblrSixShifts_norm_le _ hα 1) t ht diagonal u w
      _=_ := by ring
  have hCD : 0≤C*(1+D) := by positivity
  refine ⟨rectangular_VStar_pair_array_integrable (zero_lt_one.trans hT) hF hG hP hCD
    a b f g Φ hfb hgb hΦ hΦb E hE hbound,?_⟩
  have he := rectangular_VStar_pair_array_integral_norm_le (zero_lt_one.trans hT) hF hG hP hCD
    a b f g Φ hfb hgb hΦ hΦb E hbound
  convert he using 1
  congr 1
  ring

theorem rectangularVStarSelectedMoment_uniform_finite_small_error
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ diagonal : Bool,
      Integrable (rectangularVStarSelectedCombinedIntegrand diagonal T a b σ f g Φ) ∧
      Integrable (rectangularVStarSelectedFiniteIntegrand diagonal c T a b σ f g Φ
        (T^(2+η)) (θ*Real.log T)) ∧
      Integrable (rectangularVStarSelectedFiniteRemainderIntegrand diagonal c T a b σ f g Φ
        (T^(2+η)) (θ*Real.log T)) ∧
      ‖rectangularVStarSelectedMoment diagonal T a b σ f g Φ-
        rectangularVStarSelectedFiniteMoment diagonal c T a b σ f g Φ
          (T^(2+η)) (θ*Real.log T)‖≤C*T^(-M) := by
  obtain ⟨C,hC,hb⟩ := rectangularVStarSelectedFiniteRemainderMoment_uniform_rapid
    hc hc1 hη hθ K hK δ hδ hroot a b f g Φ hf hg hΦ M
  have hsel := rectangularVStarAFEMoment_eventually_eq_diagonal_and_offdiagonal
    K hK δ hδ hroot a b f g Φ hf hg hΦ
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,hsel,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num)] with T hb hsel hsmall
  intro σ hσ diagonal
  have hi : Integrable (rectangularVStarSelectedCombinedIntegrand diagonal T a b σ f g Φ) := by
    cases diagonal
    · exact (hsel σ hσ).2.1
    · exact (hsel σ hσ).1
  have hrem := (hb σ hσ diagonal).1
  have he : rectangularVStarSelectedFiniteIntegrand diagonal c T a b σ f g Φ (T^(2+η)) (θ*Real.log T)=
      (fun t : ℝ => rectangularVStarSelectedCombinedIntegrand diagonal T a b σ f g Φ t)-
        (fun t : ℝ => rectangularVStarSelectedFiniteRemainderIntegrand diagonal c T a b σ f g Φ
          (T^(2+η)) (θ*Real.log T) t) := by
    funext t
    have h := rectangularVStarSelectedCombinedIntegrand_eq_finite_grid diagonal c T a b σ
      (hsmall σ hσ) f g Φ (T^(2+η)) (θ*Real.log T) t
    simp only [Pi.sub_apply]
    linear_combination -h
  refine ⟨hi,by rw [he]; exact hi.sub hrem,hrem,?_⟩
  have hm : rectangularVStarSelectedFiniteMoment diagonal c T a b σ f g Φ (T^(2+η)) (θ*Real.log T)=
      rectangularVStarSelectedMoment diagonal T a b σ f g Φ-
        rectangularVStarSelectedFiniteRemainderMoment diagonal c T a b σ f g Φ (T^(2+η)) (θ*Real.log T) := by
    unfold rectangularVStarSelectedFiniteMoment
    rw [he]
    simp only [Pi.sub_apply]
    rw [integral_sub hi hrem]
    rfl
  rw [hm,sub_sub_cancel]
  exact (hb σ hσ diagonal).2


theorem rectangularVStarAFEMoment_uniform_diagonal_finite_offdiagonal_error
    {c η θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hη : 0<η) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0<δ)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) (M : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ∈K,
      Integrable (rectangularVStarSelectedFiniteIntegrand false c T a b σ f g Φ
        (T^(2+η)) (θ*Real.log T)) ∧
      ‖rectangularVStarAFEMoment T σ f g Φ-
        (bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
          bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
            rectangularVStarSelectedFiniteMoment false c T a b σ f g Φ
              (T^(2+η)) (θ*Real.log T))‖≤C*T^(-M) := by
  obtain ⟨C,hC,hsmall⟩ := rectangularVStarSelectedMoment_uniform_finite_small_error
    hc hc1 hη hθ K hK δ hδ hroot a b f g Φ hf hg hΦ M
  have hdiag := rectangularVStarAFEMoment_eventually_eq_diagonal_and_offdiagonal
    K hK δ hδ hroot a b f g Φ hf hg hΦ
  refine ⟨C,hC,?_⟩
  filter_upwards [hsmall,hdiag] with T hsmall hdiag
  intro σ hσ
  have he := hsmall σ hσ false
  refine ⟨he.2.1,?_⟩
  rw [(hdiag σ hσ).2.2]
  convert he.2.2.2 using 1
  congr 1
  ring

end
end SixthMoment
