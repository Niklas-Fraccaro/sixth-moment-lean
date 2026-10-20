import Sechstmoment.Numerator.U.Reconstruction.RectangularActualMoment
import Sechstmoment.Numerator.U.Reconstruction.RectangularConcreteAFEError
import Sechstmoment.Numerator.U.Separation.LogarithmicGaussianTail
import Sechstmoment.Zeta.AFE.Four.DualBound
import Sechstmoment.Zeta.Moments.AnalyticMomentLinearity


namespace Sechstmoment
open Complex Source MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
noncomputable section

def rectangularMomentWeight (T : ℝ) (f g Φ : ℝ → ℝ) (t : ℝ) : ℂ :=
  (Φ (t/T) : ℂ)*profileDirichletSum T f (criticalLinePoint t)*
    profileDirichletSum T g (1-criticalLinePoint t)

def rectangularAmplifiedError (T : ℝ) (f g Φ : ℝ → ℝ) (E : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, rectangularMomentWeight T f g Φ t*E t

theorem rectangular_moment_weight_continuous {T : ℝ} (hT : 1 < T) (a b : ℝ)
    (f g Φ : ℝ → ℝ) (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0)
    (hΦ : SmoothDyadicWeight Φ) : Continuous (rectangularMomentWeight T f g Φ) := by
  have hs : Continuous (fun t : ℝ => criticalLinePoint t) := by fun_prop [criticalLinePoint]
  have hs' : Continuous (fun t : ℝ => 1-criticalLinePoint t) := by fun_prop [criticalLinePoint]
  exact ((Complex.continuous_ofReal.comp (hΦ.1.continuous.comp (by fun_prop))).mul
    ((profileDirichletSum_continuous hT a f hf).comp hs)).mul
    ((profileDirichletSum_continuous hT b g hg).comp hs')

theorem rectangular_moment_weight_compact {T : ℝ} (hT : T ≠ 0)
    (f g Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    HasCompactSupport (rectangularMomentWeight T f g Φ) :=
  ((rectangular_scaled_weight_hasCompactSupport hT Φ hΦ).mul_right).mul_right

theorem rectangular_moment_weight_zero_outside {T : ℝ} (hT : 0 < T)
    (f g Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (t : ℝ) (ht : t ∉ Icc T (2*T)) :
    rectangularMomentWeight T f g Φ t=0 := by
  have hz : Φ (t/T)=0 := by
    by_contra hn
    have hs : t/T ∈ tsupport Φ :=
      subset_tsupport Φ (by simpa only [Function.mem_support] using hn)
    obtain ⟨hl,hu⟩ := hΦ.2 hs
    apply ht
    exact ⟨by nlinarith [(le_div_iff₀ hT).mp hl],
      by nlinarith [(div_le_iff₀ hT).mp hu]⟩
  simp [rectangularMomentWeight,hz]

theorem rectangular_moment_weight_norm_le {T F Gc P : ℝ} (hT : 1 < T)
    (hF : 0 ≤ F) (hGc : 0 ≤ Gc) (hP : 0 ≤ P) (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0)
    (hfb : ∀ x, ‖f x‖ ≤ F) (hgb : ∀ x, ‖g x‖ ≤ Gc)
    (hΦb : ∀ x, ‖Φ x‖ ≤ P) (t : ℝ) :
    ‖rectangularMomentWeight T f g Φ t‖ ≤ (P*F*Gc)*T^(a+b) := by
  have hft := rectangular_profileDirichletSum_norm_le hT hF a f hf hfb
    (criticalLinePoint t) (by norm_num [criticalLinePoint])
  have hgt := rectangular_profileDirichletSum_norm_le hT hGc b g hg hgb
    (1-criticalLinePoint t) (by norm_num [criticalLinePoint])
  unfold rectangularMomentWeight
  rw [norm_mul,norm_mul,Complex.norm_real]
  calc
    _ ≤ P*(F*T^a)*(Gc*T^b) := by gcongr; exact hΦb (t/T)
    _ = (P*F*Gc)*(T^a*T^b) := by ring
    _ = _ := by rw [← Real.rpow_add (zero_lt_one.trans hT)]

theorem rectangular_amplified_error_integrable {T F Gc P C e : ℝ} (hT : 1 < T)
    (hF : 0 ≤ F) (hGc : 0 ≤ Gc) (hP : 0 ≤ P) (_hC : 0 ≤ C)
    (a b : ℝ) (f g Φ : ℝ → ℝ) (E : ℝ → ℂ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0)
    (hfb : ∀ x, ‖f x‖ ≤ F) (hgb : ∀ x, ‖g x‖ ≤ Gc)
    (hΦ : SmoothDyadicWeight Φ) (hΦb : ∀ x, ‖Φ x‖ ≤ P)
    (hE : StronglyMeasurable E) (hb : ∀ t ∈ Icc T (2*T), ‖E t‖ ≤ C*T^e) :
    Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*E t) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => rectangularMomentWeight T f g Φ t*E t) volume :=
    ((rectangular_moment_weight_continuous hT a b f g Φ hf hg hΦ).stronglyMeasurable.mul
    hE).aestronglyMeasurable
  have hbound : ∀ t ∈ Icc T (2*T), ‖rectangularMomentWeight T f g Φ t*E t‖ ≤
      ((P*F*Gc)*T^(a+b))*(C*T^e) := by
    intro t ht
    rw [norm_mul]
    exact mul_le_mul (rectangular_moment_weight_norm_le hT hF hGc hP a b f g Φ
      hf hg hfb hgb hΦb t) (hb t ht) (norm_nonneg _) (by positivity)
  have hi : IntegrableOn (fun t : ℝ => rectangularMomentWeight T f g Φ t*E t)
      (Icc T (2*T)) :=
    Measure.integrableOn_of_bounded (measure_Icc_lt_top.ne) hm
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht => hbound t ht)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro t ht
  simp [rectangular_moment_weight_zero_outside (zero_lt_one.trans hT) f g Φ hΦ t ht]

theorem rectangular_amplified_error_norm_le {T F Gc P C e : ℝ} (hT : 1 < T)
    (hF : 0 ≤ F) (hGc : 0 ≤ Gc) (hP : 0 ≤ P) (_hC : 0 ≤ C)
    (a b : ℝ) (f g Φ : ℝ → ℝ) (E : ℝ → ℂ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0)
    (hfb : ∀ x, ‖f x‖ ≤ F) (hgb : ∀ x, ‖g x‖ ≤ Gc)
    (hΦ : SmoothDyadicWeight Φ) (hΦb : ∀ x, ‖Φ x‖ ≤ P)
    (hb : ∀ t ∈ Icc T (2*T), ‖E t‖ ≤ C*T^e) :
    ‖rectangularAmplifiedError T f g Φ E‖ ≤ (P*F*Gc*C)*T^(1+a+b+e) := by
  have ht : 0 < T := zero_lt_one.trans hT
  have hset : rectangularAmplifiedError T f g Φ E =
      ∫ t in Icc T (2*T), rectangularMomentWeight T f g Φ t*E t := by
    unfold rectangularAmplifiedError
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases hm : t ∈ Icc T (2*T)
    · simp [hm]
    · simp [hm,rectangular_moment_weight_zero_outside ht f g Φ hΦ t hm]
  rw [hset]
  have hb' : ∀ t ∈ Icc T (2*T), ‖rectangularMomentWeight T f g Φ t*E t‖ ≤
      (P*F*Gc*C)*T^(a+b+e) := by
    intro t ht'
    rw [norm_mul]
    calc
      _ ≤ ((P*F*Gc)*T^(a+b))*(C*T^e) :=
        mul_le_mul (rectangular_moment_weight_norm_le hT hF hGc hP a b f g Φ
          hf hg hfb hgb hΦb t) (hb t ht') (norm_nonneg _) (by positivity)
      _ = (P*F*Gc*C)*(T^(a+b)*T^e) := by ring
      _ = _ := by rw [← Real.rpow_add ht]
  have hi := norm_setIntegral_le_of_norm_le_const
    (measure_Icc_lt_top (μ := volume) (a := T) (b := 2*T)) hb'
  have hv : volume.real (Icc T (2*T))=T := by
    rw [Real.volume_real_Icc]
    simp only [show 2*T-T=T by ring,max_eq_left ht.le]
  rw [hv] at hi
  calc
    _ ≤ ((P*F*Gc*C)*T^(a+b+e))*T := hi
    _ = (P*F*Gc*C)*(T^(a+b+e)*T^(1 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add ht]; congr 1; ring

theorem rectangular_AFE_integrated_error_eq_amplified (T : ℝ) (α : MomentShifts)
    (G : ℂ → ℂ) (f g Φ : ℝ → ℝ) :
    rectangularAFEIntegratedError T α G f g Φ =
      rectangularAmplifiedError T f g Φ (bblrAFEDiscrepancy G α) := by
  unfold rectangularAFEIntegratedError rectangularAmplifiedError
  apply integral_congr_ae
  filter_upwards [] with t
  unfold rectangularAFEErrorIntegrand rectangularMomentWeight
  ring

theorem bblrGaussianVTail_time_stronglyMeasurable (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, -1/2 < (α j).re) (x R : ℝ) (hx : 0 < x) :
    StronglyMeasurable (fun t : ℝ => bblrGaussianVTail T σ α x t R) := by
  have hm := (rectangular_vertical_joint_continuous (polarPoleKiller T σ)
    (polarPoleKiller_differentiable T σ).continuous α hα x hx).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := volume.restrict {v : ℝ | R < |v|})).const_mul
    (1/(2*Real.pi) : ℂ)

theorem bblrGaussianAFETail_time_stronglyMeasurable (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, -1/2 < (α j).re) (R : ℝ) :
    StronglyMeasurable (fun t : ℝ => bblrGaussianAFETail T σ α t R) := by
  apply StronglyMeasurable.tsum
  intro n
  have hc : Continuous (fun t : ℝ => rectangularAFEOscillation t n) := by
    unfold rectangularAFEOscillation
    apply Continuous.const_cpow
    · fun_prop
    · apply Or.inl
      have h₁ : (((n 0+1)*(n 1+1) : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 0)) (Nat.succ_ne_zero (n 1))
      have h₂ : (((n 2+1)*(n 3+1) : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 2)) (Nat.succ_ne_zero (n 3))
      exact div_ne_zero h₁ h₂
  have hm := bblrGaussianVTail_time_stronglyMeasurable T σ α hα (positiveQuadProduct n)
    R (by unfold positiveQuadProduct; positivity)
  simpa only [bblrGaussianAFETailSummand,rectangularAFEOscillation,div_eq_mul_inv,
    Pi.mul_apply] using (hc.stronglyMeasurable.mul hm).mul_const
      (∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j))⁻¹

def rectangularGaussianCombinedTail (T : ℝ) (σ : MomentShifts) (R t : ℝ) : ℂ :=
  bblrGaussianAFETail T σ (rawMomentShifts T σ) t R+
    bblrDualMultiplier t (rawMomentShifts T σ)*
      bblrGaussianAFETail T σ (bblrSixShifts (rawMomentShifts T σ) 1) t R

def rectangularGaussianTailMoment (T : ℝ) (σ : MomentShifts) (f g Φ : ℝ → ℝ)
    (R : ℝ) : ℂ := rectangularAmplifiedError T f g Φ (rectangularGaussianCombinedTail T σ R)

theorem rectangularGaussianCombinedTail_stronglyMeasurable (T : ℝ) (σ : MomentShifts)
    (hα : ∀ j, ‖rawMomentShifts T σ j‖ ≤ 1/4) (R : ℝ) :
    StronglyMeasurable (rectangularGaussianCombinedTail T σ R) := by
  have hr : ∀ j, |(rawMomentShifts T σ j).re| < 1/2 := fun j =>
    ((Complex.abs_re_le_norm _).trans (hα j)).trans_lt (by norm_num)
  have hs : ∀ j, -1/2 < (rawMomentShifts T σ j).re := by
    intro j
    simpa only [neg_div] using (abs_lt.mp (hr j)).1
  have hd := rectangular_dual_shifts_strip (rawMomentShifts T σ) hr
  exact (bblrGaussianAFETail_time_stronglyMeasurable T σ _ hs R).add
    ((rectangular_dual_multiplier_continuous _ hr).stronglyMeasurable.mul
      (bblrGaussianAFETail_time_stronglyMeasurable T σ _ hd R))

theorem rectangularGaussianCombinedTail_uniform_logarithmic_bound
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0 < θ) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ t ∈ Icc T (2*T),
      ‖rectangularGaussianCombinedTail T σ (θ*Real.log T) t‖ ≤ C*T^(-(A : ℝ)) := by
  obtain ⟨C,hC,hb⟩ :=
    bblrGaussianAFETail_uniform_logarithmic_six_shifts_bound K hK δ hδ hρ hθ A
  obtain ⟨D,hD,hd⟩ := bblrDualMultiplier_uniform_normalized_bound K hK
  refine ⟨C*(1+D),by positivity,?_⟩
  filter_upwards [hb,hd,eventually_gt_atTop (0 : ℝ)] with T hb hd hT
  intro σ hσ t ht
  unfold rectangularGaussianCombinedTail
  calc
    _ ≤ ‖bblrGaussianAFETail T σ (rawMomentShifts T σ) t (θ*Real.log T)‖+
        ‖bblrDualMultiplier t (rawMomentShifts T σ)*
          bblrGaussianAFETail T σ (bblrSixShifts (rawMomentShifts T σ) 1)
            t (θ*Real.log T)‖ := norm_add_le _ _
    _ ≤ C*T^(-(A : ℝ))+D*(C*T^(-(A : ℝ))) := by
      rw [norm_mul]
      gcongr
      · simpa only [bblrSixShifts,Matrix.cons_val_zero] using hb σ hσ 0 t ht
      · exact hd σ hσ t ht
      · exact hb σ hσ 1 t ht
    _ = _ := by ring

theorem rectangularGaussianTailMoment_uniform_logarithmic_bound
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0 < θ) (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      Integrable (fun t : ℝ => rectangularMomentWeight T f g Φ t*
        rectangularGaussianCombinedTail T σ (θ*Real.log T) t) ∧
      ‖rectangularGaussianTailMoment T σ f g Φ (θ*Real.log T)‖ ≤ C*T^(1+a+b-(A : ℝ)) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨Gc,hGc,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨P,hP,hΦb⟩ := rectangular_supported_weight_bounded Φ hΦ
  obtain ⟨C,hC,hb⟩ := rectangularGaussianCombinedTail_uniform_logarithmic_bound
    K hK δ hδ hρ hθ A
  have hfs := rectangular_supported_profile_zero_above f hf
  have hgs := rectangular_supported_profile_zero_above g hg
  refine ⟨P*F*Gc*C,by positivity,?_⟩
  filter_upwards [hb,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1 : ℝ)] with T hb hs hT
  intro σ hσ
  constructor
  · exact rectangular_amplified_error_integrable hT hF hGc hP hC a b f g Φ
      _ hfs hgs hfb hgb hΦ hΦb
      (rectangularGaussianCombinedTail_stronglyMeasurable T σ (hs σ hσ) _)
      (hb σ hσ)
  · exact rectangular_amplified_error_norm_le hT hF hGc hP hC a b f g Φ
      _ hfs hgs hfb hgb hΦ hΦb (hb σ hσ)

theorem rectangularGaussianTailMoment_uniform_rapid_decay
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0 < θ) (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (N : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      ‖rectangularGaussianTailMoment T σ f g Φ (θ*Real.log T)‖ ≤ C*T^(-N) := by
  obtain ⟨A,hA⟩ := exists_nat_gt (1+a+b+N)
  obtain ⟨C,hC,hb⟩ := rectangularGaussianTailMoment_uniform_logarithmic_bound
    K hK δ hδ hρ hθ a b f g Φ hf hg hΦ A
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1 : ℝ)] with T hb hT
  intro σ hσ
  apply (hb σ hσ).2.trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)

end
end Sechstmoment
