import SixthMoment.Numerator.U.Replacement.TimeGammaErrorGaussian
import SixthMoment.Numerator.U.Separation.Frequency.ActualFarIntegral
import SixthMoment.Numerator.U.Separation.Frequency.GammaProfile

namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

def a03GaussianReplacementTimeProfile (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (z : ℂ) : ℝ→ℂ :=
  a03ProfileProduct Φ (bblrGaussianTimeReplacementAmplitude T σ α z)

def a03GaussianReplacementFrequencyProfile (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (z : ℂ) (ξ : ℝ) : ℂ :=
  profileLaplaceTransform (a03GaussianReplacementTimeProfile Φ T σ α z) ((ξ:ℂ)*I)

theorem a03_gaussian_replacement_frequency_uniform_derivative_bounds
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) :
    ∃ C : ℕ→ℕ→ℝ, (∀ k N, 0≤C k N) ∧
      ∀ (T : ℝ) (σ α : MomentShifts) (v : ℝ),
      10≤T → 1≤Real.log T → (∀ j, ‖α j‖≤1/4) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      192*(‖(c:ℂ)+(v:ℂ)*I‖+‖(c:ℂ)+(v:ℂ)*I‖^2)<T →
      ∀ k N : ℕ, ∀ ξ : ℝ,
      |ξ|^N*‖iteratedDeriv k (a03GaussianReplacementFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)) ξ‖≤
        C k N*T^(ε-1) := by
  obtain ⟨B,hB,hBd⟩ := bblrGaussianTimeReplacementAmplitude_uniform_subpower_derivatives hc hc1 hε hκ
  obtain ⟨C,hC,hCd⟩ := a03_profile_product_all_frequency_derivatives hΦ hs
  refine ⟨fun k N => a03ProfileProductDerivativeBudget (C k) B N,
    fun k N => a03_profile_product_budget_nonneg (hC k) hB N,?_⟩
  intro T σ α v hT hlog hα hroot hz k N ξ
  have hAc (x : ℝ) (hx : x∈Icc (1:ℝ) 2) :
      ContDiffAt ℝ ∞ (bblrGaussianTimeReplacementAmplitude T σ α ((c:ℂ)+(v:ℂ)*I)) x :=
    (bblrGaussianTimeReplacementAmplitude_contDiffAt hT σ α hα hz hx).of_le (by simp)
  have hAd (j : ℕ) (x : ℝ) (hx : x∈Icc (1:ℝ) 2) :
      ‖iteratedDeriv j (bblrGaussianTimeReplacementAmplitude T σ α ((c:ℂ)+(v:ℂ)*I)) x‖≤B j*T^(ε-1) :=
    hBd T σ α v x hT hlog hα hroot hz hx j
  exact hCd _ hAc B hB (T^(ε-1)) (Real.rpow_nonneg (by linarith) _) hAd k N ξ

theorem a03_gaussian_replacement_frequency_logarithmic_uniform_derivative_bounds
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) :
    ∃ C : ℕ→ℕ→ℝ, (∀ k N, 0≤C k N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ k N : ℕ, ∀ ξ : ℝ,
      |ξ|^N*‖iteratedDeriv k (a03GaussianReplacementFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)) ξ‖≤
        C k N*T^(ε-1) := by
  obtain ⟨C,hC,hCd⟩ := a03_gaussian_replacement_frequency_uniform_derivative_bounds hΦ hs hc hc1 hε hκ
  refine ⟨C,hC,?_⟩
  filter_upwards [bblrGamma_logarithmic_strip_large hc.le hc1 hθ,eventually_ge_atTop (10:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hz hT hlog
  intro σ α hα hroot v hv k N ξ
  exact hCd T σ α v hT hlog hα hroot (hz v hv) k N ξ

def a03GaussianReplacementActualTimeIntegral (Φ : ℝ→ℂ) (T : ℝ)
    (σ α : MomentShifts) (z : ℂ) (a b : ℕ) (n : Fin 4→ℕ) : ℂ :=
  ∫ t : ℝ, Φ (t/T)*(polarPoleKiller T σ z/z*(Real.pi:ℂ)^(-2*z)*
    (bblrGammaQuotient t α z-(t/2:ℂ)^(2*z)))*rectangularTwistedQuadPhase t a b n

theorem a03_gaussian_replacement_actual_time_exact_rescaling (Φ : ℝ→ℂ)
    {T : ℝ} (hT : 0<T) (σ α : MomentShifts) (z : ℂ)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (n : Fin 4→ℕ) :
    a03GaussianReplacementActualTimeIntegral Φ T σ α z a b n=
      (T:ℂ)*a03GaussianReplacementFrequencyProfile Φ T σ α z
        (-T*Real.log (phaseActualProductRatio a b n)) := by
  have he : a03GaussianReplacementActualTimeIntegral Φ T σ α z a b n=
      phaseActualTimeIntegral (a03GaussianReplacementTimeProfile Φ T σ α z) T a b n := by
    unfold a03GaussianReplacementActualTimeIntegral phaseActualTimeIntegral
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [a03GaussianReplacementTimeProfile,a03ProfileProduct,bblrGaussianTimeReplacementAmplitude,
      mul_div_cancel₀ t hT.ne']
    have ht : (T:ℂ)*(t/T:ℝ)=(t:ℂ) := by
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hT.ne']
    rw [ht]
  rw [he,phase_actual_time_integral_eq_profile_unrestricted _ T ha hb,
    a03_profile_time_fourier_rescaling _ hT]
  unfold a03GaussianReplacementFrequencyProfile
  congr 2
  push_cast
  ring

theorem a03_gaussian_replacement_actual_time_uniform_weighted_bound
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) :
    ∃ C : ℕ→ℝ, (∀ N, 0≤C N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ a b : ℕ, 0<a → 0<b →
      ∀ n : Fin 4→ℕ, ∀ N : ℕ,
      |-T*Real.log (phaseActualProductRatio a b n)|^N*
        ‖a03GaussianReplacementActualTimeIntegral Φ T σ α ((c:ℂ)+(v:ℂ)*I) a b n‖≤C N*T^ε := by
  obtain ⟨C,hC,hCd⟩ := a03_gaussian_replacement_frequency_logarithmic_uniform_derivative_bounds
    hΦ hs hc hc1 hε hκ hθ
  refine ⟨C 0,hC 0,?_⟩
  filter_upwards [hCd,eventually_gt_atTop (0:ℝ)] with T hbT hT
  intro σ α hα hroot v hv a b ha hb n N
  have hF := hbT σ α hα hroot v hv 0 N (-T*Real.log (phaseActualProductRatio a b n))
  simp only [iteratedDeriv_zero] at hF
  rw [a03_gaussian_replacement_actual_time_exact_rescaling Φ hT σ α _ ha hb,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  calc
    _=T*(|-T*Real.log (phaseActualProductRatio a b n)|^N*
        ‖a03GaussianReplacementFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)
          (-T*Real.log (phaseActualProductRatio a b n))‖) := by ring
    _≤T*(C 0 N*T^(ε-1)) := mul_le_mul_of_nonneg_left hF hT.le
    _=C 0 N*T^ε := by
      rw [show T*(C 0 N*T^(ε-1))=C 0 N*(T^(1:ℝ)*T^(ε-1)) by rw [Real.rpow_one]; ring,
        ← Real.rpow_add hT]
      congr 1
      ring


theorem a03_gaussian_replacement_actual_time_uniform_schwartz_bound
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) :
    ∃ C : ℕ→ℝ, (∀ N, 0≤C N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ a b : ℕ, 0<a → 0<b →
      ∀ n : Fin 4→ℕ, ∀ N : ℕ,
      (1+|-T*Real.log (phaseActualProductRatio a b n)|)^N*
        ‖a03GaussianReplacementActualTimeIntegral Φ T σ α ((c:ℂ)+(v:ℂ)*I) a b n‖≤C N*T^ε := by
  obtain ⟨C,hC,hCd⟩ := a03_gaussian_replacement_actual_time_uniform_weighted_bound
    hΦ hs hc hc1 hε hκ hθ
  refine ⟨fun N => 2^N*(C 0+C N),
    fun N => mul_nonneg (by positivity) (add_nonneg (hC 0) (hC N)),?_⟩
  filter_upwards [hCd,eventually_gt_atTop (0:ℝ)] with T hbT hT
  intro σ α hα hroot v hv a b ha hb n N
  let ξ := -T*Real.log (phaseActualProductRatio a b n)
  let E := ‖a03GaussianReplacementActualTimeIntegral Φ T σ α ((c:ℂ)+(v:ℂ)*I) a b n‖
  have hE : 0≤E := norm_nonneg _
  have h0 : E≤C 0*T^ε := by simpa using hbT σ α hα hroot v hv a b ha hb n 0
  have hN : |ξ|^N*E≤C N*T^ε := hbT σ α hα hroot v hv a b ha hb n N
  change (1+|ξ|)^N*E≤(2^N*(C 0+C N))*T^ε
  by_cases hξ : |ξ|≤1
  · calc
      _≤2^N*E := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) N) hE
      _≤2^N*(C 0*T^ε) := mul_le_mul_of_nonneg_left h0 (by positivity)
      _≤_ := by
        have hh := mul_nonneg (hC N) (Real.rpow_nonneg hT.le ε)
        nlinarith [show (0:ℝ)≤2^N by positivity]
  · have hξ1 : 1≤|ξ| := le_of_lt (lt_of_not_ge hξ)
    calc
      _≤(2*|ξ|)^N*E := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) N) hE
      _=2^N*(|ξ|^N*E) := by rw [mul_pow]; ring
      _≤2^N*(C N*T^ε) := mul_le_mul_of_nonneg_left hN (by positivity)
      _≤_ := by
        have hh := mul_nonneg (hC 0) (Real.rpow_nonneg hT.le ε)
        nlinarith [show (0:ℝ)≤2^N by positivity]


def rectangularWeightReplacementMellinKernel (G : ℂ→ℂ) (α : MomentShifts)
    (t : ℝ) (n : Fin 4→ℕ) (z : ℂ) : ℂ :=
  G z/z*(bblrGammaQuotient t α z-(t/2:ℂ)^(2*z))*(Real.pi:ℂ)^(-2*z)*
    rectangularAFEOscillation t n/∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+z)

theorem rectangular_weight_replacement_actual_time_factorization (T : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) (u v : ℕ) (n : Fin 4→ℕ) (z : ℂ) :
    (∫ t : ℝ, rectangularMomentPairWeight T f g Φ u v t*
      rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n z)=
      (phaseActualAmplifierPairConstant T f g u v/
        ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+z))*
        a03GaussianReplacementActualTimeIntegral (fun x => (Φ x:ℂ)) T σ α z (u+1) (v+1) n := by
  unfold a03GaussianReplacementActualTimeIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold rectangularWeightReplacementMellinKernel
  simp only [div_eq_mul_inv]
  calc
    _=(rectangularMomentPairWeight T f g Φ u v t*rectangularAFEOscillation t n)*
        (polarPoleKiller T σ z*z⁻¹*(bblrGammaQuotient t α z-(t/2:ℂ)^(2*z))*(Real.pi:ℂ)^(-2*z))*
        (∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+z))⁻¹ := by ring
    _=_ := by
      rw [rectangular_actual_pair_weight_oscillation]
      unfold phaseActualAmplifierPairConstant
      ring

theorem rectangular_weight_replacement_actual_time_uniform_schwartz_bound
    {Φ : ℝ→ℝ} (hΦ : SmoothDyadicWeight Φ)
    {c ε κ θ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) :
    ∃ C : ℕ→ℝ, (∀ N, 0≤C N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ f g : ℝ→ℝ, ∀ u w : ℕ,
      ∀ n : Fin 4→ℕ, ∀ N : ℕ,
      (1+|-T*Real.log (phaseActualProductRatio (u+1) (w+1) n)|)^N*
        ‖∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
          rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤
        ‖phaseActualAmplifierPairConstant T f g u w/
          ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+((c:ℂ)+(v:ℂ)*I))‖*C N*T^ε := by
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  obtain ⟨C,hC,hCd⟩ := a03_gaussian_replacement_actual_time_uniform_schwartz_bound hΦc hΦs hc hc1 hε hκ hθ
  refine ⟨C,hC,?_⟩
  filter_upwards [hCd] with T hbT
  intro σ α hα hroot v hv f g u w n N
  rw [rectangular_weight_replacement_actual_time_factorization,norm_mul]
  have hb := hbT σ α hα hroot v hv (u+1) (w+1) (by omega) (by omega) n N
  let D : ℝ := ‖phaseActualAmplifierPairConstant T f g u w/
    ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+((c:ℂ)+(v:ℂ)*I))‖
  change (1+|-T*Real.log (phaseActualProductRatio (u+1) (w+1) n)|)^N*
    (D*‖a03GaussianReplacementActualTimeIntegral (fun x => (Φ x:ℂ)) T σ α
      ((c:ℂ)+(v:ℂ)*I) (u+1) (w+1) n‖)≤D*C N*T^ε
  have hD : 0≤D := norm_nonneg _
  calc
    _=D*((1+|-T*Real.log (phaseActualProductRatio (u+1) (w+1) n)|)^N*
      ‖a03GaussianReplacementActualTimeIntegral (fun x => (Φ x:ℂ)) T σ α
        ((c:ℂ)+(v:ℂ)*I) (u+1) (w+1) n‖) := by ring
    _≤D*(C N*T^ε) := mul_le_mul_of_nonneg_left hb hD
    _=_ := by ring

end
end SixthMoment
