import Sechstmoment.Numerator.U.Replacement.DualErrorGaussian
import Sechstmoment.Numerator.U.Replacement.TimeGammaErrorFourier

/-! Complete literal dual replacement Fourier kernel, retaining original χ
shifts, the polekiller, raw dual Gamma shifts, and every arithmetic factor. -/
namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

def a03GaussianDualReplacementTimeProfile (Φ : ℝ→ℂ) (T : ℝ) (σ τ α : MomentShifts)
    (z : ℂ) : ℝ→ℂ :=
  a03ProfileProduct Φ (bblrGaussianDualReplacementAmplitude T σ τ α z)

def a03GaussianDualReplacementFrequencyProfile (Φ : ℝ→ℂ) (T : ℝ) (σ τ α : MomentShifts)
    (z : ℂ) (ξ : ℝ) : ℂ :=
  profileLaplaceTransform (a03GaussianDualReplacementTimeProfile Φ T σ τ α z) ((ξ:ℂ)*I)

theorem a03_gaussian_dual_replacement_frequency_logarithmic_uniform_derivative_bounds
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℕ→ℕ→ℝ, (∀ k N, 0≤C k N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ τ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot τ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ k N : ℕ, ∀ ξ : ℝ,
      |ξ|^N*‖iteratedDeriv k (a03GaussianDualReplacementFrequencyProfile Φ T σ τ α ((c:ℂ)+(v:ℂ)*I)) ξ‖≤
        C k N*T^(ε-1) := by
  obtain ⟨P,hP,hPd⟩ := bblrGaussianDualReplacementAmplitude_logarithmic_uniform_subpower_derivatives hc hc1 hε hκ hθ hR
  obtain ⟨C,hC,hCd⟩ := a03_profile_product_all_frequency_derivatives hΦ hs
  refine ⟨fun k N => a03ProfileProductDerivativeBudget (C k) P N,
    fun k N => a03_profile_product_budget_nonneg (hC k) hP N,?_⟩
  filter_upwards [hPd,eventually_gt_atTop (0:ℝ)] with T hbT hT
  intro σ τ α hσ hα hroot v hv k N ξ
  have hAc (x : ℝ) (hx : x∈Icc (1:ℝ) 2) := (hbT σ τ α hσ hα hroot v hv x hx).1
  have hAd (j : ℕ) (x : ℝ) (hx : x∈Icc (1:ℝ) 2) := (hbT σ τ α hσ hα hroot v hv x hx).2 j
  exact hCd _ hAc P hP (T^(ε-1)) (Real.rpow_nonneg hT.le _) hAd k N ξ

def a03GaussianDualReplacementActualTimeIntegral (Φ : ℝ→ℂ) (T : ℝ)
    (σ τ α : MomentShifts) (z : ℂ) (a b : ℕ) (n : Fin 4→ℕ) : ℂ :=
  ∫ t : ℝ, Φ (t/T)*(polarPoleKiller T τ z/z*(Real.pi:ℂ)^(-2*z)*
    (bblrDualMultiplier t (rawMomentShifts T σ)*bblrGammaQuotient t α z-
      (t/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j)*(t/2:ℂ)^(2*z)))*rectangularTwistedQuadPhase t a b n

theorem a03_gaussian_dual_replacement_actual_time_exact_rescaling (Φ : ℝ→ℂ)
    {T : ℝ} (hT : 0<T) (σ τ α : MomentShifts) (z : ℂ)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (n : Fin 4→ℕ) :
    a03GaussianDualReplacementActualTimeIntegral Φ T σ τ α z a b n=
      (T:ℂ)*a03GaussianDualReplacementFrequencyProfile Φ T σ τ α z
        (-T*Real.log (phaseActualProductRatio a b n)) := by
  have he : a03GaussianDualReplacementActualTimeIntegral Φ T σ τ α z a b n=
      phaseActualTimeIntegral (a03GaussianDualReplacementTimeProfile Φ T σ τ α z) T a b n := by
    unfold a03GaussianDualReplacementActualTimeIntegral phaseActualTimeIntegral
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [a03GaussianDualReplacementTimeProfile,a03ProfileProduct,bblrGaussianDualReplacementAmplitude,bblrDualLeadingMultiplier,
      mul_div_cancel₀ t hT.ne']
    have ht : (T:ℂ)*(t/T:ℝ)=(t:ℂ) := by
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hT.ne']
    rw [ht]
  rw [he,phase_actual_time_integral_eq_profile_unrestricted _ T ha hb,
    a03_profile_time_fourier_rescaling _ hT]
  unfold a03GaussianDualReplacementFrequencyProfile
  congr 2
  push_cast
  ring

/-- The genuine time-integrated replacement kernel, with its exact arithmetic
frequency. The bound includes all four AFE variables without substituting a
free near-gap parameter. -/
theorem a03_gaussian_dual_replacement_actual_time_uniform_weighted_bound
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℕ→ℝ, (∀ N, 0≤C N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ τ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot τ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ a b : ℕ, 0<a → 0<b →
      ∀ n : Fin 4→ℕ, ∀ N : ℕ,
      |-T*Real.log (phaseActualProductRatio a b n)|^N*
        ‖a03GaussianDualReplacementActualTimeIntegral Φ T σ τ α ((c:ℂ)+(v:ℂ)*I) a b n‖≤C N*T^ε := by
  obtain ⟨C,hC,hCd⟩ := a03_gaussian_dual_replacement_frequency_logarithmic_uniform_derivative_bounds
    hΦ hs hc hc1 hε hκ hθ hR
  refine ⟨C 0,hC 0,?_⟩
  filter_upwards [hCd,eventually_gt_atTop (0:ℝ)] with T hbT hT
  intro σ τ α hσ hα hroot v hv a b ha hb n N
  have hF := hbT σ τ α hσ hα hroot v hv 0 N (-T*Real.log (phaseActualProductRatio a b n))
  simp only [iteratedDeriv_zero] at hF
  rw [a03_gaussian_dual_replacement_actual_time_exact_rescaling Φ hT σ τ α _ ha hb,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  calc
    _=T*(|-T*Real.log (phaseActualProductRatio a b n)|^N*
        ‖a03GaussianDualReplacementFrequencyProfile Φ T σ τ α ((c:ℂ)+(v:ℂ)*I)
          (-T*Real.log (phaseActualProductRatio a b n))‖) := by ring
    _≤T*(C 0 N*T^(ε-1)) := mul_le_mul_of_nonneg_left hF hT.le
    _=C 0 N*T^ε := by
      rw [show T*(C 0 N*T^(ε-1))=C 0 N*(T^(1:ℝ)*T^(ε-1)) by rw [Real.rpow_one]; ring,
        ← Real.rpow_add hT]
      congr 1
      ring


/-- The actual integrated error is uniformly a rapidly decreasing symbol at
the exact amplified AFE frequency, including frequency zero. -/
theorem a03_gaussian_dual_replacement_actual_time_uniform_schwartz_bound
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℕ→ℝ, (∀ N, 0≤C N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ τ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot τ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ a b : ℕ, 0<a → 0<b →
      ∀ n : Fin 4→ℕ, ∀ N : ℕ,
      (1+|-T*Real.log (phaseActualProductRatio a b n)|)^N*
        ‖a03GaussianDualReplacementActualTimeIntegral Φ T σ τ α ((c:ℂ)+(v:ℂ)*I) a b n‖≤C N*T^ε := by
  obtain ⟨C,hC,hCd⟩ := a03_gaussian_dual_replacement_actual_time_uniform_weighted_bound
    hΦ hs hc hc1 hε hκ hθ hR
  refine ⟨fun N => 2^N*(C 0+C N),
    fun N => mul_nonneg (by positivity) (add_nonneg (hC 0) (hC N)),?_⟩
  filter_upwards [hCd,eventually_gt_atTop (0:ℝ)] with T hbT hT
  intro σ τ α hσ hα hroot v hv a b ha hb n N
  let ξ := -T*Real.log (phaseActualProductRatio a b n)
  let E := ‖a03GaussianDualReplacementActualTimeIntegral Φ T σ τ α ((c:ℂ)+(v:ℂ)*I) a b n‖
  have hE : 0≤E := norm_nonneg _
  have h0 : E≤C 0*T^ε := by simpa using hbT σ τ α hσ hα hroot v hv a b ha hb n 0
  have hN : |ξ|^N*E≤C N*T^ε := hbT σ τ α hσ hα hroot v hv a b ha hb n N
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


def rectangularDualReplacementMellinKernel (T : ℝ) (σ : MomentShifts) (G : ℂ→ℂ) (α : MomentShifts)
    (t : ℝ) (n : Fin 4→ℕ) (z : ℂ) : ℂ :=
  G z/z*(bblrDualMultiplier t (rawMomentShifts T σ)*bblrGammaQuotient t α z-
      (t/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j)*(t/2:ℂ)^(2*z))*(Real.pi:ℂ)^(-2*z)*
    rectangularAFEOscillation t n/∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+z)

/-- Exact time factorization retains both real amplifier coefficients and all
four literal AFE denominator powers. -/
theorem rectangular_dual_replacement_actual_time_factorization (T : ℝ)
    (f g Φ : ℝ→ℝ) (σ τ α : MomentShifts) (u v : ℕ) (n : Fin 4→ℕ) (z : ℂ) :
    (∫ t : ℝ, rectangularMomentPairWeight T f g Φ u v t*
      rectangularDualReplacementMellinKernel T σ (polarPoleKiller T τ) α t n z)=
      (phaseActualAmplifierPairConstant T f g u v/
        ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+z))*
        a03GaussianDualReplacementActualTimeIntegral (fun x => (Φ x:ℂ)) T σ τ α z (u+1) (v+1) n := by
  unfold a03GaussianDualReplacementActualTimeIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold rectangularDualReplacementMellinKernel
  simp only [div_eq_mul_inv]
  calc
    _=(rectangularMomentPairWeight T f g Φ u v t*rectangularAFEOscillation t n)*
        (polarPoleKiller T τ z*z⁻¹*(bblrDualMultiplier t (rawMomentShifts T σ)*bblrGammaQuotient t α z-
      (t/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j)*(t/2:ℂ)^(2*z))*(Real.pi:ℂ)^(-2*z))*
        (∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+z))⁻¹ := by ring
    _=_ := by
      rw [rectangular_actual_pair_weight_oscillation]
      unfold phaseActualAmplifierPairConstant
      ring

/-- The actual amplified Mellin error has a uniform rapidly decreasing
frequency budget. The complete arithmetic prefactor is explicit. -/
theorem rectangular_dual_replacement_actual_time_uniform_schwartz_bound
    {Φ : ℝ→ℝ} (hΦ : SmoothDyadicWeight Φ)
    {c ε κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℕ→ℝ, (∀ N, 0≤C N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ τ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot τ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ f g : ℝ→ℝ, ∀ u w : ℕ,
      ∀ n : Fin 4→ℕ, ∀ N : ℕ,
      (1+|-T*Real.log (phaseActualProductRatio (u+1) (w+1) n)|)^N*
        ‖∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
          rectangularDualReplacementMellinKernel T σ (polarPoleKiller T τ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤
        ‖phaseActualAmplifierPairConstant T f g u w/
          ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+((c:ℂ)+(v:ℂ)*I))‖*C N*T^ε := by
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  obtain ⟨C,hC,hCd⟩ := a03_gaussian_dual_replacement_actual_time_uniform_schwartz_bound hΦc hΦs hc hc1 hε hκ hθ hR
  refine ⟨C,hC,?_⟩
  filter_upwards [hCd] with T hbT
  intro σ τ α hσ hα hroot v hv f g u w n N
  rw [rectangular_dual_replacement_actual_time_factorization,norm_mul]
  have hb := hbT σ τ α hσ hα hroot v hv (u+1) (w+1) (by omega) (by omega) n N
  let D : ℝ := ‖phaseActualAmplifierPairConstant T f g u w/
    ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+((c:ℂ)+(v:ℂ)*I))‖
  change (1+|-T*Real.log (phaseActualProductRatio (u+1) (w+1) n)|)^N*
    (D*‖a03GaussianDualReplacementActualTimeIntegral (fun x => (Φ x:ℂ)) T σ τ α
      ((c:ℂ)+(v:ℂ)*I) (u+1) (w+1) n‖)≤D*C N*T^ε
  have hD : 0≤D := norm_nonneg _
  calc
    _=D*((1+|-T*Real.log (phaseActualProductRatio (u+1) (w+1) n)|)^N*
      ‖a03GaussianDualReplacementActualTimeIntegral (fun x => (Φ x:ℂ)) T σ τ α
        ((c:ℂ)+(v:ℂ)*I) (u+1) (w+1) n‖) := by ring
    _≤D*(C N*T^ε) := mul_le_mul_of_nonneg_left hb hD
    _=_ := by ring

end
end Sechstmoment
