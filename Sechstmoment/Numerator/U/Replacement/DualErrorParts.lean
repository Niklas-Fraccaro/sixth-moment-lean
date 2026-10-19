import Sechstmoment.Numerator.U.Replacement.DualErrorFourier

/-! Separate literal dual Gamma-weight and dual-phase replacement errors.
Both estimates follow from the already proved genuine factor derivative bounds. -/
namespace Sechstmoment.Source
open Sechstmoment Complex Set Metric Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000

/-- `false` is the dual weight error; `true` is the corresponding phase error.
The polekiller uses the original shifts in either part. -/
def bblrGaussianDualErrorPartAmplitude (phasePart : Bool) (T : ℝ)
    (σ τ α : MomentShifts) (z : ℂ) (y : ℝ) : ℂ :=
  if phasePart then
    bblrDualPhaseTimeError T σ y*
      (bblrGaussianTimeAmplitude T τ α z y-bblrGaussianTimeReplacementAmplitude T τ α z y)
  else
    bblrDualMultiplier (T*y) (rawMomentShifts T σ)*bblrGaussianTimeReplacementAmplitude T τ α z y

theorem bblrGaussianDualErrorPartAmplitude_exact (phasePart : Bool) (T : ℝ)
    (σ τ α : MomentShifts) (z : ℂ) (y : ℝ) :
    bblrGaussianDualErrorPartAmplitude phasePart T σ τ α z y =
      (polarPoleKiller T τ z/z*(Real.pi:ℂ)^(-2*z))*
        (if phasePart then
          (bblrDualMultiplier (T*y) (rawMomentShifts T σ)-bblrDualLeadingMultiplier T σ y)*(T*y/2:ℂ)^(2*z)
        else bblrDualMultiplier (T*y) (rawMomentShifts T σ)*
          (bblrGammaQuotient (T*y) α z-(T*y/2:ℂ)^(2*z))) := by
  cases phasePart <;>
    simp only [bblrGaussianDualErrorPartAmplitude,Bool.false_eq_true,ite_false,ite_true,
      bblrDualPhaseTimeError,bblrGaussianTimeAmplitude,bblrGaussianTimeReplacementAmplitude] <;> ring

theorem bblrGaussianDualErrorPartAmplitude_sum (T : ℝ)
    (σ τ α : MomentShifts) (z : ℂ) :
    bblrGaussianDualReplacementAmplitude T σ τ α z = fun y =>
      bblrGaussianDualErrorPartAmplitude false T σ τ α z y+
        bblrGaussianDualErrorPartAmplitude true T σ τ α z y := by
  rw [bblrGaussianDualReplacementAmplitude_exact_split]
  rfl

private theorem dual_part_error_contDiffAt {T R : ℝ} (hR : 0≤R) (hL : 1≤Real.log T)
    (hT : 192*(R+R^2)+8≤T) (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖≤R)
    {x : ℝ} (hx : x∈Icc (1:ℝ) 2) :
    ContDiffAt ℝ ⊤ (bblrDualPhaseTimeError T σ) x := by
  have hT0 : 0<T := by nlinarith [sq_nonneg R]
  have ha : AnalyticAt ℂ (a03DualLeadingPhase T σ) (x:ℂ) := by
    apply DifferentiableOn.analyticAt _
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0:ℝ)<1/4)))
    intro y hy
    have hw := bblrTimeGamma_closedBall_window hx (ball_subset_closedBall hy)
    unfold a03DualLeadingPhase
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.cpow_const
    · fun_prop
    · apply Complex.mem_slitPlane_iff.mpr
      left
      simp [Complex.div_re,Complex.mul_re,Complex.mul_im]
      have hrey : 0<y.re := by linarith [hw.1.1]
      positivity
  have hc : ContDiffAt ℝ ⊤ (fun y : ℝ => a03DualLeadingPhase T σ (y:ℂ)) x :=
    (ha.contDiffAt.restrict_scalars ℝ).comp x Complex.ofRealCLM.contDiff.contDiffAt
  have he : (fun y : ℝ => a03DualLeadingPhase T σ (y:ℂ))=bblrDualLeadingMultiplier T σ := by
    funext y
    exact a03DualLeadingPhase_ofReal T σ y
  rw [he] at hc
  exact (bblrDualMultiplier_normalizedTime_contDiffAt hR hL hT σ hσ hx).sub hc

theorem bblrGaussianDualErrorPartAmplitude_logarithmic_uniform_subpower_derivatives
    {c ε κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ)
    (hθ : 0≤θ) (hR : 0≤R) :
    ∃ P : ℕ→ℝ, (∀ n, 0≤P n) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ τ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) →
      (∀ k : PurePolarIndex, κ≤‖normalizedPurePolarRoot τ k‖) →
      ∀ phasePart : Bool, ∀ v : ℝ, |v|≤θ*Real.log T → ∀ x : ℝ, x∈Icc (1:ℝ) 2 →
      ContDiffAt ℝ ∞ (bblrGaussianDualErrorPartAmplitude phasePart T σ τ α ((c:ℂ)+(v:ℂ)*I)) x ∧
      ∀ n : ℕ, ‖iteratedDeriv n (bblrGaussianDualErrorPartAmplitude phasePart T σ τ α ((c:ℂ)+(v:ℂ)*I)) x‖≤P n*T^(ε-1) := by
  obtain ⟨E,hE,hEd⟩ := bblrDualMultiplier_normalizedTime_uniform_derivative_bounds hR
  obtain ⟨F,hF,hFd⟩ := a03DualPhaseReplacementError_normalizedTime_uniform_derivative_bounds hR
  obtain ⟨B,hB,hBd⟩ := bblrGaussianTimeAmplitude_uniform_subpower_derivatives hc hc1 hε hκ
  obtain ⟨H,hH,hHd⟩ := bblrGaussianTimeReplacementAmplitude_uniform_subpower_derivatives hc hc1 hε hκ
  let J : ℕ→ℝ := fun n => B n+H n
  have hJ : ∀ n, 0≤J n := fun n => add_nonneg (hB n) (hH n)
  let P : ℕ→ℝ := fun n => a03ProfileProductDerivativeBudget E H n+a03ProfileProductDerivativeBudget F J n
  refine ⟨P,fun n => add_nonneg (a03_profile_product_budget_nonneg hE hH n)
    (a03_profile_product_budget_nonneg hF hJ n),?_⟩
  filter_upwards [hEd,hFd,bblrGamma_logarithmic_strip_large hc.le hc1 hθ,
    eventually_ge_atTop (192*(R+R^2)+8),eventually_ge_atTop (10:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
      with T hEder hFder hlarge hRT hT hL
  intro σ τ α hσ hα hroot phasePart v hv x hx
  have hT0 : 0<T := by linarith
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  let A : ℝ→ℂ := fun y => bblrDualMultiplier (T*y) (rawMomentShifts T σ)
  let D : ℝ→ℂ := bblrDualPhaseTimeError T σ
  let G : ℝ→ℂ := bblrGaussianTimeAmplitude T τ α z
  let Q : ℝ→ℂ := bblrGaussianTimeReplacementAmplitude T τ α z
  have hAc : ContDiffAt ℝ ∞ A x := (bblrDualMultiplier_normalizedTime_contDiffAt hR hL hRT σ hσ hx).of_le (by simp)
  have hDc : ContDiffAt ℝ ∞ D x := (dual_part_error_contDiffAt hR hL hRT σ hσ hx).of_le (by simp)
  have hGc : ContDiffAt ℝ ∞ G x := (bblrGaussianTimeAmplitude_contDiffAt (by norm_num : (0:ℝ)≤1/4)
    (by norm_num; exact hT) τ α hα (hlarge v hv) hx).of_le (by simp)
  have hQc : ContDiffAt ℝ ∞ Q x := (bblrGaussianTimeReplacementAmplitude_contDiffAt hT τ α hα (hlarge v hv) hx).of_le (by simp)
  have hAd (n : ℕ) : ‖iteratedDeriv n A x‖≤E n*1 := by simpa using hEder σ hσ x hx n
  have hDd (n : ℕ) : ‖iteratedDeriv n D x‖≤F n*(1/T) := by
    change ‖iteratedDeriv n (fun y : ℝ => bblrDualMultiplier (T*y) (rawMomentShifts T σ)-
      (T*y/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j)) x‖≤F n*(1/T)
    simpa only [div_eq_mul_inv,one_mul] using hFder σ hσ x hx n
  have hGd (n : ℕ) : ‖iteratedDeriv n G x‖≤B n*T^ε :=
    hBd T (1/4) τ α v x (by linarith) hL (by norm_num) (by norm_num; exact hT) hα hroot (hlarge v hv) hx n
  have hQd (n : ℕ) : ‖iteratedDeriv n Q x‖≤H n*T^(ε-1) :=
    hHd T τ α v x hT hL hα hroot (hlarge v hv) hx n
  have hpowers : T^(ε-1)≤T^ε := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hSQd (n : ℕ) : ‖iteratedDeriv n (fun y => G y-Q y) x‖≤J n*T^ε := by
    rw [iteratedDeriv_fun_sub (hGc.of_le (by simp)) (hQc.of_le (by simp))]
    calc
      _≤‖iteratedDeriv n G x‖+‖iteratedDeriv n Q x‖ := norm_sub_le _ _
      _≤B n*T^ε+H n*T^(ε-1) := add_le_add (hGd n) (hQd n)
      _≤J n*T^ε := by dsimp [J]; nlinarith [mul_le_mul_of_nonneg_left hpowers (hH n)]
  have hAQc := hAc.mul hQc
  have hDSQc := hDc.mul (hGc.sub hQc)
  have h1 := a03_pointwise_product_derivative_budget hE hH (by norm_num : (0:ℝ)≤1)
    (Real.rpow_nonneg hT0.le _) hAc hQc hAd hQd
  have h2 := a03_pointwise_product_derivative_budget hF hJ (by positivity : 0≤1/T)
    (Real.rpow_nonneg hT0.le _) hDc (hGc.sub hQc) hDd hSQd
  have he : (1/T)*T^ε=T^(ε-1) := by rw [Real.rpow_sub hT0,Real.rpow_one]; ring
  cases phasePart
  · change ContDiffAt ℝ ∞ (fun y => A y*Q y) x ∧ _
    refine ⟨hAQc,fun n => (h1 n).trans ?_⟩
    dsimp [P]
    simp only [one_mul]
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (a03_profile_product_budget_nonneg hF hJ n))
      (Real.rpow_nonneg hT0.le _)
  · change ContDiffAt ℝ ∞ (fun y => D y*(G y-Q y)) x ∧ _
    refine ⟨hDSQc,fun n => ?_⟩
    have h := h2 n
    rw [he] at h
    apply h.trans
    dsimp [P]
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (a03_profile_product_budget_nonneg hE hH n))
      (Real.rpow_nonneg hT0.le _)

end
end Sechstmoment.Source

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

def a03GaussianDualErrorPartTimeProfile (phasePart : Bool) (Φ : ℝ→ℂ) (T : ℝ) (σ τ α : MomentShifts)
    (z : ℂ) : ℝ→ℂ :=
  a03ProfileProduct Φ (bblrGaussianDualErrorPartAmplitude phasePart T σ τ α z)

def a03GaussianDualErrorPartFrequencyProfile (phasePart : Bool) (Φ : ℝ→ℂ) (T : ℝ) (σ τ α : MomentShifts)
    (z : ℂ) (ξ : ℝ) : ℂ :=
  profileLaplaceTransform (a03GaussianDualErrorPartTimeProfile phasePart Φ T σ τ α z) ((ξ:ℂ)*I)

theorem a03_gaussian_dual_error_part_frequency_logarithmic_uniform_derivative_bounds
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℕ→ℕ→ℝ, (∀ k N, 0≤C k N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ τ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot τ j‖) →
      ∀ phasePart : Bool, ∀ v : ℝ, |v|≤θ*Real.log T → ∀ k N : ℕ, ∀ ξ : ℝ,
      |ξ|^N*‖iteratedDeriv k (a03GaussianDualErrorPartFrequencyProfile phasePart Φ T σ τ α ((c:ℂ)+(v:ℂ)*I)) ξ‖≤
        C k N*T^(ε-1) := by
  obtain ⟨P,hP,hPd⟩ := bblrGaussianDualErrorPartAmplitude_logarithmic_uniform_subpower_derivatives hc hc1 hε hκ hθ hR
  obtain ⟨C,hC,hCd⟩ := a03_profile_product_all_frequency_derivatives hΦ hs
  refine ⟨fun k N => a03ProfileProductDerivativeBudget (C k) P N,
    fun k N => a03_profile_product_budget_nonneg (hC k) hP N,?_⟩
  filter_upwards [hPd,eventually_gt_atTop (0:ℝ)] with T hbT hT
  intro σ τ α hσ hα hroot phasePart v hv k N ξ
  have hAc (x : ℝ) (hx : x∈Icc (1:ℝ) 2) := (hbT σ τ α hσ hα hroot phasePart v hv x hx).1
  have hAd (j : ℕ) (x : ℝ) (hx : x∈Icc (1:ℝ) 2) := (hbT σ τ α hσ hα hroot phasePart v hv x hx).2 j
  exact hCd _ hAc P hP (T^(ε-1)) (Real.rpow_nonneg hT.le _) hAd k N ξ

def a03GaussianDualErrorPartActualTimeIntegral (phasePart : Bool) (Φ : ℝ→ℂ) (T : ℝ)
    (σ τ α : MomentShifts) (z : ℂ) (a b : ℕ) (n : Fin 4→ℕ) : ℂ :=
  ∫ t : ℝ, Φ (t/T)*(polarPoleKiller T τ z/z*(Real.pi:ℂ)^(-2*z)*
    (if phasePart then
      (bblrDualMultiplier t (rawMomentShifts T σ)-
        (t/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j))*(t/2:ℂ)^(2*z)
    else bblrDualMultiplier t (rawMomentShifts T σ)*
      (bblrGammaQuotient t α z-(t/2:ℂ)^(2*z))))*rectangularTwistedQuadPhase t a b n

theorem a03_gaussian_dual_error_part_actual_time_exact_rescaling (phasePart : Bool) (Φ : ℝ→ℂ)
    {T : ℝ} (hT : 0<T) (σ τ α : MomentShifts) (z : ℂ)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (n : Fin 4→ℕ) :
    a03GaussianDualErrorPartActualTimeIntegral phasePart Φ T σ τ α z a b n=
      (T:ℂ)*a03GaussianDualErrorPartFrequencyProfile phasePart Φ T σ τ α z
        (-T*Real.log (phaseActualProductRatio a b n)) := by
  have he : a03GaussianDualErrorPartActualTimeIntegral phasePart Φ T σ τ α z a b n=
      phaseActualTimeIntegral (a03GaussianDualErrorPartTimeProfile phasePart Φ T σ τ α z) T a b n := by
    unfold a03GaussianDualErrorPartActualTimeIntegral phaseActualTimeIntegral
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [a03GaussianDualErrorPartTimeProfile,a03ProfileProduct,bblrGaussianDualErrorPartAmplitude_exact,bblrDualLeadingMultiplier,
      mul_div_cancel₀ t hT.ne']
    have ht : (T:ℂ)*(t/T:ℝ)=(t:ℂ) := by
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hT.ne']
    rw [ht]
  rw [he,phase_actual_time_integral_eq_profile_unrestricted _ T ha hb,
    a03_profile_time_fourier_rescaling _ hT]
  unfold a03GaussianDualErrorPartFrequencyProfile
  congr 2
  push_cast
  ring

/-- The genuine time-integrated replacement kernel, with its exact arithmetic
frequency. The bound includes all four AFE variables without substituting a
free near-gap parameter. -/
theorem a03_gaussian_dual_error_part_actual_time_uniform_weighted_bound
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℕ→ℝ, (∀ N, 0≤C N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ τ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot τ j‖) →
      ∀ phasePart : Bool, ∀ v : ℝ, |v|≤θ*Real.log T → ∀ a b : ℕ, 0<a → 0<b →
      ∀ n : Fin 4→ℕ, ∀ N : ℕ,
      |-T*Real.log (phaseActualProductRatio a b n)|^N*
        ‖a03GaussianDualErrorPartActualTimeIntegral phasePart Φ T σ τ α ((c:ℂ)+(v:ℂ)*I) a b n‖≤C N*T^ε := by
  obtain ⟨C,hC,hCd⟩ := a03_gaussian_dual_error_part_frequency_logarithmic_uniform_derivative_bounds
    hΦ hs hc hc1 hε hκ hθ hR
  refine ⟨C 0,hC 0,?_⟩
  filter_upwards [hCd,eventually_gt_atTop (0:ℝ)] with T hbT hT
  intro σ τ α hσ hα hroot phasePart v hv a b ha hb n N
  have hF := hbT σ τ α hσ hα hroot phasePart v hv 0 N (-T*Real.log (phaseActualProductRatio a b n))
  simp only [iteratedDeriv_zero] at hF
  rw [a03_gaussian_dual_error_part_actual_time_exact_rescaling phasePart Φ hT σ τ α _ ha hb,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  calc
    _=T*(|-T*Real.log (phaseActualProductRatio a b n)|^N*
        ‖a03GaussianDualErrorPartFrequencyProfile phasePart Φ T σ τ α ((c:ℂ)+(v:ℂ)*I)
          (-T*Real.log (phaseActualProductRatio a b n))‖) := by ring
    _≤T*(C 0 N*T^(ε-1)) := mul_le_mul_of_nonneg_left hF hT.le
    _=C 0 N*T^ε := by
      rw [show T*(C 0 N*T^(ε-1))=C 0 N*(T^(1:ℝ)*T^(ε-1)) by rw [Real.rpow_one]; ring,
        ← Real.rpow_add hT]
      congr 1
      ring


/-- The actual integrated error is uniformly a rapidly decreasing symbol at
the exact amplified AFE frequency, including frequency zero. -/
theorem a03_gaussian_dual_error_part_actual_time_uniform_schwartz_bound
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℕ→ℝ, (∀ N, 0≤C N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ τ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot τ j‖) →
      ∀ phasePart : Bool, ∀ v : ℝ, |v|≤θ*Real.log T → ∀ a b : ℕ, 0<a → 0<b →
      ∀ n : Fin 4→ℕ, ∀ N : ℕ,
      (1+|-T*Real.log (phaseActualProductRatio a b n)|)^N*
        ‖a03GaussianDualErrorPartActualTimeIntegral phasePart Φ T σ τ α ((c:ℂ)+(v:ℂ)*I) a b n‖≤C N*T^ε := by
  obtain ⟨C,hC,hCd⟩ := a03_gaussian_dual_error_part_actual_time_uniform_weighted_bound
    hΦ hs hc hc1 hε hκ hθ hR
  refine ⟨fun N => 2^N*(C 0+C N),
    fun N => mul_nonneg (by positivity) (add_nonneg (hC 0) (hC N)),?_⟩
  filter_upwards [hCd,eventually_gt_atTop (0:ℝ)] with T hbT hT
  intro σ τ α hσ hα hroot phasePart v hv a b ha hb n N
  let ξ := -T*Real.log (phaseActualProductRatio a b n)
  let E := ‖a03GaussianDualErrorPartActualTimeIntegral phasePart Φ T σ τ α ((c:ℂ)+(v:ℂ)*I) a b n‖
  have hE : 0≤E := norm_nonneg _
  have h0 : E≤C 0*T^ε := by simpa using hbT σ τ α hσ hα hroot phasePart v hv a b ha hb n 0
  have hN : |ξ|^N*E≤C N*T^ε := hbT σ τ α hσ hα hroot phasePart v hv a b ha hb n N
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


def rectangularDualErrorPartMellinKernel (phasePart : Bool) (T : ℝ) (σ : MomentShifts) (G : ℂ→ℂ) (α : MomentShifts)
    (t : ℝ) (n : Fin 4→ℕ) (z : ℂ) : ℂ :=
  G z/z*(if phasePart then
      (bblrDualMultiplier t (rawMomentShifts T σ)-
        (t/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j))*(t/2:ℂ)^(2*z)
    else bblrDualMultiplier t (rawMomentShifts T σ)*
      (bblrGammaQuotient t α z-(t/2:ℂ)^(2*z)))*(Real.pi:ℂ)^(-2*z)*
    rectangularAFEOscillation t n/∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+z)

/-- The combined literal dual replacement equals the two separate errors. -/
theorem rectangular_dual_replacement_mellin_kernel_eq_error_parts (T : ℝ)
    (σ : MomentShifts) (G : ℂ→ℂ) (α : MomentShifts) (t : ℝ)
    (n : Fin 4→ℕ) (z : ℂ) :
    rectangularDualReplacementMellinKernel T σ G α t n z =
      rectangularDualErrorPartMellinKernel false T σ G α t n z+
        rectangularDualErrorPartMellinKernel true T σ G α t n z := by
  simp only [rectangularDualReplacementMellinKernel,rectangularDualErrorPartMellinKernel,
    Bool.false_eq_true,ite_false,ite_true]
  ring

/-- Exact time factorization retains both real amplifier coefficients and all
four literal AFE denominator powers. -/
theorem rectangular_dual_error_part_actual_time_factorization (phasePart : Bool) (T : ℝ)
    (f g Φ : ℝ→ℝ) (σ τ α : MomentShifts) (u v : ℕ) (n : Fin 4→ℕ) (z : ℂ) :
    (∫ t : ℝ, rectangularMomentPairWeight T f g Φ u v t*
      rectangularDualErrorPartMellinKernel phasePart T σ (polarPoleKiller T τ) α t n z)=
      (phaseActualAmplifierPairConstant T f g u v/
        ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+z))*
        a03GaussianDualErrorPartActualTimeIntegral phasePart (fun x => (Φ x:ℂ)) T σ τ α z (u+1) (v+1) n := by
  unfold a03GaussianDualErrorPartActualTimeIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold rectangularDualErrorPartMellinKernel
  simp only [div_eq_mul_inv]
  calc
    _=(rectangularMomentPairWeight T f g Φ u v t*rectangularAFEOscillation t n)*
        (polarPoleKiller T τ z*z⁻¹*(if phasePart then
      (bblrDualMultiplier t (rawMomentShifts T σ)-
        (t/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j))*(t/2:ℂ)^(2*z)
    else bblrDualMultiplier t (rawMomentShifts T σ)*
      (bblrGammaQuotient t α z-(t/2:ℂ)^(2*z)))*(Real.pi:ℂ)^(-2*z))*
        (∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+z))⁻¹ := by ring
    _=_ := by
      rw [rectangular_actual_pair_weight_oscillation]
      unfold phaseActualAmplifierPairConstant
      ring

/-- The actual amplified Mellin error has a uniform rapidly decreasing
frequency budget. The complete arithmetic prefactor is explicit. -/
theorem rectangular_dual_error_part_actual_time_uniform_schwartz_bound
    {Φ : ℝ→ℝ} (hΦ : SmoothDyadicWeight Φ)
    {c ε κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℕ→ℝ, (∀ N, 0≤C N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ τ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot τ j‖) →
      ∀ phasePart : Bool, ∀ v : ℝ, |v|≤θ*Real.log T → ∀ f g : ℝ→ℝ, ∀ u w : ℕ,
      ∀ n : Fin 4→ℕ, ∀ N : ℕ,
      (1+|-T*Real.log (phaseActualProductRatio (u+1) (w+1) n)|)^N*
        ‖∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
          rectangularDualErrorPartMellinKernel phasePart T σ (polarPoleKiller T τ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤
        ‖phaseActualAmplifierPairConstant T f g u w/
          ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+((c:ℂ)+(v:ℂ)*I))‖*C N*T^ε := by
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  obtain ⟨C,hC,hCd⟩ := a03_gaussian_dual_error_part_actual_time_uniform_schwartz_bound hΦc hΦs hc hc1 hε hκ hθ hR
  refine ⟨C,hC,?_⟩
  filter_upwards [hCd] with T hbT
  intro σ τ α hσ hα hroot phasePart v hv f g u w n N
  rw [rectangular_dual_error_part_actual_time_factorization,norm_mul]
  have hb := hbT σ τ α hσ hα hroot phasePart v hv (u+1) (w+1) (by omega) (by omega) n N
  let D : ℝ := ‖phaseActualAmplifierPairConstant T f g u w/
    ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+((c:ℂ)+(v:ℂ)*I))‖
  change (1+|-T*Real.log (phaseActualProductRatio (u+1) (w+1) n)|)^N*
    (D*‖a03GaussianDualErrorPartActualTimeIntegral phasePart (fun x => (Φ x:ℂ)) T σ τ α
      ((c:ℂ)+(v:ℂ)*I) (u+1) (w+1) n‖)≤D*C N*T^ε
  have hD : 0≤D := norm_nonneg _
  calc
    _=D*((1+|-T*Real.log (phaseActualProductRatio (u+1) (w+1) n)|)^N*
      ‖a03GaussianDualErrorPartActualTimeIntegral phasePart (fun x => (Φ x:ℂ)) T σ τ α
        ((c:ℂ)+(v:ℂ)*I) (u+1) (w+1) n‖) := by ring
    _≤D*(C N*T^ε) := mul_le_mul_of_nonneg_left hb hD
    _=_ := by ring

end
end Sechstmoment
