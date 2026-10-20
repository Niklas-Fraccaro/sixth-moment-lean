import Sechstmoment.Numerator.U.Replacement.DualPhaseError
import Sechstmoment.Numerator.U.Replacement.TimeGammaErrorGaussian
import Sechstmoment.Numerator.U.Separation.Frequency.GammaProfile

namespace Sechstmoment.Source
open Sechstmoment Complex Set Metric Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000

def bblrDualLeadingMultiplier (T : ℝ) (σ : MomentShifts) (y : ℝ) : ℂ :=
  (T*y/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j)

def bblrDualPhaseTimeError (T : ℝ) (σ : MomentShifts) (y : ℝ) : ℂ :=
  bblrDualMultiplier (T*y) (rawMomentShifts T σ)-bblrDualLeadingMultiplier T σ y

def bblrGaussianDualReplacementAmplitude (T : ℝ) (σ τ α : MomentShifts)
    (z : ℂ) (y : ℝ) : ℂ :=
  (polarPoleKiller T τ z/z*(Real.pi:ℂ)^(-2*z))*
    (bblrDualMultiplier (T*y) (rawMomentShifts T σ)*bblrGammaQuotient (T*y) α z-
      bblrDualLeadingMultiplier T σ y*(T*y/2:ℂ)^(2*z))

theorem bblrGaussianDualReplacementAmplitude_exact_split (T : ℝ)
    (σ τ α : MomentShifts) (z : ℂ) :
    bblrGaussianDualReplacementAmplitude T σ τ α z = fun y =>
      bblrDualMultiplier (T*y) (rawMomentShifts T σ)*bblrGaussianTimeReplacementAmplitude T τ α z y+
      bblrDualPhaseTimeError T σ y*
        (bblrGaussianTimeAmplitude T τ α z y-bblrGaussianTimeReplacementAmplitude T τ α z y) := by
  funext y
  unfold bblrGaussianDualReplacementAmplitude bblrDualPhaseTimeError
    bblrGaussianTimeAmplitude bblrGaussianTimeReplacementAmplitude
  ring

private theorem dual_error_contDiffAt {T R : ℝ} (hR : 0≤R) (hL : 1≤Real.log T)
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

theorem a03_pointwise_product_derivative_budget {A G : ℝ→ℂ}
    {E B : ℕ→ℝ} (hE : ∀ n, 0≤E n) (_hB : ∀ n, 0≤B n)
    {D F : ℝ} (hD : 0≤D) (_hF : 0≤F) {x : ℝ}
    (hA : ContDiffAt ℝ ∞ A x) (hG : ContDiffAt ℝ ∞ G x)
    (hAd : ∀ n, ‖iteratedDeriv n A x‖≤E n*D)
    (hGd : ∀ n, ‖iteratedDeriv n G x‖≤B n*F) (n : ℕ) :
    ‖iteratedDeriv n (fun y => A y*G y) x‖≤a03ProfileProductDerivativeBudget E B n*(D*F) := by
  rw [iteratedDeriv_fun_mul (hA.of_le (by simp)) (hG.of_le (by simp))]
  calc
    _≤∑ i∈Finset.range (n+1), ‖(n.choose i:ℂ)*iteratedDeriv i A x*iteratedDeriv (n-i) G x‖ := norm_sum_le _ _
    _≤∑ i∈Finset.range (n+1), (n.choose i:ℝ)*(E i*D)*(B (n-i)*F) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [norm_mul,Complex.norm_natCast]
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hAd i) (Nat.cast_nonneg _)
      · exact hGd (n-i)
      · exact norm_nonneg _
      · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hE i) hD)
    _=_ := by
      unfold a03ProfileProductDerivativeBudget
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem bblrGaussianDualReplacementAmplitude_logarithmic_uniform_subpower_derivatives
    {c ε κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ)
    (hθ : 0≤θ) (hR : 0≤R) :
    ∃ P : ℕ→ℝ, (∀ n, 0≤P n) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ τ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) →
      (∀ k : PurePolarIndex, κ≤‖normalizedPurePolarRoot τ k‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ x : ℝ, x∈Icc (1:ℝ) 2 →
      ContDiffAt ℝ ∞ (bblrGaussianDualReplacementAmplitude T σ τ α ((c:ℂ)+(v:ℂ)*I)) x ∧
      ∀ n : ℕ, ‖iteratedDeriv n (bblrGaussianDualReplacementAmplitude T σ τ α ((c:ℂ)+(v:ℂ)*I)) x‖≤P n*T^(ε-1) := by
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
  intro σ τ α hσ hα hroot v hv x hx
  have hT0 : 0<T := by linarith
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  let A : ℝ→ℂ := fun y => bblrDualMultiplier (T*y) (rawMomentShifts T σ)
  let D : ℝ→ℂ := bblrDualPhaseTimeError T σ
  let G : ℝ→ℂ := bblrGaussianTimeAmplitude T τ α z
  let Q : ℝ→ℂ := bblrGaussianTimeReplacementAmplitude T τ α z
  have hAc : ContDiffAt ℝ ∞ A x := (bblrDualMultiplier_normalizedTime_contDiffAt hR hL hRT σ hσ hx).of_le (by simp)
  have hDc : ContDiffAt ℝ ∞ D x := (dual_error_contDiffAt hR hL hRT σ hσ hx).of_le (by simp)
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
  rw [bblrGaussianDualReplacementAmplitude_exact_split]
  change ContDiffAt ℝ ∞ (fun y => A y*Q y+D y*(G y-Q y)) x ∧ _
  refine ⟨hAQc.add hDSQc,?_⟩
  intro n
  rw [iteratedDeriv_fun_add (hAQc.of_le (by simp)) (hDSQc.of_le (by simp))]
  have h1 := a03_pointwise_product_derivative_budget hE hH (by norm_num : (0:ℝ)≤1)
    (Real.rpow_nonneg hT0.le _) hAc hQc hAd hQd n
  have h2 := a03_pointwise_product_derivative_budget hF hJ (by positivity : 0≤1/T)
    (Real.rpow_nonneg hT0.le _) hDc (hGc.sub hQc) hDd hSQd n
  have he : (1/T)*T^ε=T^(ε-1) := by rw [Real.rpow_sub hT0,Real.rpow_one]; ring
  rw [he] at h2
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by dsimp [P]; ring))

end
end Sechstmoment.Source
