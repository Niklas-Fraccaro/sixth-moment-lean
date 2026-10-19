import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Sechstmoment.Numerator.V.DP.DPPhaseControl
import Sechstmoment.Zeta.Moments.SixTerms

/-!
# The actual dyadic outer phase and all six normalized BBLR phases

The substitution t = T x converts the true time integral into an integral
on the fixed weight support.  The actual complex power there equals an
exponential whose logarithmic ratio tends to one.  Dominated convergence
uses the proved dyadic phase window and the integrable fixed weight norm.
-/

namespace Sechstmoment.Source
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

def normalizedDyadicPhase (θ : ℂ) (T x : ℝ) : ℂ :=
  Complex.exp ((Real.log (T*x/(2*Real.pi))/Real.log T : ℝ)*θ)

lemma dyadic_phase_ratio_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ => Real.log (T*x/(2*Real.pi))/Real.log T) atTop (𝓝 1) := by
  have ht : Tendsto (fun T : ℝ => 1 + (Real.log x-Real.log (2*Real.pi))/Real.log T)
      atTop (𝓝 (1+0)) := tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  have ht' : Tendsto (fun T : ℝ => 1 + (Real.log x-Real.log (2*Real.pi))/Real.log T)
      atTop (𝓝 1) := by simpa using ht
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hπ : 0 < 2*Real.pi := by positivity
  rw [Real.log_div (mul_pos hTpos hx).ne' hπ.ne', Real.log_mul hTpos.ne' hx.ne']
  field_simp [(Real.log_pos hT).ne']
  ring

lemma normalizedDyadicPhase_tendsto (θ : ℂ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ => normalizedDyadicPhase θ T x) atTop (𝓝 (Complex.exp θ)) := by
  simpa only [normalizedDyadicPhase,Complex.ofReal_one,one_mul] using
    ((dyadic_phase_ratio_tendsto hx).ofReal.mul_const θ).cexp

lemma smoothDyadicWeight_integrable (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable Φ :=
  hΦ.1.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport Φ) hΦ.2)

lemma normalizedDyadicPhase_integral_tendsto (θ : ℂ) (Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => ∫ x : ℝ, (Φ x:ℂ)*normalizedDyadicPhase θ T x)
      atTop (𝓝 ((∫ x : ℝ, (Φ x:ℂ))*Complex.exp θ)) := by
  have hm (T : ℝ) : AEStronglyMeasurable
      (fun x : ℝ => (Φ x:ℂ)*normalizedDyadicPhase θ T x) volume := by
    apply Measurable.aestronglyMeasurable
    unfold normalizedDyadicPhase
    have hΦm := hΦ.1.continuous.measurable
    fun_prop
  have hb : ∀ᶠ T : ℝ in atTop, ∀ᵐ x : ℝ,
      ‖(Φ x:ℂ)*normalizedDyadicPhase θ T x‖ ≤
        ‖Φ x‖*Real.exp (2*|θ.re|) := by
    filter_upwards [eventually_gt_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop dpPhaseWindowConstant)] with T hT hlog
    filter_upwards [] with x
    by_cases hx : Φ x=0
    · simp [hx]
    have hxs : x ∈ Icc (1:ℝ) 2 := hΦ.2 (subset_tsupport Φ (by simpa [Function.mem_support] using hx))
    have hTpos : 0 < T := zero_lt_one.trans hT
    have hTX : T*x ∈ Icc (T/4) (2*T) := by
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hxs.1 hTpos.le]
      · nlinarith [mul_le_mul_of_nonneg_left hxs.2 hTpos.le]
    have hq := dp_phase_endpoint_in_window hT hlog hTX
    rw [norm_mul,Complex.norm_real,normalizedDyadicPhase,Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    calc
      _ ≤ (Real.log (T*x/(2*Real.pi))/Real.log T)*|θ.re| :=
        mul_le_mul_of_nonneg_left (le_abs_self θ.re) hq.1
      _ ≤ 2*|θ.re| := mul_le_mul_of_nonneg_right hq.2 (abs_nonneg _)
  have hi := ((smoothDyadicWeight_integrable Φ hΦ).norm).mul_const (Real.exp (2*|θ.re|))
  have hl : ∀ᵐ x : ℝ, Tendsto
      (fun T : ℝ => (Φ x:ℂ)*normalizedDyadicPhase θ T x) atTop
      (𝓝 ((Φ x:ℂ)*Complex.exp θ)) := by
    filter_upwards [] with x
    by_cases hx : Φ x=0
    · simp [hx]
    have hxs : x ∈ Icc (1:ℝ) 2 := hΦ.2 (subset_tsupport Φ (by simpa [Function.mem_support] using hx))
    exact tendsto_const_nhds.mul (normalizedDyadicPhase_tendsto θ (by linarith [hxs.1]))
  simpa only [integral_mul_const] using
    tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall hm) hb hi hl


lemma dyadic_phase_cpow_eq_exp {T x : ℝ} (hT : 0 < T) (hx : 0 < x) (θ : ℂ) :
    (T*x/(2*Real.pi):ℂ)^θ = Complex.exp ((Real.log (T*x/(2*Real.pi)):ℝ)*θ) := by
  have hp : 0 < T*x/(2*Real.pi) := by positivity
  rw [show (T*x/(2*Real.pi):ℂ) = ((T*x/(2*Real.pi):ℝ):ℂ) by push_cast; rfl,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le]

/-- An actual dyadic weight times an arbitrary complex power is integrable. -/
theorem dyadicComplexPowerWeight_integrable {T : ℝ} (hT : 0 < T) (θ : ℂ)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t : ℝ => (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^θ) := by
  let H : ℝ → ℂ := fun x => Complex.exp ((Real.log (T*max x (1/2)/(2*Real.pi)):ℝ)*θ)
  have hpos (x : ℝ) : 0 < T*max x (1/2)/(2*Real.pi) := by
    have : 0 < max x (1/2) := lt_of_lt_of_le (by norm_num) (le_max_right x (1/2))
    positivity
  have hH : Continuous H := by
    unfold H
    exact ((Complex.continuous_ofReal.comp
      ((by fun_prop : Continuous (fun x : ℝ => T*max x (1/2)/(2*Real.pi))).log
        (fun x => (hpos x).ne'))).mul continuous_const).cexp
  have hweight : HasCompactSupport (fun x : ℝ => (Φ x:ℂ)) := by
    have hc : HasCompactSupport Φ :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport Φ) hΦ.2
    exact hc.comp_left (g := Complex.ofReal) (by norm_num)
  have hi : Integrable (fun x : ℝ => (Φ x:ℂ)*H x) :=
    ((Complex.continuous_ofReal.comp hΦ.1.continuous).mul hH).integrable_of_hasCompactSupport
      hweight.mul_right
  have hp (x : ℝ) : (Φ x:ℂ)*H x = (Φ x:ℂ)*(T*x/(2*Real.pi):ℂ)^θ := by
    by_cases hx : Φ x=0
    · simp [hx]
    have hxs : x ∈ Icc (1:ℝ) 2 := hΦ.2 (subset_tsupport Φ (by simpa [Function.mem_support] using hx))
    rw [dyadic_phase_cpow_eq_exp hT (by linarith [hxs.1])]
    simp only [H,max_eq_left (by linarith [hxs.1] : (1/2:ℝ) ≤ x)]
  have hi' : Integrable (fun x : ℝ => (Φ x:ℂ)*(T*x/(2*Real.pi):ℂ)^θ) := by
    exact hi.congr (Eventually.of_forall hp)
  have ht := hi'.comp_div hT.ne'
  convert ht using 1
  ext t
  congr 2
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hT.ne']

lemma dyadicComplexPowerWeight_normalized_eq {T : ℝ} (hT : 0<T) (θ : ℂ)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    (∫ t : ℝ, (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(θ/(Real.log T:ℂ)))/(T:ℂ) =
      ∫ x : ℝ, (Φ x:ℂ)*normalizedDyadicPhase θ T x := by
  have hs := Measure.integral_comp_mul_left
    (fun t : ℝ => (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(θ/(Real.log T:ℂ))) T
  rw [abs_of_pos (inv_pos.mpr hT),Complex.real_smul,Complex.ofReal_inv] at hs
  calc
    _ = ∫ x : ℝ, (Φ (T*x/T):ℂ)*(T*x/(2*Real.pi):ℂ)^(θ/(Real.log T:ℂ)) := by
      simpa only [div_eq_mul_inv,mul_comm,Complex.ofReal_mul] using hs.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [mul_div_cancel_left₀ x hT.ne']
      by_cases hx : Φ x=0
      · simp [hx]
      have hxs : x ∈ Icc (1:ℝ) 2 := hΦ.2 (subset_tsupport Φ (by simpa [Function.mem_support] using hx))
      rw [dyadic_phase_cpow_eq_exp hT (by linarith [hxs.1])]
      unfold normalizedDyadicPhase
      congr 2
      push_cast
      ring

/-- The actual normalized outer time factor converges to the weight mass times exp θ. -/
theorem dyadicComplexPowerWeight_normalized_tendsto (θ : ℂ) (Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ =>
      (∫ t : ℝ, (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(θ/(Real.log T:ℂ)))/(T:ℂ))
      atTop (𝓝 ((∫ x : ℝ, (Φ x:ℂ))*Complex.exp θ)) := by
  apply (normalizedDyadicPhase_integral_tendsto θ Φ hΦ).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  exact (dyadicComplexPowerWeight_normalized_eq hT θ Φ hΦ).symm

/-- All six literal source powers scale by the same logarithmic normalization. -/
theorem bblrSixPhaseExponents_raw (T : ℝ) (σ : MomentShifts) (m : Fin 6) :
    bblrSixPhaseExponents (rawMomentShifts T σ) m =
      bblrSixPhaseExponents σ m / (Real.log T:ℂ) := by
  fin_cases m <;> simp [bblrSixPhaseExponents,rawMomentShifts] <;> ring

/-- The actual time factor for each of the six source phases has its claimed limit. -/
theorem bblrSixPhaseWeight_normalized_tendsto (σ : MomentShifts) (m : Fin 6)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ =>
      (∫ t : ℝ, (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^
        (bblrSixPhaseExponents (rawMomentShifts T σ) m))/(T:ℂ))
      atTop (𝓝 ((∫ x : ℝ, (Φ x:ℂ))*Complex.exp (bblrSixPhaseExponents σ m))) := by
  simpa only [bblrSixPhaseExponents_raw] using
    dyadicComplexPowerWeight_normalized_tendsto (bblrSixPhaseExponents σ m) Φ hΦ

end
end Sechstmoment.Source
