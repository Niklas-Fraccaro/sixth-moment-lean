import Sechstmoment.Numerator.U.MainTerm.DyadicSixPhaseLimit
import Sechstmoment.Numerator.U.MainTerm.MovingPolarFactors

/-! Joint limits for the actual outer dyadic time factors. -/
namespace Sechstmoment.Source
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem normalizedDyadicPhase_moving_tendsto
    {ι : Type*} {l : Filter ι} {T : ι → ℝ} {θ : ι → ℂ} {θ₀ : ℂ}
    (hT : Tendsto T l atTop) (hθ : Tendsto θ l (𝓝 θ₀)) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun i => normalizedDyadicPhase (θ i) (T i) x) l (𝓝 (Complex.exp θ₀)) := by
  simpa only [Function.comp_def,normalizedDyadicPhase,Complex.ofReal_one,one_mul] using
    (((dyadic_phase_ratio_tendsto hx).comp hT).ofReal.mul hθ).cexp

theorem normalizedDyadicPhase_integral_moving_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {T : ι → ℝ} {θ : ι → ℂ} {θ₀ : ℂ}
    (hT : Tendsto T l atTop) (hθ : Tendsto θ l (𝓝 θ₀))
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun i => ∫ x : ℝ, (Φ x:ℂ)*normalizedDyadicPhase (θ i) (T i) x) l
      (𝓝 ((∫ x : ℝ, (Φ x:ℂ))*Complex.exp θ₀)) := by
  let M : ℝ := ‖θ₀‖+1
  have hm (i : ι) : AEStronglyMeasurable
      (fun x : ℝ => (Φ x:ℂ)*normalizedDyadicPhase (θ i) (T i) x) volume := by
    apply Measurable.aestronglyMeasurable
    unfold normalizedDyadicPhase
    have hΦm := hΦ.1.continuous.measurable
    fun_prop
  have hb : ∀ᶠ i in l, ∀ᵐ x : ℝ,
      ‖(Φ x:ℂ)*normalizedDyadicPhase (θ i) (T i) x‖ ≤
        ‖Φ x‖*Real.exp (2*M) := by
    filter_upwards [hT.eventually (eventually_gt_atTop (1:ℝ)),
      (Real.tendsto_log_atTop.comp hT).eventually (eventually_ge_atTop dpPhaseWindowConstant),
      hθ.norm.eventually (eventually_lt_nhds (by dsimp [M]; linarith : ‖θ₀‖ < M))]
      with i hTi hlog hθi
    filter_upwards [] with x
    by_cases hx : Φ x=0
    · simp [hx]
    have hxs : x ∈ Icc (1:ℝ) 2 :=
      hΦ.2 (subset_tsupport Φ (by simpa [Function.mem_support] using hx))
    have hTp : 0 < T i := zero_lt_one.trans hTi
    have hTX : T i*x ∈ Icc (T i/4) (2*T i) := by
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hxs.1 hTp.le]
      · nlinarith [mul_le_mul_of_nonneg_left hxs.2 hTp.le]
    have hq := dp_phase_endpoint_in_window hTi hlog hTX
    rw [norm_mul,Complex.norm_real,normalizedDyadicPhase,Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    calc
      _ ≤ (Real.log (T i*x/(2*Real.pi))/Real.log (T i))*|(θ i).re| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hq.1
      _ ≤ 2*|(θ i).re| := mul_le_mul_of_nonneg_right hq.2 (abs_nonneg _)
      _ ≤ 2*M := mul_le_mul_of_nonneg_left
        ((Complex.abs_re_le_norm _).trans hθi.le) (by norm_num)
  have hi := ((smoothDyadicWeight_integrable Φ hΦ).norm).mul_const (Real.exp (2*M))
  have hl : ∀ᵐ x : ℝ, Tendsto
      (fun i => (Φ x:ℂ)*normalizedDyadicPhase (θ i) (T i) x) l
      (𝓝 ((Φ x:ℂ)*Complex.exp θ₀)) := by
    filter_upwards [] with x
    by_cases hx : Φ x=0
    · simp only [hx,Complex.ofReal_zero,zero_mul]
      exact tendsto_const_nhds
    have hxs : x ∈ Icc (1:ℝ) 2 :=
      hΦ.2 (subset_tsupport Φ (by simpa [Function.mem_support] using hx))
    exact tendsto_const_nhds.mul
      (normalizedDyadicPhase_moving_tendsto hT hθ (by linarith [hxs.1]))
  simpa only [integral_mul_const] using
    tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall hm) hb hi hl

theorem dyadicComplexPowerWeight_normalized_moving_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {T : ι → ℝ} {θ : ι → ℂ} {θ₀ : ℂ}
    (hT : Tendsto T l atTop) (hθ : Tendsto θ l (𝓝 θ₀))
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun i =>
      (∫ t : ℝ, (Φ (t/T i):ℂ)*(t/(2*Real.pi):ℂ)^(θ i/(Real.log (T i):ℂ)))/(T i:ℂ))
      l (𝓝 ((∫ x : ℝ, (Φ x:ℂ))*Complex.exp θ₀)) := by
  apply (normalizedDyadicPhase_integral_moving_tendsto hT hθ Φ hΦ).congr'
  filter_upwards [hT.eventually (eventually_gt_atTop (0:ℝ))] with i hTi
  exact (dyadicComplexPowerWeight_normalized_eq hTi (θ i) Φ hΦ).symm

theorem bblrSixPhaseWeight_normalized_moving_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {T : ι → ℝ} {σ : ι → MomentShifts} {σ₀ : MomentShifts}
    (hT : Tendsto T l atTop) (hσ : Tendsto σ l (𝓝 σ₀)) (m : Fin 6)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun i =>
      (∫ t : ℝ, (Φ (t/T i):ℂ)*(t/(2*Real.pi):ℂ)^
        (bblrSixPhaseExponents (rawMomentShifts (T i) (σ i)) m))/(T i:ℂ)) l
      (𝓝 ((∫ x : ℝ, (Φ x:ℂ))*Complex.exp (bblrSixPhaseExponents σ₀ m))) := by
  simpa only [Function.comp_def,bblrSixPhaseExponents_raw] using
    dyadicComplexPowerWeight_normalized_moving_tendsto hT
      ((bblrSixPhaseExponents_continuous m).tendsto σ₀ |>.comp hσ) Φ hΦ

end
end Sechstmoment.Source
