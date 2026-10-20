import SixthMoment.Analysis.Mellin.SmoothMellin
import SixthMoment.Numerator.V.Arithmetic.GaussFourLBound


namespace SixthMoment.Source
open Complex Real MeasureTheory Filter Set ZMod
open scoped Topology BigOperators Classical ContDiff
noncomputable section
set_option maxHeartbeats 800000

def gaussMellinIntegrand (q : ℕ) [NeZero q] (w : ℝ → ℂ)
    (κ : ℝ) (α : Fin 4 → ℂ) (x v : ℝ) : ℂ :=
  mellin w ((κ : ℂ)+(v : ℂ)*I) * (x : ℂ)^((κ : ℂ)+(v : ℂ)*I) *
    gaussFourLTransform q (fun j => (κ : ℂ)+(v : ℂ)*I+α j)

theorem gaussFourLTransform_line_continuous (q : ℕ) [NeZero q]
    (κ : ℝ) (α : Fin 4 → ℂ)
    (hα : ∀ j, κ+(α j).re ∈ Icc (1/2 : ℝ) (3/4)) :
    Continuous (fun v : ℝ => gaussFourLTransform q
      (fun j => (κ : ℂ)+(v : ℂ)*I+α j)) := by
  have hL (χ : DirichletCharacter ℂ q) (j : Fin 4) :
      Continuous (fun v : ℝ => χ.LFunction ((κ : ℂ)+(v : ℂ)*I+α j)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hne : (κ : ℂ)+(v : ℂ)*I+α j ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero,one_re] at hr
      linarith [(hα j).2]
    have hc : ContinuousAt (fun t : ℝ => (κ : ℂ)+(t : ℂ)*I+α j) v := by fun_prop
    exact ContinuousAt.comp' (f := fun t : ℝ => (κ : ℂ)+(t : ℂ)*I+α j) (x := v)
      (χ.differentiableAt_LFunction _ (Or.inl hne)).continuousAt hc
  unfold gaussFourLTransform
  fun_prop

theorem gaussMellinIntegrand_continuous {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (q : ℕ) [NeZero q]
    (κ : ℝ) (α : Fin 4 → ℂ) (hα : ∀ j, κ+(α j).re ∈ Icc (1/2 : ℝ) (3/4))
    {x : ℝ} (hx : 0 < x) :
    Continuous (gaussMellinIntegrand q w κ α x) := by
  have hM := smooth_mellin_line_continuous hw hws κ
  have hG := gaussFourLTransform_line_continuous q κ α hα
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hP : Continuous (fun v : ℝ => (x : ℂ)^((κ : ℂ)+(v : ℂ)*I)) := by
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl hxC
  exact (hM.mul hP).mul hG

theorem smooth_gauss_fourL_mellin_bound {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1 : ℝ) 2)
    (κ : ℝ) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ _ : NeZero q,
      ∀ α : Fin 4 → ℂ, (∀ j, κ+(α j).re ∈ Icc (1/2 : ℝ) (3/4)) →
      (∀ j, |(α j).im| ≤ R) → ∀ x : ℝ, 0 < x →
      Integrable (gaussMellinIntegrand q w κ α x) ∧
        ‖∫ v : ℝ, gaussMellinIntegrand q w κ α x v‖ ≤
          C*(q : ℝ)^(1/2+ε)*x^κ := by
  obtain ⟨A,hA,hbound⟩ := allDirichlet_gauss_fourL_bound hε
  let J : ℝ := ∫ v : ℝ, (1+|v|)^20*‖mellin w ((κ : ℂ)+(v : ℂ)*I)‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => by positivity)
  refine ⟨A*(1+R)^20*(J+1),by positivity,?_⟩
  intro q hq α hα hαim x hx
  have : NeZero q := hq
  have hweight := smooth_mellin_weighted_integrable hw hws κ 20
  let K : ℝ := A*(q : ℝ)^(1/2+ε)*x^κ*(1+R)^20
  have hpoint (v : ℝ) : ‖gaussMellinIntegrand q w κ α x v‖ ≤
      K*((1+|v|)^20*‖mellin w ((κ : ℂ)+(v : ℂ)*I)‖) := by
    have hs (j : Fin 4) : ((κ : ℂ)+(v : ℂ)*I+α j).re ∈
        Icc (1/2 : ℝ) (3/4) := by simpa using hα j
    have ht (j : Fin 4) : |((κ : ℂ)+(v : ℂ)*I+α j).im| ≤ |v|+R := by
      simp only [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add]
      exact (abs_add_le v (α j).im).trans (by linarith [hαim j])
    have hb := hbound q hq (fun j => (κ : ℂ)+(v : ℂ)*I+α j) hs
      (|v|+R) (by positivity) ht
    have hp : (1+(|v|+R))^20 ≤ ((1+R)*(1+|v|))^20 := by
      gcongr
      nlinarith [abs_nonneg v]
    have hpow : ‖(x : ℂ)^((κ : ℂ)+(v : ℂ)*I)‖ = x^κ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    unfold gaussMellinIntegrand
    rw [norm_mul,norm_mul,hpow]
    calc
      _ ≤ ‖mellin w ((κ : ℂ)+(v : ℂ)*I)‖*x^κ*
          (A*(q : ℝ)^(1/2+ε)*(1+(|v|+R))^20) := by gcongr
      _ ≤ ‖mellin w ((κ : ℂ)+(v : ℂ)*I)‖*x^κ*
          (A*(q : ℝ)^(1/2+ε)*((1+R)*(1+|v|))^20) := by gcongr
      _ = _ := by dsimp only [K]; rw [mul_pow]; ring
  have hmajor := hweight.const_mul K
  have hInt : Integrable (gaussMellinIntegrand q w κ α x) :=
    hmajor.mono' (gaussMellinIntegrand_continuous hw hws q κ α hα hx).aestronglyMeasurable
      (Eventually.of_forall hpoint)
  refine ⟨hInt,?_⟩
  have hnorm := norm_integral_le_of_norm_le hmajor (Eventually.of_forall hpoint)
  rw [integral_const_mul] at hnorm
  calc
    _ ≤ K*J := hnorm
    _ ≤ K*(J+1) := by dsimp only [K]; gcongr; linarith
    _ = _ := by dsimp only [K]; ring

end
end SixthMoment.Source
