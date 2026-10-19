import Sechstmoment.Numerator.V.EulerTransfer.CorrectedGauss

/-! Absolute convergence and uniform bounds for the actual corrected displaced Mellin integral. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open Complex Real MeasureTheory Filter Set ZMod
open scoped Topology BigOperators Classical ContDiff
noncomputable section

def correctedMellinIntegrand (q : ℕ) [NeZero q] (d : ℕ) (w : ℝ → ℂ)
    (κ : ℝ) (s : Fin 4 → ℂ) (x v : ℝ) : ℂ :=
  mellin w ((κ:ℂ)+(v:ℂ)*I) * (x:ℂ)^((κ:ℂ)+(v:ℂ)*I) *
    correctedGaussTransform q d s ((κ:ℂ)+(v:ℂ)*I)

theorem correctedMellin_continuous {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) (q : ℕ) [NeZero q] (d : ℕ)
    (κ : ℝ) (s : Fin 4 → ℂ) (H : ∀ j, κ+(s j).re ∈ Icc (1/2:ℝ) (3/4))
    (x : ℝ) (hx : 0 < x) : Continuous (correctedMellinIntegrand q d w κ s x) := by
  have hM := smooth_mellin_line_continuous hw hws κ
  have hG := correctedGauss_line_continuous q d s κ H
  have hP : Continuous (fun v : ℝ => (x:ℂ)^((κ:ℂ)+(v:ℂ)*I)) := by
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')
  exact (hM.mul hP).mul hG

theorem correctedMellin_bound {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) (κ β ε : ℝ)
    (hκ : 0 < κ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ _ : NeZero q, ∀ d : ℕ, d ≠ 0 →
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ min κ (β/2)) →
      (∀ j, κ+(s j).re ∈ Icc (1/2:ℝ) (3/4)) → ∀ x : ℝ, 0 < x →
      Integrable (correctedMellinIntegrand q d w κ s x) ∧
      ‖∫ v : ℝ, correctedMellinIntegrand q d w κ s x v‖ ≤
        C*(d:ℝ)^β*(q:ℝ)^(1/2+ε)*x^κ := by
  obtain ⟨A,hA,hbound⟩ := correctedGauss_bound κ β ε hκ hβ hε
  let R := min κ (β/2)
  have hR : 0 ≤ R := le_min hκ.le (by linarith)
  let J : ℝ := ∫ v : ℝ, (1+|v|)^20*‖mellin w ((κ:ℂ)+(v:ℂ)*I)‖
  have hJ : 0 ≤ J := integral_nonneg (fun _ => by positivity)
  refine ⟨A*(1+R)^20*(J+1),by positivity,?_⟩
  intro q hq d hd s hs hsr x hx
  have : NeZero q := hq
  have hweight := smooth_mellin_weighted_integrable hw hws κ 20
  let K := A*(d:ℝ)^β*(q:ℝ)^(1/2+ε)*x^κ*(1+R)^20
  have hpoint (v : ℝ) : ‖correctedMellinIntegrand q d w κ s x v‖ ≤
      K*((1+|v|)^20*‖mellin w ((κ:ℂ)+(v:ℂ)*I)‖) := by
    have hreal (j : Fin 4) : ((κ:ℂ)+(v:ℂ)*I+s j).re ∈ Icc (1/2:ℝ) (3/4) := by
      simpa using hsr j
    have him (j : Fin 4) : |((κ:ℂ)+(v:ℂ)*I+s j).im| ≤ |v|+R := by
      simp only [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add]
      have hj : |(s j).im| ≤ R := (abs_im_le_norm (s j)).trans (hs j)
      linarith [abs_add_le v (s j).im]
    have hb := hbound q hq d hd s hs _ (by simp) hreal (|v|+R) (by positivity) him
    have hp : (1+(|v|+R))^20 ≤ ((1+R)*(1+|v|))^20 := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [abs_nonneg v]
    have hpow : ‖(x:ℂ)^((κ:ℂ)+(v:ℂ)*I)‖ = x^κ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    unfold correctedMellinIntegrand
    rw [norm_mul,norm_mul,hpow]
    calc
      _ ≤ ‖mellin w ((κ:ℂ)+(v:ℂ)*I)‖*x^κ*
          (A*(d:ℝ)^β*(q:ℝ)^(1/2+ε)*(1+(|v|+R))^20) := by gcongr
      _ ≤ ‖mellin w ((κ:ℂ)+(v:ℂ)*I)‖*x^κ*
          (A*(d:ℝ)^β*(q:ℝ)^(1/2+ε)*((1+R)*(1+|v|))^20) := by gcongr
      _ = _ := by dsimp only [K]; rw [mul_pow]; ring
  have hmajor := hweight.const_mul K
  have hInt : Integrable (correctedMellinIntegrand q d w κ s x) :=
    hmajor.mono' (correctedMellin_continuous hw hws q d κ s hsr x hx).aestronglyMeasurable
      (Eventually.of_forall hpoint)
  refine ⟨hInt,?_⟩
  have hnorm := norm_integral_le_of_norm_le hmajor (Eventually.of_forall hpoint)
  rw [integral_const_mul] at hnorm
  calc
    _ ≤ K*J := hnorm
    _ ≤ K*(J+1) := by dsimp only [K]; gcongr; linarith
    _ = _ := by dsimp only [K]; ring

end
end Sechstmoment.Source.NoDPGlobalLFactorization
