import Sechstmoment.Numerator.V.Arithmetic.TimeWeightMellinMass
import Sechstmoment.Numerator.V.EulerTransfer.CorrectedMellin

/-! The corrected Mellin integral with an explicit weight budget.
This exposes the common constant needed for the actual time-weight family. -/

namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory Filter
open scoped ContDiff
noncomputable section

theorem correctedMellin_bound_with_mass (κ β ε : ℝ)
    (hκ : 0 < κ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ → ℂ, ContDiff ℝ ∞ w →
      tsupport w ⊆ Icc (1:ℝ) 2 → ∀ J : ℝ,
      (∫ v : ℝ, (1+|v|)^20*‖mellin w ((κ:ℂ)+(v:ℂ)*I)‖) ≤ J →
      ∀ q : ℕ, ∀ _ : NeZero q, ∀ d : ℕ, d ≠ 0 →
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ min κ (β/2)) →
      (∀ j, κ+(s j).re ∈ Icc (1/2:ℝ) (3/4)) → ∀ x : ℝ, 0 < x →
      Integrable (correctedMellinIntegrand q d w κ s x) ∧
      ‖∫ v : ℝ, correctedMellinIntegrand q d w κ s x v‖ ≤
        C*J*(d:ℝ)^β*(q:ℝ)^(1/2+ε)*x^κ := by
  obtain ⟨A,hA,hbound⟩ := correctedGauss_bound κ β ε hκ hβ hε
  let R := min κ (β/2)
  have hR : 0 ≤ R := le_min hκ.le (by linarith)
  refine ⟨A*(1+R)^20,by positivity,?_⟩
  intro w hw hws J hJ q hq d hd s hs hsr x hx
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
    _ ≤ K*(∫ v : ℝ, (1+|v|)^20*‖mellin w ((κ:ℂ)+(v:ℂ)*I)‖) := hnorm
    _ ≤ K*J := mul_le_mul_of_nonneg_left hJ (by dsimp only [K]; positivity)
    _ = _ := by dsimp only [K]; ring

theorem timeWeight_correctedMellin_uniform_bound {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) (κ β ε : ℝ)
    (hκ : 0 < κ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2*Real.pi ≤ T → 1 ≤ Real.log T →
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ q : ℕ, ∀ _ : NeZero q, ∀ d : ℕ, d ≠ 0 →
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ min κ (β/2)) →
      (∀ j, κ+(s j).re ∈ Icc (1/2:ℝ) (3/4)) → ∀ x : ℝ, 0 < x →
      Integrable (correctedMellinIntegrand q d
        (noDPTimeWeight w T (z/(Real.log T:ℂ))) κ s x) ∧
      ‖∫ v : ℝ, correctedMellinIntegrand q d
        (noDPTimeWeight w T (z/(Real.log T:ℂ))) κ s x v‖ ≤
        C*(d:ℝ)^β*(q:ℝ)^(1/2+ε)*x^κ := by
  obtain ⟨A,hA,hbound⟩ := correctedMellin_bound_with_mass κ β ε hκ hβ hε
  obtain ⟨J,hJ,hmass⟩ := noDPTimeWeight_uniform_weighted_mellin_mass hw hws hR κ 20
  refine ⟨A*J,by positivity,?_⟩
  intro T hT hL z hz q hq d hd s hs hsr x hx
  have : NeZero q := hq
  exact hbound _ (noDPTimeWeight_contDiff hw hws T _)
    ((noDPTimeWeight_tsupport w T _).trans hws) J (hmass T hT hL z hz).2
    q hq d hd s hs hsr x hx

end
end Sechstmoment.Source.NoDPGlobalLFactorization
