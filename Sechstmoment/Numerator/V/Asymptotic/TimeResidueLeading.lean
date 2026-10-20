import Sechstmoment.Numerator.V.Asymptotic.TimeMellinLeading
import Sechstmoment.Numerator.V.Asymptotic.TimeResidueScale


namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem timeWeight_residue_leading_uniform {w : ℝ → ℂ} (hw : Continuous w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) (R : ℝ) (hR : 0 ≤ R) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 0 < T →
      max 1 ((2*R)*(elementaryPhaseLogBound+1)) ≤ Real.log T →
      ∀ σ z : ℂ, ‖σ‖ ≤ R → ‖z‖ ≤ R →
      ‖mellin (noDPTimeWeight w T (z/(Real.log T:ℂ))) (1-σ/(Real.log T:ℂ))*
          ((T/(2*Real.pi):ℝ):ℂ)^(1-σ/(Real.log T:ℂ))/(T:ℂ)-
        (1/(2*Real.pi):ℂ)*Complex.exp (-(σ+z))*(∫ x : ℝ, w x)‖ ≤ A/Real.log T := by
  obtain ⟨C,hC,HC⟩ := compact_dyadic_mellin_scaled_error hw hws
  let S := 2*R
  let W : ℂ := ∫ x : ℝ, w x
  let D := ‖W‖+C*S+1
  let P := 2*S*elementaryPhaseLogBound
  let K : ℂ := (1/(2*Real.pi):ℂ)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hP : 0 ≤ P := by
    dsimp only [P]
    exact mul_nonneg (by positivity) elementaryPhaseLogBound_pos.le
  refine ⟨‖K‖*Real.exp S*(P*D+C*S)+1,by positivity,?_⟩
  intro T hT hlog σ z hσ hz
  let ν := σ+z
  let E := elementaryCenteredPhase T 1 ν
  let M := mellin w (1-ν/(Real.log T:ℂ))
  have hν : ‖ν‖ ≤ S := (norm_add_le σ z).trans (by dsimp only [S]; linarith)
  have hL1 : 1 ≤ Real.log T := (le_max_left _ _).trans hlog
  have hL0 : 0 < Real.log T := by linarith
  have hlarge : S*(elementaryPhaseLogBound+1) ≤ Real.log T :=
    (le_max_right _ _).trans hlog
  have hSL : S ≤ Real.log T := by
    nlinarith [mul_nonneg hS elementaryPhaseLogBound_pos.le]
  have hphaseLog : max 1 (S*elementaryPhaseLogBound) ≤ Real.log T :=
    max_le hL1 (by nlinarith)
  have hE : ‖E-1‖ ≤ P/Real.log T :=
    elementaryCenteredPhase_error_bound hT (by norm_num) hν hphaseLog
  have hM : ‖M-W‖ ≤ C*S/Real.log T := by
    have H := HC (Real.log T) hL0 (-ν) (by simpa only [norm_neg] using hν.trans hSL)
    have H' : ‖M-W‖ ≤ C*‖ν‖/Real.log T := by
      simpa only [neg_div,← sub_eq_add_neg,norm_neg] using H
    exact H'.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hν hC.le) hL0.le)
  have hMn : ‖M‖ ≤ D := by
    calc
      _ = ‖(M-W)+W‖ := by rw [sub_add_cancel]
      _ ≤ ‖M-W‖+‖W‖ := norm_add_le _ _
      _ ≤ C*S/Real.log T+‖W‖ := add_le_add hM le_rfl
      _ ≤ D := by dsimp only [D]; linarith [div_le_self (mul_nonneg hC.le hS) hL1]
  have hdiff : ‖E*M-W‖ ≤ (P*D+C*S)/Real.log T := by
    rw [show E*M-W = (E-1)*M+(M-W) by ring]
    calc
      _ ≤ ‖(E-1)*M‖+‖M-W‖ := norm_add_le _ _
      _ ≤ (P/Real.log T)*D+C*S/Real.log T := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul hE hMn (norm_nonneg M)
          (div_nonneg hP hL0.le)) hM
      _ = _ := by ring
  have hexp : ‖Complex.exp (-ν)‖ ≤ Real.exp S := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    exact (Complex.re_le_norm (-ν)).trans (by simpa only [norm_neg] using hν)
  rw [timeWeight_residue_centered_scale w hT σ z]
  change ‖K*Complex.exp (-ν)*E*M-K*Complex.exp (-ν)*W‖ ≤ _
  rw [show K*Complex.exp (-ν)*E*M-K*Complex.exp (-ν)*W =
    K*Complex.exp (-ν)*(E*M-W) by ring,norm_mul,norm_mul]
  calc
    _ ≤ (‖K‖*Real.exp S)*((P*D+C*S)/Real.log T) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hexp (norm_nonneg K)) hdiff
        (norm_nonneg _) (by positivity)
    _ = (‖K‖*Real.exp S*(P*D+C*S))/Real.log T := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hL0.le

end
end Sechstmoment.Source
