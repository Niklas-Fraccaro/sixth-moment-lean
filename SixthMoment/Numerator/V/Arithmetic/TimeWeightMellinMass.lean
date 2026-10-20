import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import SixthMoment.Analysis.Mellin.SmoothMellin
import SixthMoment.Numerator.V.Arithmetic.TimeWeightFamily


namespace SixthMoment.Source
open Complex Real Set MeasureTheory
open scoped ContDiff
noncomputable section

theorem noDPTimeWeight_uniform_weighted_mellin_mass {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) (κ : ℝ) (k : ℕ) :
    ∃ J : ℝ, 0 < J ∧ ∀ T : ℝ, 2*Real.pi ≤ T → 1 ≤ Real.log T →
      ∀ z : ℂ, ‖z‖ ≤ R →
      Integrable (fun v : ℝ => (1+|v|)^k*
        ‖mellin (noDPTimeWeight w T (z/(Real.log T:ℂ))) ((κ:ℂ)+(v:ℂ)*I)‖) ∧
      (∫ v : ℝ, (1+|v|)^k*
        ‖mellin (noDPTimeWeight w T (z/(Real.log T:ℂ))) ((κ:ℂ)+(v:ℂ)*I)‖) ≤ J := by
  obtain ⟨D,hD,hdecay⟩ := noDPTimeWeight_uniform_mellin_decay hw hws hR κ (k+2)
  refine ⟨D*Real.pi+1,by positivity,?_⟩
  intro T hT hL z hz
  have hwsT : tsupport (noDPTimeWeight w T (z/(Real.log T:ℂ))) ⊆ Icc (1:ℝ) 2 :=
    (noDPTimeWeight_tsupport w T _).trans hws
  have hweight := smooth_mellin_weighted_integrable
    (noDPTimeWeight_contDiff hw hws T _) hwsT κ k
  have hmajor : Integrable (fun v : ℝ => D*(1+v^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul D
  have hpoint (v : ℝ) : (1+|v|)^k*
      ‖mellin (noDPTimeWeight w T (z/(Real.log T:ℂ))) ((κ:ℂ)+(v:ℂ)*I)‖ ≤
        D*(1+v^2)⁻¹ := by
    have hpoly : 1+v^2 ≤ (1+|v|)^2 := by nlinarith [sq_abs v,abs_nonneg v]
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < 1+v^2)).mpr
    calc
      _ ≤ ((1+|v|)^k*
          ‖mellin (noDPTimeWeight w T (z/(Real.log T:ℂ))) ((κ:ℂ)+(v:ℂ)*I)‖)*
            (1+|v|)^2 := mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = (1+|v|)^(k+2)*
          ‖mellin (noDPTimeWeight w T (z/(Real.log T:ℂ))) ((κ:ℂ)+(v:ℂ)*I)‖ := by
        rw [pow_add]
        ring
      _ ≤ D := hdecay T hT hL z hz v
  refine ⟨hweight,?_⟩
  calc
    _ ≤ ∫ v : ℝ, D*(1+v^2)⁻¹ := integral_mono hweight hmajor hpoint
    _ = D*Real.pi := by rw [integral_const_mul,integral_univ_inv_one_add_sq]
    _ ≤ D*Real.pi+1 := by linarith

end
end SixthMoment.Source
