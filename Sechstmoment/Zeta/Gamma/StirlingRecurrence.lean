import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Sechstmoment.Zeta.Gamma.StirlingStep

/-! Exact finite Gamma/Stirling recurrence in the right half-plane. -/

namespace Sechstmoment.Source
open Complex Real
open scoped BigOperators
noncomputable section

def gammaStirlingFactor (s : ℂ) : ℂ :=
  Complex.Gamma s*Complex.exp (s-(s-1/2)*Complex.log s)

theorem log_add_one_right_half_plane (s : ℂ) (hs : 0 < s.re) :
    Complex.log (s+1) = Complex.log s+Complex.log (1+s⁻¹) := by
  have hs0 : s ≠ 0 := by intro h; simp only [h,zero_re] at hs; linarith
  have hi : 0 < (s⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hs (Complex.normSq_pos.mpr hs0)
  have hy : 0 < (1+s⁻¹).re := by simp only [add_re,one_re]; linarith
  have hy0 : 1+s⁻¹ ≠ 0 := by intro h; simp only [h,zero_re] at hy; linarith
  have hxarg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hs))
  have hyarg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  have H := (Complex.log_mul_eq_add_log_iff hs0 hy0).mpr
    (show s.arg+(1+s⁻¹).arg ∈ Set.Ioc (-Real.pi) Real.pi from
      ⟨by linarith [hxarg.1,hyarg.1],by linarith [hxarg.2,hyarg.2]⟩)
  have he : s*(1+s⁻¹) = s+1 := by field_simp [hs0]
  rw [he] at H
  exact H

theorem gammaStirlingFactor_step (s : ℂ) (hs : 0 < s.re) :
    gammaStirlingFactor s = gammaStirlingFactor (s+1)*Complex.exp (stirlingStepError s) := by
  have hs0 : s ≠ 0 := by intro h; simp only [h,zero_re] at hs; linarith
  have hlog := log_add_one_right_half_plane s hs
  unfold gammaStirlingFactor stirlingStepError
  rw [Complex.Gamma_add_one s hs0,hlog,mul_assoc,← Complex.exp_add]
  have he : (s+1-(s+1-1/2)*(Complex.log s+Complex.log (1+s⁻¹)))+
      ((s+1/2)*Complex.log (1+s⁻¹)-1) =
        (s-(s-1/2)*Complex.log s)-Complex.log s := by ring
  rw [he,Complex.exp_sub (s-(s-1/2)*Complex.log s) (Complex.log s),Complex.exp_log hs0]
  field_simp [hs0]

theorem gammaStirlingFactor_iterate (s : ℂ) (hs : 0 < s.re) (N : ℕ) :
    gammaStirlingFactor s = gammaStirlingFactor (s+N)*
      Complex.exp (∑ k ∈ Finset.range N, stirlingStepError (s+k)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hsn : 0 < (s+(n:ℂ)).re := by simp only [add_re,natCast_re]; positivity
    calc
      _ = gammaStirlingFactor (s+n)*
          Complex.exp (∑ k ∈ Finset.range n, stirlingStepError (s+k)) := ih
      _ = (gammaStirlingFactor ((s+n)+1)*Complex.exp (stirlingStepError (s+n)))*
          Complex.exp (∑ k ∈ Finset.range n, stirlingStepError (s+k)) := by
        rw [gammaStirlingFactor_step (s+n) hsn]
      _ = _ := by
        simp only [Finset.sum_range_succ,Complex.exp_add,Nat.cast_succ,add_assoc]
        ring

end
end Sechstmoment.Source
