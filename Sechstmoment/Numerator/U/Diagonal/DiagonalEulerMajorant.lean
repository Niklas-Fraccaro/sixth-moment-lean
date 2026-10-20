import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Sechstmoment.Arithmetic.Euler.Shifted.Local


namespace Sechstmoment

theorem d3PrimePowerCoefficient_succ_recurrence (m : ℕ) :
    d3PrimePowerCoefficient (m+1)*(m+1) =
      d3PrimePowerCoefficient m*(m+3) := by
  have h := Nat.choose_mul_succ_eq (m+2) 2
  simpa [d3PrimePowerCoefficient, Nat.add_assoc] using h.symm

theorem d9PrimePowerCoefficient_succ_recurrence (m : ℕ) :
    (m+1+8).choose 8*(m+1) = (m+8).choose 8*(m+9) := by
  have h := Nat.choose_mul_succ_eq (m+8) 8
  simpa [Nat.add_assoc] using h.symm

theorem d3PrimePowerCoefficient_sq_le_d9 (m : ℕ) :
    d3PrimePowerCoefficient m ^ 2 ≤ (m+8).choose 8 := by
  induction m with
  | zero => norm_num [d3PrimePowerCoefficient]
  | succ m ih =>
    have h3 := d3PrimePowerCoefficient_succ_recurrence m
    have h9 := d9PrimePowerCoefficient_succ_recurrence m
    have hs : (m+3)^2 ≤ (m+9)*(m+1) := by nlinarith
    have hmul : d3PrimePowerCoefficient (m+1)^2*(m+1)^2 ≤
        (m+1+8).choose 8*(m+1)^2 := by
      calc
        _ = (d3PrimePowerCoefficient m)^2*(m+3)^2 := by
          calc
            _ = (d3PrimePowerCoefficient (m+1)*(m+1))^2 := by ring
            _ = (d3PrimePowerCoefficient m*(m+3))^2 := congrArg (fun n : ℕ => n^2) h3
            _ = _ := by ring
        _ ≤ (m+8).choose 8*((m+9)*(m+1)) := Nat.mul_le_mul ih hs
        _ = (m+1+8).choose 8*(m+1)^2 := by
          nlinarith [h9]
    nlinarith [hmul]

theorem d3PrimePowerCoefficient_sq_le_d9_real (m : ℕ) :
    (d3PrimePowerCoefficient m : ℝ)^2 ≤ ((m+8).choose 8 : ℝ) := by
  exact_mod_cast d3PrimePowerCoefficient_sq_le_d9 m

end Sechstmoment
