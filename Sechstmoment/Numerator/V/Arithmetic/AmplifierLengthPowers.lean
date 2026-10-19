import Sechstmoment.Numerator.V.Arithmetic.StartingLine

/-! Exact length costs when the kernel error is summed over both amplifiers. -/

namespace Sechstmoment.Source
open Real Set
noncomputable section

theorem amplifier_product_log_power_bound {T R η N : ℝ}
    (hT : 1 < T) (hR : 0 ≤ R) (hN : 0 < N) (hNlen : N ≤ T^(2*η)) :
    N^(noDPRightLine T R-1) ≤ Real.exp (2*η*(R+2)) := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hX : 0 < T^(2*η) := Real.rpow_pos_of_pos hT0 _
  have hpower : (T^(2*η))^((R+2)/Real.log T) = Real.exp (2*η*(R+2)) := by
    rw [Real.rpow_def_of_pos hX,Real.log_rpow hT0]
    congr 1
    field_simp [hL.ne']
  have hexponent : noDPRightLine T R-1 = (R+2)/Real.log T := by
    unfold noDPRightLine
    ring
  rw [hexponent]
  exact (Real.rpow_le_rpow hN.le hNlen (by positivity)).trans_eq hpower

theorem amplifier_pair_indices_length_bound {T η : ℝ} (hT : 0 < T)
    {a b : ℕ} (ha : a < ⌊T^η⌋₊) (hb : b < ⌊T^η⌋₊) :
    0 < (a+1:ℝ)*(b+1:ℝ) ∧ (a+1:ℝ)*(b+1:ℝ) ≤ T^(2*η) := by
  have hX : 0 ≤ T^η := Real.rpow_nonneg hT.le _
  have hfloor : (⌊T^η⌋₊:ℝ) ≤ T^η := Nat.floor_le hX
  have haX : (a+1:ℝ) ≤ T^η :=
    (by exact_mod_cast Nat.succ_le_of_lt ha : (a+1:ℝ) ≤ (⌊T^η⌋₊:ℝ)).trans hfloor
  have hbX : (b+1:ℝ) ≤ T^η :=
    (by exact_mod_cast Nat.succ_le_of_lt hb : (b+1:ℝ) ≤ (⌊T^η⌋₊:ℝ)).trans hfloor
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ T^η*T^η := mul_le_mul haX hbX (by positivity) hX
    _ = T^(2*η) := by rw [← Real.rpow_add hT]; congr 1; ring

end
end Sechstmoment.Source
