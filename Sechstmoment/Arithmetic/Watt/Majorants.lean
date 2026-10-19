import Sechstmoment.Arithmetic.Watt.Partition

/-! Numerical bounds used in summing completed Watt blocks. -/

namespace DivisorProof
namespace Watt41
open Real Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

theorem Scales.QX_le_product_sq {p : WattScales} {L : ℝ}
    (hH : 1 ≤ p.H) (hC : 1 ≤ p.C) (hR : 1 ≤ p.R) (hS : 1 ≤ p.S)
    (hV : 1 ≤ p.V) (hP : 1 ≤ p.P) (hL : 1 ≤ L) :
    (completedScales p L).Q*(completedScales p L).X ≤ p.product^2 := by
  have hprod : 1 ≤ p.product := by
    unfold WattScales.product
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hR hS) hV) hP
  have hRS : 1 ≤ p.R*p.S := one_le_mul_of_one_le_of_one_le hR hS
  have hden : 1 ≤ p.H*p.C*L := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hH hC) hL
  have hroot : Real.sqrt (p.R/(p.H*p.C*L)) ≤ p.R := by
    apply (Real.sqrt_le_left (by linarith : 0 ≤ p.R)).mpr
    apply (div_le_iff₀ (by positivity : 0 < p.H*p.C*L)).mpr
    have hr2 : p.R ≤ p.R^2 := by nlinarith
    exact hr2.trans (le_mul_of_one_le_right (by positivity) hden)
  have hX : (completedScales p L).X ≤ p.product := by
    calc _ ≤ p.R*p.S*p.P := by
          dsimp [completedScales,Scales.X]
          gcongr
      _ ≤ p.product := by
        unfold WattScales.product
        nlinarith [mul_nonneg (by positivity : 0 ≤ p.R*p.S*p.P) (sub_nonneg.mpr hV)]
  have hQ : (completedScales p L).Q ≤ p.product := by
    dsimp [completedScales,Scales.Q,WattScales.product]
    nlinarith [one_le_mul_of_one_le_of_one_le hV hP]
  simpa only [pow_two] using
    mul_le_mul hQ hX (by dsimp [completedScales,Scales.X]; positivity) (by positivity)

theorem blockScale_sqrt_le {A : ℝ} (_hA : 0 ≤ A) (j : ℕ) :
    Real.sqrt (blockScale A j) ≤ Real.sqrt A*(7/8 : ℝ)^j := by
  have hr : Real.sqrt (3/4 : ℝ) ≤ 7/8 :=
    (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 7/8)).mpr (by norm_num)
  induction j with
  | zero => simp
  | succ j ih =>
    rw [blockScale_succ,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3/4),pow_succ]
    calc _ ≤ (7/8)*((Real.sqrt A)*(7/8 : ℝ)^j) :=
        mul_le_mul hr ih (Real.sqrt_nonneg _) (by norm_num)
      _ = _ := by ring

/-- An absolute bound for the square-root mass of every finite block family. -/
theorem sum_blockScale_sqrt_le {A : ℝ} (hA : 0 ≤ A) (N : ℕ) :
    (∑ j ∈ range N, Real.sqrt (blockScale A j)) ≤ 8*Real.sqrt A := by
  have hgeo : (∑ j ∈ range N, (7/8 : ℝ)^j) = 8*(1-(7/8 : ℝ)^N) := by
    rw [geom_sum_eq (by norm_num : (7/8 : ℝ) ≠ 1)]
    ring
  calc _ ≤ ∑ j ∈ range N, Real.sqrt A*(7/8 : ℝ)^j :=
      sum_le_sum fun j _ => blockScale_sqrt_le hA j
    _ = Real.sqrt A*(8*(1-(7/8 : ℝ)^N)) := by rw [← mul_sum,hgeo]
    _ ≤ 8*Real.sqrt A := by
      have hnonneg := mul_nonneg (Real.sqrt_nonneg A)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 7/8) N)
      nlinarith

end
end Watt41
end DivisorProof
