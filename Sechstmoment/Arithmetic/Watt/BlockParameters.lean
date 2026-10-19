import Sechstmoment.Arithmetic.Watt.OscillatoryBlocks

/-! All scale and large-X checks for a completed block, derived from the
original three size hypotheses. -/

namespace DivisorProof
namespace Watt41
open Real Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem blockScale_le {A : ℝ} (hA : 0 ≤ A) (i : ℕ) : blockScale A i ≤ A := by
  simpa only [blockScale_zero] using blockScale_antitone hA (Nat.zero_le i)

theorem blockScales_sizes {p : WattScales} {A : ℝ} (hp : ∀ i, 1 ≤ p.size i)
    {i j k : ℕ} (hi : 1 ≤ blockScale p.H i) (hj : 1 ≤ blockScale p.C j)
    (hk : 1 ≤ blockScale A k) : ∀ n, 1 ≤ (blockScales p A i j k).size n := by
  intro n
  fin_cases n
  · exact hi
  · exact hj
  · exact hk
  · exact hp 5
  · exact hp 2
  · exact hp 3

theorem blockScales_size_conditions {p : WattScales} {A : ℝ}
    (hH : 0 < p.H) (hC : 0 < p.C) (hA : 0 < A)
    (hfirst : p.H^2*p.C ≤ (p.R*p.S)^2) (hsecond : A ≤ (p.R*p.S)^2)
    (i j k : ℕ) :
    max ((blockScales p A i j k).H^2*(blockScales p A i j k).K)
      (blockScales p A i j k).L ≤ (blockScales p A i j k).Q^2 := by
  apply max_le
  · apply le_trans _ hfirst
    change (blockScale p.H i)^2*blockScale p.C j ≤ p.H^2*p.C
    exact mul_le_mul (pow_le_pow_left₀ (blockScale_pos hH i).le (blockScale_le hH.le i) 2)
      (blockScale_le hC.le j) (blockScale_pos hC j).le (sq_nonneg p.H)
  · exact (blockScale_le hA.le k).trans hsecond

theorem blockScales_X_ge_completed {p : WattScales} {A : ℝ}
    (hH : 0 < p.H) (hC : 0 < p.C) (hA : 0 < A)
    (hR : 0 ≤ p.R) (hS : 0 ≤ p.S) (hP : 0 ≤ p.P) (i j k : ℕ) :
    (completedScales p A).X ≤ (blockScales p A i j k).X := by
  unfold Scales.X
  change Real.sqrt (p.R/(p.H*p.C*A))*p.S*p.P ≤
    Real.sqrt (p.R/(blockScale p.H i*blockScale p.C j*blockScale A k))*p.S*p.P
  apply mul_le_mul_of_nonneg_right _ hP
  apply mul_le_mul_of_nonneg_right _ hS
  apply Real.sqrt_le_sqrt
  have hHC : blockScale p.H i*blockScale p.C j ≤ p.H*p.C :=
    mul_le_mul (blockScale_le hH.le i) (blockScale_le hC.le j) (blockScale_pos hC j).le hH.le
  exact div_le_div_of_nonneg_left hR
    (mul_pos (mul_pos (blockScale_pos hH i) (blockScale_pos hC j)) (blockScale_pos hA k))
    (mul_le_mul hHC (blockScale_le hA.le k) (blockScale_pos hA k).le (mul_pos hH hC).le)

def dualLength (p : WattScales) (E : ℝ) : ℝ := (p.S*p.P/p.V)*E

theorem dualLength_pos {p : WattScales} {E : ℝ}
    (hS : 0 < p.S) (hP : 0 < p.P) (hV : 0 < p.V) (hE : 0 < E) :
    0 < dualLength p E := by unfold dualLength; positivity

theorem completedScales_X_sq_mul_E {p : WattScales} {E : ℝ}
    (hH : 0 < p.H) (hC : 0 < p.C) (hR : 0 ≤ p.R)
    (hS : 0 < p.S) (hP : 0 < p.P) (hV : 0 < p.V) (hE : 0 < E) :
    (completedScales p (dualLength p E)).X^2*E = p.X^2 := by
  have hA := dualLength_pos hS hP hV hE
  have hprod : 0 ≤ p.product := by unfold WattScales.product; positivity
  rw [completedScales_X_sq hH hC hR hV hA hprod]
  have hc : (p.S*p.P/(p.V*dualLength p E))*E = 1 := by
    unfold dualLength
    field_simp [hS.ne',hP.ne',hV.ne',hE.ne']
  calc
    _ = p.X^2*((p.S*p.P/(p.V*dualLength p E))*E) := by ring
    _ = _ := by rw [hc,mul_one]

/-- The original large-X hypothesis implies Watt's threshold on every block. -/
theorem blockScales_large_X {p : WattScales} {E F : ℝ}
    (hp : ∀ i, 1 ≤ p.size i) (hE : 1 ≤ E) (hF : 1 ≤ F)
    (hlarge : F*E ≤ p.X) (i j k : ℕ) :
    F ≤ (blockScales p (dualLength p E) i j k).X := by
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one (hp 0)
  have hC : 0 < p.C := lt_of_lt_of_le zero_lt_one (hp 1)
  have hR : 0 < p.R := lt_of_lt_of_le zero_lt_one (hp 2)
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  have hEp : 0 < E := by linarith
  have hA := dualLength_pos hS hP hV hEp
  have hid := completedScales_X_sq_mul_E hH hC hR.le hS hP hV hEp
  have hsq : F^2*E ≤ p.X^2 := by
    calc
      _ ≤ F^2*E^2 := mul_le_mul_of_nonneg_left (by nlinarith : E ≤ E^2) (sq_nonneg F)
      _ = (F*E)^2 := by ring
      _ ≤ p.X^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ F) hEp.le]
  rw [← hid] at hsq
  have hsq' : F^2 ≤ (completedScales p (dualLength p E)).X^2 :=
    le_of_mul_le_mul_right hsq hEp
  have hxp : 0 ≤ (completedScales p (dualLength p E)).X := by
    unfold Scales.X completedScales
    positivity
  have hx : F ≤ (completedScales p (dualLength p E)).X := by nlinarith
  exact hx.trans (blockScales_X_ge_completed hH hC hA hR.le hS.le hP.le i j k)

end
end Watt41
end DivisorProof
