import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Sechstmoment
open Complex Real Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1500000

theorem a03CommonX_point_gap_cap {T X A B D a b s u : ℝ}
    (hT : 0<T) (hX : 0<X) (hA : 0<A) (hB : 0<B)
    (ha : A≤T^a) (hb : B≤T^b) (hprod : X^2/(A*B)≤T^(2+u))
    (hlow : D≤T^(s-1)*X) : D≤8*T^((a+b)/2+s+u/2) := by
  have hP : X^2≤T^(a+b+2+u) := by
    have hh := (div_le_iff₀ (mul_pos hA hB)).mp hprod
    have hAB := mul_le_mul ha hb hB.le (Real.rpow_pos_of_pos hT _).le
    have hu := mul_le_mul_of_nonneg_left hAB (Real.rpow_nonneg hT.le (2+u))
    have he : T^(2+u)*(T^a*T^b)=T^(a+b+2+u) := by
      rw [←Real.rpow_add hT,←Real.rpow_add hT]
      congr 1
      ring
    calc
      X^2 ≤ T^(2+u)*(A*B) := hh
      _ ≤ T^(2+u)*(T^a*T^b) := hu
      _ = T^(a+b+2+u) := he
  have hx : X≤T^((a+b+2+u)/2) := by
    have hh := Real.sqrt_le_sqrt hP
    have he : Real.sqrt (T^(a+b+2+u))=T^((a+b+2+u)/2) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hT.le]
      congr 1
      ring
    simpa only [Real.sqrt_sq_eq_abs,abs_of_pos hX,he] using hh
  have he : T^(s-1)*T^((a+b+2+u)/2)=T^((a+b)/2+s+u/2) := by
    rw [←Real.rpow_add hT]
    congr 1
    ring
  have hD := hlow.trans (mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hT.le (s-1)))
  rw [he] at hD
  exact hD.trans (by nlinarith only [Real.rpow_nonneg hT.le ((a+b)/2+s+u/2)])

theorem a03CommonX_soft_boundary_polynomial_ratio {T X s ε : ℝ}
    (hT : 1≤T) (_hX : 0<X) (hs : s≤1/2) (hε : 0≤ε)
    (hLow : T^(1-s)≤X) :
    ((1/64:ℝ)^ε/64)*T^ε≤((X^2/64)^ε)/64 := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hpow : T≤X^2 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hTp.le (1-s)) hLow 2
    have he : (T^(1-s))^2=T^(2-2*s) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hTp.le]
      congr 1
      norm_num
      ring
    rw [he] at hh
    have ht : T^(1:ℝ)≤T^(2-2*s) :=
      Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hs] : (1:ℝ)≤2-2*s)
    rw [Real.rpow_one] at ht
    exact ht.trans hh
  have hh : (1/64:ℝ)*T≤X^2/64 := by linarith only [hpow]
  have hp := Real.rpow_le_rpow (by positivity : (0:ℝ)≤(1/64:ℝ)*T) hh hε
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤1/64) hTp.le] at hp
  calc
    ((1/64:ℝ)^ε/64)*T^ε=((1/64:ℝ)^ε*T^ε)/64 := by ring
    _≤((X^2/64)^ε)/64 :=
      div_le_div_of_nonneg_right hp (by norm_num : (0:ℝ)≤64)

end
end Sechstmoment
