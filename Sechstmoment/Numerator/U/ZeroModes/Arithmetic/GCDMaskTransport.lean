import Sechstmoment.Numerator.U.ZeroModes.Ratio.GCDVStarCoordinates
import Sechstmoment.Numerator.U.ZeroModes.RatioUnitTail

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem a03CommonX_outside_near_frequency_lower {T X D H s : ℝ}
    (hT : 0<T) (hX : 0<X) (hD : 0≤D) (hH : 0≤H)
    (hout : T^(s-1)*X≤D*H) : T^s≤|T*D*H/X| := by
  have ht : T*T^(s-1)=T^s := by
    calc
      _=T^1*T^(s-1) := by rw [Real.rpow_one]
      _=T^(1+(s-1)) := (Real.rpow_add hT _ _).symm
      _=T^s := by congr 1; ring
  have hh := mul_le_mul_of_nonneg_left hout (div_nonneg hT.le hX.le)
  have he : (T/X)*(T^(s-1)*X)=T*T^(s-1) := by field_simp
  have hf : (T/X)*(D*H)=T*D*H/X := by ring
  rw [he,hf,ht] at hh
  simpa only [abs_of_nonneg (by positivity : 0≤T*D*H/X)] using hh

theorem a03CommonX_low_frequency_product_lower {T X D H s : ℝ}
    (hT : 0<T) (_hX : 0<X) (hDH : 1≤D*H)
    (hnear : D*H≤T^(s-1)*X) : T^(1-s)≤X := by
  have hprod : T^(1-s)*T^(s-1)=1 := by
    rw [←Real.rpow_add hT]
    have he : 1-s+(s-1)=(0:ℝ) := by ring
    rw [he,Real.rpow_zero]
  have hh := mul_le_mul_of_nonneg_left (hDH.trans hnear) (Real.rpow_nonneg hT.le (1-s))
  calc
    T^(1-s)=T^(1-s)*1 := (mul_one _).symm
    _≤T^(1-s)*(T^(s-1)*X) := hh
    _=X := by rw [←mul_assoc,hprod,one_mul]

theorem a03CommonX_integrated_unit_ratio_lower {A m X : ℝ}
    (hA : 0<A) (hm : 0<m) (hX : 0<X) (hunit : X/(A*m)≤1) :
    X/A≤A*m^2/X := by
  have hXm : X≤A*m := (div_le_one (mul_pos hA hm)).mp hunit
  have hma : X/A≤m := (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using hXm)
  have hratio : m≤A*m^2/X := by
    apply (le_div_iff₀ hX).mpr
    nlinarith [mul_le_mul_of_nonneg_left hXm hm.le]
  exact hma.trans hratio

theorem a03CommonX_integrated_unit_polynomial_ratio {T A m X a s : ℝ}
    (hT : 0<T) (hA : 0<A) (hm : 0<m) (hX : 0<X)
    (hAmp : A≤T^a) (hLow : T^(1-s)≤X) (hunit : X/(A*m)≤1) :
    T^(1-s-a)≤A*m^2/X := by
  have hp : 0<T^a := Real.rpow_pos_of_pos hT _
  have hh : T^(1-s)/T^a≤X/A := div_le_div₀ hX.le hLow hA hAmp
  have he : T^(1-s)/T^a=T^(1-s-a) := (Real.rpow_sub hT (1-s) a).symm
  rw [he] at hh
  exact hh.trans (a03CommonX_integrated_unit_ratio_lower hA hm hX hunit)

theorem a03Physical_product_tail_argument_lower {T t P u C : ℝ}
    (hT : 0<T) (ht : 0<t) (ht2 : t≤2) (hC : 0<C)
    (hP : T^(2+u)/C≤P) : T^u/(4*C)≤P/(T*t)^2 := by
  have hP0 : 0≤P := (by positivity : 0<T^(2+u)/C).le.trans hP
  have hd : 0<(T*t)^2 := sq_pos_of_pos (mul_pos hT ht)
  have ht4 : (T*t)^2≤4*T^2 := by nlinarith [sq_nonneg (T*(2-t))]
  have he : T^(2+u)=T^2*T^u := by rw [Real.rpow_add hT,Real.rpow_ofNat]
  rw [he] at hP
  apply (le_div_iff₀ hd).mpr
  have hbase : (T^2*T^u)/C≤P := hP
  have hb : T^u/(4*C)*(4*T^2)=T^2*T^u/C := by field_simp
  calc
    _≤T^u/(4*C)*(4*T^2) := mul_le_mul_of_nonneg_left ht4 (by positivity)
    _=T^2*T^u/C := hb
    _≤P := hbase

end
end Sechstmoment
