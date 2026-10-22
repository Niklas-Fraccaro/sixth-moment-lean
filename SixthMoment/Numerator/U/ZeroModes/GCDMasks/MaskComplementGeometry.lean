import SixthMoment.Numerator.U.Separation.ContinuousDyadicUnitRatioTail
import SixthMoment.Numerator.U.ZeroModes.GCDMasks.MaskPowerTransport
import SixthMoment.Numerator.U.ZeroModes.GCDMasks.PassiveMaskPartition

namespace SixthMoment
open Complex Real Source Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 600000

def a03NativeGCDMaskTailExponent (a b s ε : ℝ) : ℝ :=
  min ε (min (1-s-a) (1-s-b))

def a03NativeGCDMaskTailConstant (ε : ℝ) : ℝ :=
  min (9/16) ((1/64:ℝ)^ε/64)

theorem a03NativeGCDMaskTailConstant_pos (ε : ℝ) :
    0<a03NativeGCDMaskTailConstant ε := by
  unfold a03NativeGCDMaskTailConstant
  exact lt_min (by norm_num) (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num))

theorem a03NativeGCDMaskTailExponent_pos {a b s ε : ℝ}
    (hε : 0<ε) (ha : s+a<1) (hb : s+b<1) :
    0<a03NativeGCDMaskTailExponent a b s ε := by
  unfold a03NativeGCDMaskTailExponent
  exact lt_min hε (lt_min (by linarith only [ha]) (by linarith only [hb]))

theorem a03NativeGCDCoordinateGap_one_le (w : Fin 5→ℕ) (hw : ∀j,1≤w j) :
    1≤a03NativeGCDCoordinateGap w := by
  have hp (j : Fin 5) : 0<w j := by have := hw j; omega
  have hd : 0<Nat.gcd (w 0*w 2) (w 1*w 3) :=
    Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (hp 0) (hp 2))
  unfold a03NativeGCDCoordinateGap
  have hD : (1:ℝ)≤Nat.gcd (w 0*w 2) (w 1*w 3) := by exact_mod_cast hd
  have hH : (1:ℝ)≤w 4 := by exact_mod_cast hw 4
  nlinarith only [hD,hH]

theorem a03CommonX_low_frequency_gap {T X D s : ℝ}
    (hT : 0<T) (hX : 0<X) (hfreq : T*D/X≤T^s) : D≤T^(s-1)*X := by
  have hh := (div_le_iff₀ hX).mp hfreq
  have hd : D≤(T^s*X)/T := (le_div_iff₀ hT).mpr (by simpa only [mul_comm] using hh)
  convert hd using 1
  rw [Real.rpow_sub hT,Real.rpow_one]
  ring

theorem a03CommonX_low_gap_spatial_lower {T X D s : ℝ}
    (hT : 0<T) (hD : 1≤D) (hlow : D≤T^(s-1)*X) : T^(1-s)≤X := by
  have hh : 1≤T^(s-1)*X := hD.trans hlow
  have he : T^(1-s)*T^(s-1)=1 := by
    rw [←Real.rpow_add hT,show (1-s)+(s-1)=0 by ring,Real.rpow_zero]
  have hp := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hT.le (1-s))
  simpa only [mul_one,←mul_assoc,he,one_mul] using hp

theorem a03CommonX_product_boundary_spatial {T A B X u : ℝ}
    (hT : 0<T) (hA : 0<A) (hB : 0<B) (hX : 0<X)
    (hprod : T^(2+u)≤X^2/(A*B)) :
    (T*Real.sqrt (A*B))*T^(u/2)≤X := by
  have hAB : 0<A*B := mul_pos hA hB
  have hpow : T^2*(T^(u/2))^2=T^(2+u) := by
    rw [←Real.rpow_two,←Real.rpow_natCast,←Real.rpow_mul hT.le,←Real.rpow_add hT]
    congr 1
    norm_num
  have he : ((T*Real.sqrt (A*B))*T^(u/2))^2=(A*B)*T^(2+u) := by
    calc
      _=(A*B)*(T^2*(T^(u/2))^2) := by
        rw [mul_pow,mul_pow,Real.sq_sqrt hAB.le]
        ring
      _=_ := by rw [hpow]
  have hh := (le_div_iff₀ hAB).mp hprod
  have hsq : ((T*Real.sqrt (A*B))*T^(u/2))^2≤X^2 := by
    rw [he]
    simpa only [mul_comm] using hh
  exact (sq_le_sq₀ (by positivity) hX.le).mp hsq

theorem a03NativeGCDMaskTailThreshold_soft {T X a b s ε : ℝ}
    (hT : 1≤T) (hX : 0<X) (hs : s≤1/2) (hε : 0≤ε) (hLow : T^(1-s)≤X) :
    a03NativeGCDMaskTailConstant ε*T^(a03NativeGCDMaskTailExponent a b s ε)≤
      ((X^2/64)^ε)/64 := by
  have hc : a03NativeGCDMaskTailConstant ε≤((1/64:ℝ)^ε)/64 := min_le_right _ _
  have he : a03NativeGCDMaskTailExponent a b s ε≤ε := min_le_left _ _
  have hpow := Real.rpow_le_rpow_of_exponent_le hT he
  exact (mul_le_mul hc hpow (Real.rpow_nonneg (zero_le_one.trans hT) _)
    (by positivity)).trans (a03CommonX_soft_boundary_polynomial_ratio hT hX hs hε hLow)

theorem a03NativeGCDMaskTailThreshold_unit {T A m X a b s ε : ℝ}
    (hT : 1≤T) (hA : 0<A) (hm : 0<m) (hX : 0<X)
    (hAmp : A≤T^a) (hLow : T^(1-s)≤X) (hunit : X/(A*m)≤4/3) :
    a03NativeGCDMaskTailConstant ε*T^(a03NativeGCDMaskTailExponent a b s ε)≤A*m^2/X := by
  have hc : a03NativeGCDMaskTailConstant ε≤9/16 := min_le_left _ _
  have he : a03NativeGCDMaskTailExponent a b s ε≤1-s-a :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hpow := Real.rpow_le_rpow_of_exponent_le hT he
  have hh := a03CommonX_integrated_bounded_polynomial_ratio
    (zero_lt_one.trans_le hT) hA hm hX (by norm_num : (0:ℝ)<4/3) hAmp hLow hunit
  norm_num only [show (1:ℝ)/(4/3)^2=9/16 by norm_num] at hh
  exact (mul_le_mul hc hpow (Real.rpow_nonneg (zero_le_one.trans hT) _)
    (by norm_num : (0:ℝ)≤9/16)).trans hh

theorem a03_native_GCD_passive_mask_complement_classified
    {T : ℝ} (hT : 1≤T) (a b s u ε : ℝ) (hs : s≤1/2) (hε : 0≤ε)
    (f g : ℝ→ℝ) (w : Fin 5→ℕ) (hw : ∀j,1≤w j) (X : ℝ) (hX : 0<X)
    (hf : f (Real.log (w 0:ℝ)/Real.log T)≠0)
    (hg : g (Real.log (w 1:ℝ)/Real.log T)≠0)
    (ha : (w 0:ℝ)≤T^a) (hb : (w 1:ℝ)≤T^b)
    (hmask : a03NativeGCDSelectedDyadicMask (fun _ => True) T a b s u ε f g w X≠1) :
    T^(2+u)<X^2/((w 0:ℝ)*w 1) ∨
      T^s≤T*a03NativeGCDCoordinateGap w/X ∨
      a03NativeGCDMaskTailConstant (DivisorProof.inputExponent ε 1)*T^(a03NativeGCDMaskTailExponent a b s (DivisorProof.inputExponent ε 1))≤
        (w 0:ℝ)*(w 2:ℝ)^2/X ∨
      a03NativeGCDMaskTailConstant (DivisorProof.inputExponent ε 1)*T^(a03NativeGCDMaskTailExponent a b s (DivisorProof.inputExponent ε 1))≤
        (w 1:ℝ)*(w 3:ℝ)^2/X := by
  by_contra h
  push Not at h
  obtain ⟨hprod,hfreq,hrM,hrN⟩ := h
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hρ : 0≤DivisorProof.inputExponent ε 1 := by
    unfold DivisorProof.inputExponent
    exact le_min (div_nonneg hε (by norm_num)) (by norm_num)
  have hp (j : Fin 5) : (0:ℝ)<w j := by
    exact_mod_cast (show 0<w j by have := hw j; omega)
  have hlow := a03CommonX_low_frequency_gap hTp hX hfreq.le
  have hLow := a03CommonX_low_gap_spatial_lower hTp (a03NativeGCDCoordinateGap_one_le w hw) hlow
  have hgap := a03CommonX_point_gap_cap hTp hX (hp 0) (hp 1) ha hb hprod hlow
  have hsoft := a03NativeGCDMaskTailThreshold_soft (a:=a) (b:=b)
    (ε:=DivisorProof.inputExponent ε 1) hT hX hs hρ hLow
  have hM₂ : 4/3<X/((w 0:ℝ)*w 2) := by
    by_contra hu
    have hh := a03NativeGCDMaskTailThreshold_unit (a:=a) (b:=b) (ε:=DivisorProof.inputExponent ε 1)
      hT (hp 0) (hp 2) hX ha hLow (le_of_not_gt hu)
    exact (not_lt_of_ge hh) hrM
  have hN₂ : 4/3<X/((w 1:ℝ)*w 3) := by
    by_contra hu
    have hh := a03NativeGCDMaskTailThreshold_unit (a:=b) (b:=a) (ε:=DivisorProof.inputExponent ε 1)
      hT (hp 1) (hp 3) hX hb hLow (le_of_not_gt hu)
    have he : a03NativeGCDMaskTailExponent b a s (DivisorProof.inputExponent ε 1)=a03NativeGCDMaskTailExponent a b s (DivisorProof.inputExponent ε 1) := by
      unfold a03NativeGCDMaskTailExponent
      rw [min_comm (1-s-b) (1-s-a)]
    rw [he] at hh
    exact (not_lt_of_ge hh) hrN
  exact hmask (a03_native_GCD_passive_mask_partition hTp a b s u ε hε f g w hw X hX
    hf hg ha hb hgap hprod hlow hM₂ hN₂ (hrM.trans_le hsoft) (hrN.trans_le hsoft))

end
end SixthMoment
