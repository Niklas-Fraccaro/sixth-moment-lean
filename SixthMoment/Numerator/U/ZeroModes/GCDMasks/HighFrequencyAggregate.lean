import SixthMoment.Numerator.U.ZeroModes.GCDMasks.AbsoluteConvergence
import SixthMoment.Numerator.U.ZeroModes.GCDMasks.HighFrequencyEnvelope

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000

def a03NativeGCDMaskedPhysicalSum
    (mask : Bool→ℕ→ℕ→((ℕ×ℕ)×ℕ)→ℝ→ℝ) (dual : Bool) (Φ : ℝ→ℂ)
    (T a b : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  (T:ℂ)*∑positive : Bool,∑z∈Finset.range ⌊T^a⌋₊,∑v∈Finset.range ⌊T^b⌋₊,
    ∫X : ℝ in Ioi 0,∑'p : (ℕ×ℕ)×ℕ,(mask positive z v p X:ℂ)*
      a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X

theorem a03NativeGCD_amplifier_spatial_budget_bound {T a b : ℝ} (hT : 1≤T)
    (z v : ℕ) (hz : z∈Finset.range ⌊T^a⌋₊) (hv : v∈Finset.range ⌊T^b⌋₊) :
    (∫X : ℝ in Ioi 0,(X^(5/2:ℝ)+X^(7/2:ℝ))*
      a03NativeGCDSpatialEnvelope (T*Real.sqrt ((z+1:ℝ)*(v+1:ℝ))) X)≤
        T^((1+a+b)*(9/2:ℝ)) := by
  have ht : 0<T := zero_lt_one.trans_le hT
  have hz1 : (1:ℝ)≤z+1 := by linarith [Nat.cast_nonneg (α:=ℝ) z]
  have hv1 : (1:ℝ)≤v+1 := by linarith [Nat.cast_nonneg (α:=ℝ) v]
  have hp : (1:ℝ)≤(z+1:ℝ)*(v+1:ℝ) := by nlinarith
  have hY : 1≤T*Real.sqrt ((z+1:ℝ)*(v+1:ℝ)) := by
    have hh := mul_le_mul hT (Real.one_le_sqrt.mpr hp) zero_le_one (zero_lt_one.trans_le hT).le
    simpa only [one_mul] using hh
  have hzcap : (z+1:ℝ)≤T^a :=
    (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hz) : (z+1:ℝ)≤⌊T^a⌋₊).trans
      (Nat.floor_le (Real.rpow_nonneg ht.le a))
  have hvcap : (v+1:ℝ)≤T^b :=
    (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hv) : (v+1:ℝ)≤⌊T^b⌋₊).trans
      (Nat.floor_le (Real.rpow_nonneg ht.le b))
  have hYcap : T*Real.sqrt ((z+1:ℝ)*(v+1:ℝ))≤T^(1+a+b) := by
    calc
      _≤T*((z+1:ℝ)*(v+1:ℝ)) := mul_le_mul_of_nonneg_left
        (Real.sqrt_le_self_iff.mpr (Or.inr hp)) ht.le
      _≤T*(T^a*T^b) := mul_le_mul_of_nonneg_left
        (mul_le_mul hzcap hvcap (by positivity) (Real.rpow_nonneg ht.le a)) ht.le
      _=T^(1+a+b) := by
        calc
          _=T^(1:ℝ)*(T^a*T^b) := by rw [Real.rpow_one]
          _=T^(1+a+b) := by
            rw [←Real.rpow_add ht,←Real.rpow_add ht]
            congr 1
            ring
  exact a03NativeGCDSpatialBroadBudget_uniform_power hT hY hYcap

theorem a03NativeGCD_masked_physical_sum_norm_le_of_point_bound
    {T a b D Q : ℝ} (hT : 1≤T) (hD : 0≤D) (k : ℕ)
    (mask : Bool→ℕ→ℕ→((ℕ×ℕ)×ℕ)→ℝ→ℝ) (dual : Bool) (Φ : ℝ→ℂ)
    (σ α : MomentShifts) (f g : ℝ→ℝ)
    (hpoint : ∀positive : Bool,∀z∈Finset.range ⌊T^a⌋₊,∀v∈Finset.range ⌊T^b⌋₊,
      ∀X : ℝ,0<X →
      ‖∑'p : (ℕ×ℕ)×ℕ,(mask positive z v p X:ℂ)*
        a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X‖≤
      (D*T^(-Q)*(Real.log T)^k/((z+1:ℝ)*(v+1:ℝ)*T^2))*
        ((X^(5/2:ℝ)+X^(7/2:ℝ))*a03NativeGCDSpatialEnvelope (T*Real.sqrt ((z+1:ℝ)*(v+1:ℝ))) X)) :
    ‖a03NativeGCDMaskedPhysicalSum mask dual Φ T a b σ α f g‖≤
      2*D*T^(1+a+b+(1+a+b)*(9/2:ℝ)-Q)*(Real.log T)^k := by
  have ht : 0<T := zero_lt_one.trans_le hT
  have hlog0 : 0≤Real.log T := Real.log_nonneg hT
  let B : ℝ := D*T^(-Q)*(Real.log T)^k*T^((1+a+b)*(9/2:ℝ))
  have hB : 0≤B := by dsimp [B]; positivity
  have hlocal (positive : Bool) (z : ℕ) (hz : z∈Finset.range ⌊T^a⌋₊)
      (v : ℕ) (hv : v∈Finset.range ⌊T^b⌋₊) :
      ‖∫X : ℝ in Ioi 0,∑'p : (ℕ×ℕ)×ℕ,(mask positive z v p X:ℂ)*
        a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X‖≤B := by
    have hY : 0<T*Real.sqrt ((z+1:ℝ)*(v+1:ℝ)) := by positivity
    have hcoeff : 0≤D*T^(-Q)*(Real.log T)^k := by positivity
    have hden : 1≤(z+1:ℝ)*(v+1:ℝ)*T^2 := by
      have hp : (1:ℝ)≤(z+1:ℝ)*(v+1:ℝ) := by nlinarith [Nat.cast_nonneg (α:=ℝ) z,Nat.cast_nonneg (α:=ℝ) v]
      have hs : (1:ℝ)≤T^2 := by nlinarith
      simpa only [one_mul] using mul_le_mul hp hs (by norm_num : (0:ℝ)≤1) (by positivity : 0≤(z+1:ℝ)*(v+1:ℝ))
    have hint := norm_integral_le_of_norm_le
      ((a03NativeGCDSpatialBroadBudget_integrable hY).const_mul
        (D*T^(-Q)*(Real.log T)^k/((z+1:ℝ)*(v+1:ℝ)*T^2))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
      exact hpoint positive z hz v hv X hX)
    rw [integral_const_mul] at hint
    calc
      _≤(D*T^(-Q)*(Real.log T)^k/((z+1:ℝ)*(v+1:ℝ)*T^2))*
        (∫X : ℝ in Ioi 0,(X^(5/2:ℝ)+X^(7/2:ℝ))*a03NativeGCDSpatialEnvelope (T*Real.sqrt ((z+1:ℝ)*(v+1:ℝ))) X) := hint
      _≤(D*T^(-Q)*(Real.log T)^k)*T^((1+a+b)*(9/2:ℝ)) :=
        mul_le_mul (div_le_self hcoeff hden) (a03NativeGCD_amplifier_spatial_budget_bound hT z v hz hv)
          (setIntegral_nonneg measurableSet_Ioi (fun X hX => by
            have hx : 0<X := hX
            unfold a03NativeGCDSpatialEnvelope
            positivity)) hcoeff
      _=B := rfl
  unfold a03NativeGCDMaskedPhysicalSum
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ht.le]
  have hsum (positive : Bool) :
      ‖∑z∈Finset.range ⌊T^a⌋₊,∑v∈Finset.range ⌊T^b⌋₊,
        ∫X : ℝ in Ioi 0,∑'p : (ℕ×ℕ)×ℕ,(mask positive z v p X:ℂ)*
          a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2 X‖≤
        (⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*B := by
    apply (norm_sum_le _ _).trans
    calc
      _≤∑_z∈Finset.range ⌊T^a⌋₊,∑_v∈Finset.range ⌊T^b⌋₊,B := by
        apply Finset.sum_le_sum
        intro z hz
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun v hv => hlocal positive z hz v hv))
      _=_ := by simp [mul_assoc]
  calc
    _≤T*(∑_positive : Bool,(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*B) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun positive _ => hsum positive))) ht.le
    _=T*(2*((⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*B)) := by simp [two_mul]
    _≤T*(2*(T^a*T^b*B)) := by
      gcongr
      · exact Nat.floor_le (Real.rpow_nonneg ht.le a)
      · exact Nat.floor_le (Real.rpow_nonneg ht.le b)
    _=_ := by
      have he : T*(T^a*T^b*T^(-Q)*T^((1+a+b)*(9/2:ℝ)))=
          T^(1+a+b+(1+a+b)*(9/2:ℝ)-Q) := by
        calc
          _=T^(1:ℝ)*(T^a*T^b*T^(-Q)*T^((1+a+b)*(9/2:ℝ))) := by rw [Real.rpow_one]
          _=_ := by
            rw [←Real.rpow_add ht,←Real.rpow_add ht,←Real.rpow_add ht,←Real.rpow_add ht]
            congr 1
            ring
      dsimp [B]
      rw [show T*(2*(T^a*T^b*(D*T^(-Q)*(Real.log T)^k*T^((1+a+b)*(9/2:ℝ)))))=
        2*D*(T*(T^a*T^b*T^(-Q)*T^((1+a+b)*(9/2:ℝ))))*(Real.log T)^k by ring,he]

theorem a03NativeGCD_high_gap_frequency {T X s : ℝ} (hT : 0<T) (hX : 0<X)
    (positive : Bool) (a b m n h : ℕ)
    (hgap : T^(s-1)*X≤(Nat.gcd ((a+1)*(m+1)) ((b+1)*(n+1)):ℝ)*(h+1)) :
    T^s≤|-(T*rectangularGapSign positive*(Nat.gcd ((a+1)*(m+1)) ((b+1)*(n+1)):ℝ)*(h+1)/X)| := by
  have he : T*T^(s-1)=T^s := by
    calc
      _=T^(1:ℝ)*T^(s-1) := by rw [Real.rpow_one]
      _=T^s := by rw [←Real.rpow_add hT]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_left hgap (div_nonneg hT.le hX.le)
  have hc : (T/X)*(T^(s-1)*X)=T^s := by rw [←he]; field_simp
  rw [hc] at hh
  rw [abs_neg,abs_div,abs_mul,abs_mul,abs_mul,abs_of_pos hT,
    abs_of_pos (by positivity : 0<(h:ℝ)+1),abs_of_pos hX]
  rw [abs_of_nonneg (show (0:ℝ)≤Nat.gcd ((a+1)*(m+1)) ((b+1)*(n+1)) from Nat.cast_nonneg _)]
  cases positive <;> norm_num [rectangularGapSign] <;>
    simpa only [mul_assoc,mul_comm,mul_left_comm,div_eq_mul_inv] using hh

end
end SixthMoment
