import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic


namespace Sechstmoment
open Real
open scoped BigOperators
noncomputable section

def bblrNearMassLogRadius (T η : ℝ) : ℝ :=
  1+Real.log (32*T^(2+η))

theorem bblrNearMassLogRadius_one_le {T η : ℝ} (hT : 1≤T) (hη : 0≤η) :
    1≤bblrNearMassLogRadius T η := by
  have hp : 1≤T^(2+η) := Real.one_le_rpow hT (by linarith)
  have hprod : 1≤32*T^(2+η) := by linarith
  unfold bblrNearMassLogRadius
  linarith [Real.log_nonneg hprod]

theorem bblrNearMass_product_le_cap {T η : ℝ} {P Q : ℕ}
    (hP : 0<P) (hQ : 0<Q)
    (hcut : (P:ℝ)*Q≤16*T^(2+η)) :
    (P:ℝ)≤16*T^(2+η) ∧ (Q:ℝ)≤16*T^(2+η) := by
  have hP1 : (1:ℝ)≤P := by exact_mod_cast hP
  have hQ1 : (1:ℝ)≤Q := by exact_mod_cast hQ
  constructor
  · exact (by nlinarith [show (0:ℝ)≤P by positivity] : (P:ℝ)≤(P:ℝ)*Q).trans hcut
  · exact (by nlinarith [show (0:ℝ)≤Q by positivity] : (Q:ℝ)≤(P:ℝ)*Q).trans hcut

theorem bblrNearMass_harmonic_P_le_radius {T η : ℝ} {P Q : ℕ}
    (hT : 1≤T) (_hη : 0≤η) (hP : 0<P) (hQ : 0<Q)
    (hcut : (P:ℝ)*Q≤16*T^(2+η)) :
    (harmonic P : ℝ)≤bblrNearMassLogRadius T η := by
  have hp : (0:ℝ)<P := by exact_mod_cast hP
  have hpower : 0≤T^(2+η) := Real.rpow_nonneg (zero_le_one.trans hT) _
  have hpc := (bblrNearMass_product_le_cap hP hQ hcut).1
  have hbound : (P:ℝ)≤32*T^(2+η) := by linarith
  exact (harmonic_le_one_add_log P).trans
    (add_le_add le_rfl (Real.log_le_log hp hbound))

theorem bblrNearMass_harmonic_K_le_radius {T η : ℝ} {P Q K : ℕ}
    (hT : 1≤T) (hη : 0≤η) (hP : 0<P) (hQ : 0<Q)
    (hcut : (P:ℝ)*Q≤16*T^(2+η)) (hK : K≤2*Q) :
    (harmonic K : ℝ)≤bblrNearMassLogRadius T η := by
  by_cases hK0 : K=0
  · simpa [hK0] using (zero_le_one.trans (bblrNearMassLogRadius_one_le hT hη))
  have hk : (0:ℝ)<K := by exact_mod_cast Nat.pos_of_ne_zero hK0
  have hpc := (bblrNearMass_product_le_cap hP hQ hcut).2
  have hkr : (K:ℝ)≤2*(Q:ℝ) := by exact_mod_cast hK
  have hbound : (K:ℝ)≤32*T^(2+η) := by linarith
  exact (harmonic_le_one_add_log K).trans
    (add_le_add le_rfl (Real.log_le_log hk hbound))

theorem bblrNearMass_sqrt_product_le_power {T η : ℝ} {P Q : ℕ}
    (hT : 1≤T) (hcut : (P:ℝ)*Q≤16*T^(2+η)) :
    Real.sqrt ((P:ℝ)*Q)≤4*T^(1+η/2) := by
  have ht : 0≤T := zero_le_one.trans hT
  calc
    _ ≤ Real.sqrt (16*T^(2+η)) := Real.sqrt_le_sqrt hcut
    _ = 4*T^(1+η/2) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤16)]
      norm_num
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul ht]
      congr 2
      ring

theorem bblrNearMass_sqrt_small_product_le_power {T η : ℝ} {P Q : ℕ}
    (hT : 1≤T) (hPQ : P≤Q) (hcut : (P:ℝ)*Q≤16*T^(2+η)) :
    Real.sqrt (P:ℝ)≤2*T^(1/2+η/4) := by
  have hpq : (P:ℝ)≤Q := by exact_mod_cast hPQ
  have hp : (P:ℝ)≤Real.sqrt ((P:ℝ)*Q) := by
    calc
      _ = Real.sqrt ((P:ℝ)^2) := (Real.sqrt_sq (Nat.cast_nonneg P)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [show (0:ℝ)≤P by positivity])
  calc
    _ ≤ Real.sqrt (4*T^(1+η/2)) := Real.sqrt_le_sqrt
      (hp.trans (bblrNearMass_sqrt_product_le_power hT hcut))
    _ = 2*T^(1/2+η/4) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
      norm_num
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul (zero_le_one.trans hT)]
      congr 2
      ring

theorem bblrNearMassLogRadius_le_log {T η : ℝ} (hT : 1≤T) (hη : 0≤η) :
    bblrNearMassLogRadius T η≤(10+η)*(1+Real.log T) := by
  have ht : 0<T := zero_lt_one.trans_le hT
  have hL : 0≤Real.log T := Real.log_nonneg hT
  have hlog2 : Real.log 2≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hlog32 : Real.log 32≤5 := by
    rw [show (32:ℝ)=(2:ℝ)^5 by norm_num,Real.log_pow]
    norm_num
    linarith
  unfold bblrNearMassLogRadius
  rw [Real.log_mul (by norm_num : (32:ℝ)≠0) (Real.rpow_pos_of_pos ht _).ne',
    Real.log_rpow ht]
  nlinarith

end
end Sechstmoment
