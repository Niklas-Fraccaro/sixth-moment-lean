import Sechstmoment.Numerator.U.Replacement.ActualUnrestrictedRatioGCDVStar

/-! Concrete absolute majorant for the actual shifted common-X density.
No amplifier coefficient or continuous coordinate is reinterpreted. -/
namespace Sechstmoment.Source
open Complex Real Set
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 700000

def a03NativeGCDBroadDensity (α : MomentShifts) (a b m n : ℕ) (X : ℝ) : ℂ :=
  (a:ℂ)^(-1+α 1)*(b:ℂ)^(-1+α 3)*(m:ℂ)^(-1-α 0+α 1)*
    (n:ℂ)^(-1-α 2+α 3)*(X:ℂ)^(-1-α 1-α 3)

theorem a03NativeGCDBroadDensity_norm_bound (α : MomentShifts)
    (hα : ∀ j : Fin 4,‖α j‖≤1/4) {a b m n : ℕ}
    (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) {X : ℝ} (hX : 0<X) :
    ‖a03NativeGCDBroadDensity α a b m n X‖≤
      (m:ℝ)^(-(1/2:ℝ))*(n:ℝ)^(-(1/2:ℝ))*(X^(-(3/2:ℝ))+X^(-(1/2:ℝ))) := by
  have hre (j : Fin 4) := abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))
  have ha1 : (1:ℝ)≤a := by exact_mod_cast ha
  have hb1 : (1:ℝ)≤b := by exact_mod_cast hb
  have hm1 : (1:ℝ)≤m := by exact_mod_cast hm
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hp (r : ℕ) (hr : 0<r) (z : ℂ) : ‖(r:ℂ)^z‖=(r:ℝ)^z.re := by
    simpa only [Complex.ofReal_natCast] using
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hr : (0:ℝ)<r) z
  have hA : (a:ℝ)^(-1+(α 1).re)≤1 := by
    exact (Real.rpow_le_rpow_of_exponent_le ha1 (by linarith [(hre 1).2] : -1+(α 1).re≤0)).trans_eq (Real.rpow_zero _)
  have hB : (b:ℝ)^(-1+(α 3).re)≤1 := by
    exact (Real.rpow_le_rpow_of_exponent_le hb1 (by linarith [(hre 3).2] : -1+(α 3).re≤0)).trans_eq (Real.rpow_zero _)
  have hM : (m:ℝ)^(-1-(α 0).re+(α 1).re)≤(m:ℝ)^(-(1/2:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith [(hre 0).1,(hre 1).2])
  have hN : (n:ℝ)^(-1-(α 2).re+(α 3).re)≤(n:ℝ)^(-(1/2:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [(hre 2).1,(hre 3).2])
  have hXb : X^(-1-(α 1).re-(α 3).re)≤X^(-(3/2:ℝ))+X^(-(1/2:ℝ)) := by
    by_cases hx : X≤1
    · exact (Real.rpow_le_rpow_of_exponent_ge hX hx
        (by linarith [(hre 1).2,(hre 3).2] : -(3/2:ℝ)≤ -1-(α 1).re-(α 3).re)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hX.le _))
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hx))
        (by linarith [(hre 1).1,(hre 3).1] : -1-(α 1).re-(α 3).re≤ -(1/2:ℝ))).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg hX.le _))
  unfold a03NativeGCDBroadDensity
  rw [norm_mul,norm_mul,norm_mul,norm_mul,hp a ha,hp b hb,hp m hm,hp n hn,
    Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp only [Complex.add_re,Complex.sub_re,Complex.neg_re,Complex.one_re]
  calc
    _≤1*1*(m:ℝ)^(-(1/2:ℝ))*(n:ℝ)^(-(1/2:ℝ))*(X^(-(3/2:ℝ))+X^(-(1/2:ℝ))) := by gcongr
    _=_ := by ring

/-- This is exactly the five-power density in the unrestricted actual
native integrand; the positive gcd coefficient remains outside it. -/
theorem a03UnrestrictedRatioGCDVStarIntegrand_eq_broadDensity
    (dual positive : Bool) (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (f g : ℝ→ℝ) (u v m n h : ℕ) (X : ℝ) :
    Sechstmoment.a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v m n h X=
      (f (Real.log (u+1:ℝ)/Real.log T):ℂ)*(g (Real.log (v+1:ℝ)/Real.log T):ℂ)*
        (Nat.gcd ((u+1)*(m+1)) ((v+1)*(n+1)):ℂ)*
          a03NativeGCDBroadDensity α (u+1) (v+1) (m+1) (n+1) X*
            (a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (Sechstmoment.rawMomentShifts T σ)) ((u+1:ℝ)*(m+1:ℝ)^2/X)*
              a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (Sechstmoment.rawMomentShifts T σ)) ((v+1:ℝ)*(n+1:ℝ)^2/X))*
                ∫t : ℝ,Complex.exp (((-(T*rectangularGapSign positive*
                    (Nat.gcd ((u+1)*(m+1)) ((v+1)*(n+1)):ℝ)*(h+1)/X):ℝ):ℂ)*I*(t:ℂ))*
                  Sechstmoment.a03RatioLeadingBranchProfile dual Φ T σ t*
                    bblrVStar (polarPoleKiller T σ) (X^2/((u+1:ℝ)*(v+1:ℝ)*(T*t)^2)) := by
  unfold Sechstmoment.a03UnrestrictedRatioGCDVStarIntegrand a03NativeGCDBroadDensity
  push_cast
  ring

end
end Sechstmoment.Source
