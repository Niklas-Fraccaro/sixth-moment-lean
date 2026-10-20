import SixthMoment.Numerator.U.Sources.FiniteAmplifierGCDReindex
import SixthMoment.Numerator.U.ZeroModes.Ratio.AmplifierBudget

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03FiniteAmplifier_gcd_reindex_real (N₁ N₂ : ℕ) (F : ℕ→ℕ→ℕ→ℝ) :
    (∑ d∈Finset.Icc 1 (min N₁ N₂),∑ m∈Finset.Icc 1 (N₁/d),∑ n∈Finset.Icc 1 (N₂/d),
      if m.Coprime n then F d m n else 0)=
      ∑ m∈Finset.Icc 1 N₁,∑ n∈Finset.Icc 1 N₂,
        F (Nat.gcd m n) (m/Nat.gcd m n) (n/Nat.gcd m n) := by
  have hh := SixthMoment.a03FiniteAmplifier_gcd_reindex N₁ N₂
    (fun d m n => (F d m n:ℂ))
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum,apply_ite,Complex.ofReal_zero] using hh

def a03ZeroModeRatioPrimitiveProfilePowerMass (T a b : ℝ) (f g : ℝ→ℝ) (r t : ℝ) : ℝ :=
  ∑ d∈Finset.Icc 1 (min ⌊T^a⌋₊ ⌊T^b⌋₊),
    ∑ m∈Finset.Icc 1 (⌊T^a⌋₊/d),∑ n∈Finset.Icc 1 (⌊T^b⌋₊/d),
      if m.Coprime n then
        ‖f (Real.log (d*m:ℕ)/Real.log T)‖*‖g (Real.log (d*n:ℕ)/Real.log T)‖*
          (d:ℝ)^(-1:ℝ)*(m:ℝ)^(r-1)*(n:ℝ)^(t-1) else 0

theorem a03ZeroModeRatioPrimitiveProfilePowerMass_eq_original
    (T a b : ℝ) (f g : ℝ→ℝ) (r t : ℝ) :
    a03ZeroModeRatioPrimitiveProfilePowerMass T a b f g r t=
      a03ZeroModeRatioProfilePowerMass T a b f g r t := by
  unfold a03ZeroModeRatioPrimitiveProfilePowerMass
  rw [a03FiniteAmplifier_gcd_reindex_real]
  unfold a03ZeroModeRatioProfilePowerMass a03ZeroModeRatioCommonAmplifierPower
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n _
  have hdm : Nat.gcd m n*(m/Nat.gcd m n)=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
  have hdn : Nat.gcd m n*(n/Nat.gcd m n)=n := Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)
  rw [hdm,hdn]
  ring

theorem a03ZeroModeRatioPrimitiveProfilePowerMass_uniform_bound {a b r t : ℝ}
    (hr : 0<r) (hr1 : r≤1) (ht : 0<t) (ht1 : t≤1) (hrt : 1≤r+t)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,0<T →
      a03ZeroModeRatioPrimitiveProfilePowerMass T a b f g r t≤C*T^(a*r+b*t) := by
  simp_rw [a03ZeroModeRatioPrimitiveProfilePowerMass_eq_original]
  exact a03ZeroModeRatioProfilePowerMass_uniform_bound hr hr1 ht ht1 hrt f g hf hg

end
end SixthMoment.Source
