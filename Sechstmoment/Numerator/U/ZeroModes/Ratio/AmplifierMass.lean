import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEError

/-! The complete original amplifier ranges in the ratio-contour residual
budget. The common gcd is extracted from each literal original pair; no
independent gcd cutoff or divisor-growth premise is introduced. -/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03PositiveInteger_power_sum_le {r : ℝ} (hr : 0<r) (hr1 : r≤1) (N : ℕ) :
    (∑ n∈Finset.Icc 1 N,(n:ℝ)^(r-1))≤(N:ℝ)^r/r := by
  have he : (∑ i∈Finset.range N,((i+1:ℕ):ℝ)^(r-1))=
      ∑ n∈Finset.Icc 1 N,(n:ℝ)^(r-1) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega),ih]
  have hanti : AntitoneOn (fun x : ℝ => x^(r-1)) (Ioc 0 (0+(N:ℝ))) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos hx.1 hxy (by linarith)
  have hi : IntegrableOn (fun x : ℝ => x^(r-1)) (Icc 0 (0+(N:ℝ))) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hs := hanti.sum_le_integral_of_integrableOn hi
  simp only [zero_add] at hs
  rw [he,integral_rpow (Or.inl (by linarith))] at hs
  simp only [sub_add_cancel,Real.zero_rpow hr.ne',sub_zero] at hs
  exact hs

theorem a03PositiveInteger_power_sum_floor_le {T r : ℝ}
    (hT : 0<T) (hr : 0<r) (hr1 : r≤1) (a : ℝ) :
    (∑ n∈Finset.Icc 1 ⌊T^a⌋₊,(n:ℝ)^(r-1))≤T^(a*r)/r := by
  calc
    _≤(⌊T^a⌋₊:ℝ)^r/r := a03PositiveInteger_power_sum_le hr hr1 _
    _≤(T^a)^r/r := by
      apply div_le_div_of_nonneg_right _ hr.le
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (Real.rpow_nonneg hT.le _)) hr.le
    _=_ := by rw [←Real.rpow_mul hT.le]

def a03ZeroModeRatioCommonAmplifierPower (m n : ℕ) (r t : ℝ) : ℝ :=
  (Nat.gcd m n:ℝ)^(-1:ℝ)*((m/Nat.gcd m n:ℕ):ℝ)^(r-1)*
    ((n/Nat.gcd m n:ℕ):ℝ)^(t-1)

theorem a03ZeroModeRatioCommonAmplifierPower_le {m n : ℕ}
    (hm : 0<m) (hn : 0<n) {r t : ℝ} (hrt : 1≤r+t) :
    a03ZeroModeRatioCommonAmplifierPower m n r t≤(m:ℝ)^(r-1)*(n:ℝ)^(t-1) := by
  let g := Nat.gcd m n
  let a := m/g
  let b := n/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left n hm
  have hga : g*a=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
  have hgb : g*b=n := Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)
  have ha : 0<a := Nat.div_pos (Nat.gcd_le_left n hm) hg
  have hb : 0<b := Nat.div_pos (Nat.gcd_le_right m hn) hg
  have hgp : 0<(g:ℝ) := by exact_mod_cast hg
  have hg1 : 1≤(g:ℝ) := by exact_mod_cast hg
  have hgcost : (g:ℝ)^(1-r-t)≤1 := by
    calc
      _≤(g:ℝ)^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hg1 (by linarith)
      _=1 := Real.rpow_zero _
  have he : a03ZeroModeRatioCommonAmplifierPower m n r t=
      (g:ℝ)^(1-r-t)*((m:ℝ)^(r-1)*(n:ℝ)^(t-1)) := by
    unfold a03ZeroModeRatioCommonAmplifierPower
    change (g:ℝ)^(-1:ℝ)*(a:ℝ)^(r-1)*(b:ℝ)^(t-1)=_
    rw [←hga,←hgb]
    simp only [Nat.cast_mul]
    rw [Real.mul_rpow (Nat.cast_nonneg g) (Nat.cast_nonneg a),
      Real.mul_rpow (Nat.cast_nonneg g) (Nat.cast_nonneg b)]
    calc
      _=((g:ℝ)^(-1:ℝ))*((a:ℝ)^(r-1)*(b:ℝ)^(t-1)) := by ring
      _=(g:ℝ)^((1-r-t)+(r-1)+(t-1))*((a:ℝ)^(r-1)*(b:ℝ)^(t-1)) := by
        congr 2
        ring
      _=_ := by rw [Real.rpow_add hgp,Real.rpow_add hgp]; ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right hgcost (by positivity)).trans_eq (one_mul _)

def a03ZeroModeRatioProfilePowerMass (T a b : ℝ) (f g : ℝ→ℝ) (r t : ℝ) : ℝ :=
  ∑ m∈Finset.Icc 1 ⌊T^a⌋₊,∑ n∈Finset.Icc 1 ⌊T^b⌋₊,
    ‖f (Real.log m/Real.log T)‖*‖g (Real.log n/Real.log T)‖*
      a03ZeroModeRatioCommonAmplifierPower m n r t

theorem a03ZeroModeRatioProfilePowerMass_nonneg (T a b : ℝ) (f g : ℝ→ℝ) (r t : ℝ) :
    0≤a03ZeroModeRatioProfilePowerMass T a b f g r t := by
  unfold a03ZeroModeRatioProfilePowerMass a03ZeroModeRatioCommonAmplifierPower
  positivity

theorem a03ZeroModeRatioProfilePowerMass_uniform_bound {a b r t : ℝ}
    (hr : 0<r) (hr1 : r≤1) (ht : 0<t) (ht1 : t≤1) (hrt : 1≤r+t)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,0<T →
      a03ZeroModeRatioProfilePowerMass T a b f g r t≤C*T^(a*r+b*t) := by
  obtain ⟨F,hF,hfB⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgB⟩ := rectangular_supported_profile_bounded g hg
  refine ⟨F*G/(r*t),by positivity,?_⟩
  intro T hT
  have hsum : a03ZeroModeRatioProfilePowerMass T a b f g r t≤
      F*G*(∑ m∈Finset.Icc 1 ⌊T^a⌋₊,(m:ℝ)^(r-1))*
        (∑ n∈Finset.Icc 1 ⌊T^b⌋₊,(n:ℝ)^(t-1)) := by
    unfold a03ZeroModeRatioProfilePowerMass
    calc
      _≤∑ m∈Finset.Icc 1 ⌊T^a⌋₊,∑ n∈Finset.Icc 1 ⌊T^b⌋₊,
          F*G*((m:ℝ)^(r-1)*(n:ℝ)^(t-1)) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        apply mul_le_mul
        · exact mul_le_mul (hfB _) (hgB _) (norm_nonneg _) hF
        · exact a03ZeroModeRatioCommonAmplifierPower_le
            (by have hh := (Finset.mem_Icc.mp hm).1; omega)
            (by have hh := (Finset.mem_Icc.mp hn).1; omega) hrt
        · unfold a03ZeroModeRatioCommonAmplifierPower
          positivity
        · positivity
      _=_ := by simp only [←Finset.mul_sum,←Finset.sum_mul]; ring
  calc
    _≤F*G*(∑ m∈Finset.Icc 1 ⌊T^a⌋₊,(m:ℝ)^(r-1))*
        (∑ n∈Finset.Icc 1 ⌊T^b⌋₊,(n:ℝ)^(t-1)) := hsum
    _≤F*G*(T^(a*r)/r)*(T^(b*t)/t) := by
      gcongr
      · exact a03PositiveInteger_power_sum_floor_le hT hr hr1 a
      · exact a03PositiveInteger_power_sum_floor_le hT ht ht1 b
    _=_ := by rw [Real.rpow_add hT]; ring

end
end Sechstmoment.Source
