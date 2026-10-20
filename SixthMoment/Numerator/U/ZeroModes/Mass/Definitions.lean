import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import SixthMoment.Numerator.U.ZeroModes.SixTensorZeroMode

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03ZeroModeContinuousM₂ (_a b _m n d x : ℝ) : ℝ := b*n/d*x

def a03ZeroModeContinuousN₂ (a _b m _n d x : ℝ) : ℝ := a*m/d*x

def a03ZeroModeSixDensity (a b m n d x : ℝ) : ℝ :=
  1/Real.sqrt (a*b*m*a03ZeroModeContinuousM₂ a b m n d x*n*a03ZeroModeContinuousN₂ a b m n d x)

theorem a03ZeroModeSixDensity_eq {a b m n d x : ℝ}
    (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) (hd : 0<d) (hx : 0<x) :
    a03ZeroModeSixDensity a b m n d x=d/(a*b*m*n*x) := by
  have hprod : a*b*m*a03ZeroModeContinuousM₂ a b m n d x*n*a03ZeroModeContinuousN₂ a b m n d x=
      (a*b*m*n*x/d)^2 := by
    unfold a03ZeroModeContinuousM₂ a03ZeroModeContinuousN₂
    ring
  unfold a03ZeroModeSixDensity
  rw [hprod,Real.sqrt_sq (by positivity)]
  field_simp

theorem a03ZeroMode_gcd_pos {a b m n : ℕ} (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) :
    0<(Nat.gcd (a*m) (b*n):ℝ) := by
  have hleft := Nat.mul_pos ha hm
  have hright := Nat.mul_pos hb hn
  have hg := Nat.gcd_pos_of_pos_left (b*n) hleft
  have _ := hright
  exact_mod_cast hg

theorem a03ZeroModeSixDensity_gcd_eq {a b m n : ℕ} (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n)
    {x : ℝ} (hx : 0<x) :
    a03ZeroModeSixDensity a b m n (Nat.gcd (a*m) (b*n)) x=
      (Nat.gcd (a*m) (b*n):ℝ)/((a:ℝ)*b*m*n*x) :=
  a03ZeroModeSixDensity_eq (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hm) (by exact_mod_cast hn) (a03ZeroMode_gcd_pos ha hb hm hn) hx

theorem a03ZeroMode_dyadic_inverse_integrable {L : ℝ} (hL : 0<L) :
    IntegrableOn (fun x : ℝ => 1/x) (Icc L (2*L)) := by
  have hc : ContinuousOn (fun x : ℝ => 1/x) (Icc L (2*L)) :=
    continuousOn_const.div continuousOn_id (fun x hx => (hL.trans_le hx.1).ne')
  exact hc.integrableOn_Icc

theorem a03ZeroMode_dyadic_inverse_integral {L : ℝ} (hL : 0<L) :
    (∫ x : ℝ in Icc L (2*L),1/x)=Real.log 2 := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by linarith : L≤2*L),
    integral_one_div_of_pos hL (by positivity)]
  congr 1
  field_simp

def a03ZeroModeGapWeightSum (d H : ℝ) : ℝ :=
  ∑ h∈Finset.Icc 1 ⌊2*H⌋₊,rectangularSmoothBlockWeight (d*(h:ℝ)/H)

theorem a03ZeroModeGapWeightSum_nonneg (d H : ℝ) : 0≤a03ZeroModeGapWeightSum d H :=
  Finset.sum_nonneg (fun _h _ => rectangularSmoothBlockWeight_nonneg _)

theorem a03ZeroModeGapWeightSum_le {d H : ℝ} (hd : 0<d) (hH : 0<H) :
    a03ZeroModeGapWeightSum d H≤2*H/d := by
  let s : Finset ℕ := (Finset.Icc 1 ⌊2*H⌋₊).filter (fun h => h≤⌊2*H/d⌋₊)
  have hz (h : ℕ) (hh : ¬h≤⌊2*H/d⌋₊) : rectangularSmoothBlockWeight (d*(h:ℝ)/H)=0 := by
    by_contra hn
    have hs := (rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hn)).2
    have hhreal : (h:ℝ)≤2*H/d := by
      apply (le_div_iff₀ hd).mpr
      have hnum := (div_le_iff₀ hH).mp hs
      nlinarith only [hnum]
    exact hh (Nat.le_floor hhreal)
  have he : a03ZeroModeGapWeightSum d H=∑ h∈s,rectangularSmoothBlockWeight (d*(h:ℝ)/H) := by
    unfold a03ZeroModeGapWeightSum s
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro h _
    split_ifs with hh
    · rfl
    · exact hz h hh
  have hsub : s⊆Finset.Icc 1 ⌊2*H/d⌋₊ := by
    intro h hh
    have hs := Finset.mem_filter.mp hh
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs.1).1,hs.2⟩
  calc
    _=∑ h∈s,rectangularSmoothBlockWeight (d*(h:ℝ)/H) := he
    _≤∑ _h∈s,(1:ℝ) := Finset.sum_le_sum (fun h _ => rectangularSmoothBlockWeight_le_one _)
    _=(s.card:ℝ) := by simp
    _≤((Finset.Icc 1 ⌊2*H/d⌋₊).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _=(⌊2*H/d⌋₊:ℝ) := by simp
    _≤2*H/d := Nat.floor_le (by positivity)

def a03ZeroModeDyadicGapMass (a b m n d H L : ℝ) : ℝ :=
  a03ZeroModeGapWeightSum d H*
    ∫ x : ℝ in Icc L (2*L),a03ZeroModeSixDensity a b m n d x

theorem a03ZeroModeSixDensity_dyadic_integrable {a b m n d L : ℝ}
    (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) (hd : 0<d) (hL : 0<L) :
    IntegrableOn (a03ZeroModeSixDensity a b m n d) (Icc L (2*L)) := by
  have hi := (a03ZeroMode_dyadic_inverse_integrable hL).const_mul (d/(a*b*m*n))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [a03ZeroModeSixDensity_eq ha hb hm hn hd (hL.trans_le hx.1)]
  ring

theorem a03ZeroModeSixDensity_dyadic_integral {a b m n d L : ℝ}
    (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) (hd : 0<d) (hL : 0<L) :
    (∫ x : ℝ in Icc L (2*L),a03ZeroModeSixDensity a b m n d x)=
      d/(a*b*m*n)*Real.log 2 := by
  calc
    _=∫ x : ℝ in Icc L (2*L),(d/(a*b*m*n))*(1/x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [a03ZeroModeSixDensity_eq ha hb hm hn hd (hL.trans_le hx.1)]
      ring
    _=_ := by rw [integral_const_mul,a03ZeroMode_dyadic_inverse_integral hL]

theorem a03ZeroModeDyadicGapMass_le {a b m n d H L : ℝ}
    (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) (hd : 0<d) (hH : 0<H) (hL : 0<L) :
    a03ZeroModeDyadicGapMass a b m n d H L≤2*H*Real.log 2/(a*b*m*n) := by
  unfold a03ZeroModeDyadicGapMass
  rw [a03ZeroModeSixDensity_dyadic_integral ha hb hm hn hd hL]
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    _≤(2*H/d)*(d/(a*b*m*n)*Real.log 2) :=
      mul_le_mul_of_nonneg_right (a03ZeroModeGapWeightSum_le hd hH) (by positivity)
    _=_ := by field_simp

theorem a03ZeroModeDyadicGapMass_gcd_le {a b m n : ℕ}
    (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) {H L : ℝ} (hH : 0<H) (hL : 0<L) :
    a03ZeroModeDyadicGapMass a b m n (Nat.gcd (a*m) (b*n)) H L≤
      2*H*Real.log 2/((a:ℝ)*b*m*n) :=
  a03ZeroModeDyadicGapMass_le (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hm) (by exact_mod_cast hn) (a03ZeroMode_gcd_pos ha hb hm hn) hH hL

end
end SixthMoment
