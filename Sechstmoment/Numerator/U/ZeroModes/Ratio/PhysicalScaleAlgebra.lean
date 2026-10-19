import Sechstmoment.Numerator.U.ZeroModes.Ratio.AmplifierBudget
import Sechstmoment.Numerator.U.ZeroModes.Ratio.PhysicalResidual

/-! Exact common-x normalization of all three physical contour gains,
followed by the actual original amplifier exponents. -/
namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioPhysicalScale (T : ℝ) (g a b : ℕ) : ℝ :=
  T*(g:ℝ)*(a:ℝ)^(1/2:ℝ)*(b:ℝ)^(1/2:ℝ)

theorem a03ZeroModeRatioPhysicalScale_pos {T : ℝ} (hT : 0<T)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) :
    0<a03ZeroModeRatioPhysicalScale T g a b := by
  unfold a03ZeroModeRatioPhysicalScale
  exact mul_pos (mul_pos (mul_pos hT (by exact_mod_cast hg))
    (Real.rpow_pos_of_pos (by exact_mod_cast ha) _))
      (Real.rpow_pos_of_pos (by exact_mod_cast hb) _)

theorem a03ZeroModeRatioPhysicalScale_eq {T : ℝ}
    (g a b : ℕ) :
    a03ZeroModeRatioPhysicalScale T g a b=T*(g:ℝ)*Real.sqrt (a*b:ℕ) := by
  unfold a03ZeroModeRatioPhysicalScale
  rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg a)]
  simp only [Real.sqrt_eq_rpow]
  ring

theorem a03ZeroModeRatioPhysicalScale_power_normalization {T : ℝ} (hT : 0<T)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b)
    (β δ c q d l r : ℝ) :
    T^(-c)*(g:ℝ)^(-1+β+δ-c-q)*(a:ℝ)^(-1+β+d-l)*(b:ℝ)^(-1+δ+d-r)*
      (a03ZeroModeRatioPhysicalScale T g a b)^(c+q-β-δ)=
    T^(q-β-δ)*(g:ℝ)^(-1:ℝ)*
      (a:ℝ)^((c+q)/2-1+(β-δ)/2+d-l)*
      (b:ℝ)^((c+q)/2-1+(δ-β)/2+d-r) := by
  have hgp : 0<(g:ℝ) := by exact_mod_cast hg
  have hap : 0<(a:ℝ) := by exact_mod_cast ha
  have hbp : 0<(b:ℝ) := by exact_mod_cast hb
  have hY : (a03ZeroModeRatioPhysicalScale T g a b)^(c+q-β-δ)=
      T^(c+q-β-δ)*(g:ℝ)^(c+q-β-δ)*
        (a:ℝ)^((c+q-β-δ)/2)*(b:ℝ)^((c+q-β-δ)/2) := by
    unfold a03ZeroModeRatioPhysicalScale
    rw [Real.mul_rpow (mul_nonneg (mul_nonneg hT.le hgp.le) (Real.rpow_nonneg hap.le _))
        (Real.rpow_nonneg hbp.le _),
      Real.mul_rpow (mul_nonneg hT.le hgp.le) (Real.rpow_nonneg hap.le _),
      Real.mul_rpow hT.le hgp.le,←Real.rpow_mul hap.le,←Real.rpow_mul hbp.le]
    congr 2 <;> ring
  rw [hY]
  calc
    _=(T^(-c)*T^(c+q-β-δ))*
      ((g:ℝ)^(-1+β+δ-c-q)*(g:ℝ)^(c+q-β-δ))*
      ((a:ℝ)^(-1+β+d-l)*(a:ℝ)^((c+q-β-δ)/2))*
      ((b:ℝ)^(-1+δ+d-r)*(b:ℝ)^((c+q-β-δ)/2)) := by ring
    _=_ := by
      rw [←Real.rpow_add hT,←Real.rpow_add hgp,←Real.rpow_add hap,←Real.rpow_add hbp]
      congr 2 <;> ring

theorem a03ZeroModeRatioPhysicalGain_power {g a : ℕ} (_hg : 0<g) (_ha : 0<a)
    {x : ℝ} (hx : 0<x) (c : ℝ) :
    (x/(g*a:ℕ))^c=x^c*(g:ℝ)^(-c)*(a:ℝ)^(-c) := by
  rw [Nat.cast_mul,Real.div_rpow hx.le
    (mul_nonneg (Nat.cast_nonneg g) (Nat.cast_nonneg a)),
    Real.mul_rpow (Nat.cast_nonneg g) (Nat.cast_nonneg a),div_eq_mul_inv,mul_inv_rev,
    ←Real.rpow_neg (Nat.cast_nonneg g),←Real.rpow_neg (Nat.cast_nonneg a)]
  ring

theorem a03ZeroModeRatioPhysicalPrefactor_gain_norm (α : MomentShifts)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {x : ℝ} (hx : 0<x) (s : ℂ) (d l r q : ℝ) (hlr : l+r=q) :
    ‖a03ZeroModeRatioPhysicalPrefactor α g a b A B x s‖*(a:ℝ)^d*(b:ℝ)^d*
      ((x/(g*a:ℕ))^l*(x/(g*b:ℕ))^r)=
    (‖A (g*a)‖*‖B (g*b)‖*(g:ℝ)^(-1+(α 1).re+(α 3).re-s.re-q)*
      (a:ℝ)^(-1+(α 1).re+d-l)*(b:ℝ)^(-1+(α 3).re+d-r))*
        x^(q-(α 1).re-(α 3).re) := by
  have hgp : 0<(g:ℝ) := by exact_mod_cast hg
  have hap : 0<(a:ℝ) := by exact_mod_cast ha
  have hbp : 0<(b:ℝ) := by exact_mod_cast hb
  rw [a03ZeroModeRatioPhysicalPrefactor_norm α hg ha hb A B hx,
    a03ZeroModeRatioPhysicalGain_power hg ha hx,a03ZeroModeRatioPhysicalGain_power hg hb hx]
  calc
    _=(‖A (g*a)‖*‖B (g*b)‖)*
      (((g:ℝ)^(-1+(α 1).re+(α 3).re-s.re)*(g:ℝ)^(-l))*(g:ℝ)^(-r))*
      (((a:ℝ)^(-1+(α 1).re)*(a:ℝ)^d)*(a:ℝ)^(-l))*
      (((b:ℝ)^(-1+(α 3).re)*(b:ℝ)^d)*(b:ℝ)^(-r))*
      ((x^(-(α 1).re-(α 3).re)*x^l)*x^r) := by ring
    _=_ := by
      rw [←Real.rpow_add hgp,←Real.rpow_add hgp,←Real.rpow_add hap,←Real.rpow_add hap,
        ←Real.rpow_add hbp,←Real.rpow_add hbp,←Real.rpow_add hx,←Real.rpow_add hx]
      simp only [←hlr]
      congr 2 <;> ring

def a03ZeroModeRatioResidualLeftLine (ε : ℝ) : Fin 3→ℝ :=
  ![a03ZeroModeRatioPrimaryLine ε,0,a03ZeroModeRatioSecondaryLine ε]

def a03ZeroModeRatioResidualRightLine (ε : ℝ) : Fin 3→ℝ :=
  ![a03ZeroModeRatioPrimaryLine ε,a03ZeroModeRatioSecondaryLine ε,0]

theorem a03ZeroModeRatioResidualLine_sum (ε : ℝ) (j : Fin 3) :
    a03ZeroModeRatioResidualLeftLine ε j+a03ZeroModeRatioResidualRightLine ε j=
      a03ZeroModeRatioSecondaryLine ε := by
  fin_cases j
  all_goals norm_num [a03ZeroModeRatioResidualLeftLine,a03ZeroModeRatioResidualRightLine,
    a03ZeroModeRatioPrimaryLine,a03ZeroModeRatioSecondaryLine]
  ring

def a03ZeroModeRatioResidualAmplifierLeftExponent (η : ℝ) : Fin 3→ℝ :=
  ![1/2+η,1/4+η,3/4+η]

def a03ZeroModeRatioResidualAmplifierRightExponent (η : ℝ) : Fin 3→ℝ :=
  ![1/2+η,3/4+η,1/4+η]

theorem a03ZeroModeRatioResidualAmplifier_exponents_dominate {η β δ : ℝ}
    (hη : 0<η) (hβ : |β|≤η/32) (hδ : |δ|≤η/32) (j : Fin 3) :
    ((1+η/4)+a03ZeroModeRatioSecondaryLine (η/4))/2+(β-δ)/2+η/4-
        a03ZeroModeRatioResidualLeftLine (η/4) j≤
      a03ZeroModeRatioResidualAmplifierLeftExponent η j ∧
    ((1+η/4)+a03ZeroModeRatioSecondaryLine (η/4))/2+(δ-β)/2+η/4-
        a03ZeroModeRatioResidualRightLine (η/4) j≤
      a03ZeroModeRatioResidualAmplifierRightExponent η j := by
  have hb := abs_le.mp hβ
  have hd := abs_le.mp hδ
  fin_cases j <;>
    norm_num [a03ZeroModeRatioResidualLeftLine,a03ZeroModeRatioResidualRightLine,
      a03ZeroModeRatioResidualAmplifierLeftExponent,a03ZeroModeRatioResidualAmplifierRightExponent,
      a03ZeroModeRatioPrimaryLine,a03ZeroModeRatioSecondaryLine] <;>
    constructor <;> linarith

theorem a03ZeroModeRatioResidual_time_exponent_dominate {η β δ : ℝ}
    (hη : 0<η) (hβ : |β|≤η/32) (hδ : |δ|≤η/32) :
    1+a03ZeroModeRatioSecondaryLine (η/4)-β-δ≤1/2+η := by
  have hb := abs_le.mp hβ
  have hd := abs_le.mp hδ
  unfold a03ZeroModeRatioSecondaryLine
  linarith

theorem a03ZeroModeRatioResidual_xmass_exponent_range {η β δ : ℝ}
    (hη : 0<η) (hη1 : η≤1/16) (hβ : |β|≤η/32) (hδ : |δ|≤η/32) :
    1/4≤(1+η/4)+a03ZeroModeRatioSecondaryLine (η/4)-β-δ ∧
      (1+η/4)+a03ZeroModeRatioSecondaryLine (η/4)-β-δ≤1 := by
  have hb := abs_le.mp hβ
  have hd := abs_le.mp hδ
  unfold a03ZeroModeRatioSecondaryLine
  constructor <;> linarith

theorem a03ZeroModeRatioPhysicalScale_residual_budget {T η β δ : ℝ}
    (hT : 1≤T) (hη : 0<η) (hβ : |β|≤η/32) (hδ : |δ|≤η/32)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (j : Fin 3) :
    T*(T^(-(1+η/4))*(g:ℝ)^(-1+β+δ-(1+η/4)-a03ZeroModeRatioSecondaryLine (η/4))*
      (a:ℝ)^(-1+β+η/4-a03ZeroModeRatioResidualLeftLine (η/4) j)*
      (b:ℝ)^(-1+δ+η/4-a03ZeroModeRatioResidualRightLine (η/4) j)*
      (a03ZeroModeRatioPhysicalScale T g a b)^((1+η/4)+a03ZeroModeRatioSecondaryLine (η/4)-β-δ))≤
    T^(1/2+η)*(g:ℝ)^(-1:ℝ)*
      (a:ℝ)^(a03ZeroModeRatioResidualAmplifierLeftExponent η j-1)*
      (b:ℝ)^(a03ZeroModeRatioResidualAmplifierRightExponent η j-1) := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  have ha1 : 1≤(a:ℝ) := by exact_mod_cast ha
  have hb1 : 1≤(b:ℝ) := by exact_mod_cast hb
  rw [a03ZeroModeRatioPhysicalScale_power_normalization hTp hg ha hb]
  have ht := a03ZeroModeRatioResidual_time_exponent_dominate hη hβ hδ
  have he := a03ZeroModeRatioResidualAmplifier_exponents_dominate hη hβ hδ j
  have htime : T*T^(a03ZeroModeRatioSecondaryLine (η/4)-β-δ)=
      T^(1+a03ZeroModeRatioSecondaryLine (η/4)-β-δ) := by
    calc
      _=T^(1:ℝ)*T^(a03ZeroModeRatioSecondaryLine (η/4)-β-δ) := by rw [Real.rpow_one]
      _=_ := by rw [←Real.rpow_add hTp]; congr 1; ring
  calc
    _=(T*T^(a03ZeroModeRatioSecondaryLine (η/4)-β-δ))*(g:ℝ)^(-1:ℝ)*
      (a:ℝ)^(((1+η/4)+a03ZeroModeRatioSecondaryLine (η/4))/2-1+(β-δ)/2+η/4-
        a03ZeroModeRatioResidualLeftLine (η/4) j)*
      (b:ℝ)^(((1+η/4)+a03ZeroModeRatioSecondaryLine (η/4))/2-1+(δ-β)/2+η/4-
        a03ZeroModeRatioResidualRightLine (η/4) j) := by ring
    _≤_ := by
      rw [htime]
      have hA : (a:ℝ)^(((1+η/4)+a03ZeroModeRatioSecondaryLine (η/4))/2-1+(β-δ)/2+η/4-
          a03ZeroModeRatioResidualLeftLine (η/4) j)≤
          (a:ℝ)^(a03ZeroModeRatioResidualAmplifierLeftExponent η j-1) :=
        Real.rpow_le_rpow_of_exponent_le ha1 (by linarith only [he.1])
      have hB : (b:ℝ)^(((1+η/4)+a03ZeroModeRatioSecondaryLine (η/4))/2-1+(δ-β)/2+η/4-
          a03ZeroModeRatioResidualRightLine (η/4) j)≤
          (b:ℝ)^(a03ZeroModeRatioResidualAmplifierRightExponent η j-1) :=
        Real.rpow_le_rpow_of_exponent_le hb1 (by linarith only [he.2])
      exact mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hT ht)
          (Real.rpow_nonneg (Nat.cast_nonneg g) _)) hA (by positivity) (by positivity))
        hB (by positivity) (by positivity)

end
end Sechstmoment.Source
