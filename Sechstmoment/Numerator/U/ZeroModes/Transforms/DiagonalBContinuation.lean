import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.FixedDiagonalEulerMellin
import Sechstmoment.Numerator.U.ZeroModes.Ratio.EtaBounds

namespace Sechstmoment
open Complex Real Source Set
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03DiagonalBPrimeCorrection (p : ℕ) (α β γ δ s : ℂ) : ℂ :=
  bblrEtaCorrection p (α+γ+2*s) (β+γ+2*s) (α+β+γ+δ+4*s)

def a03DiagonalBPrimeRational (p : ℕ) (α β γ δ s : ℂ) (ν : ℕ) : ℂ :=
  ((p:ℂ)^(-γ))^ν+(p:ℂ)^(-δ)*
    (∑ k∈Finset.range ν,((p:ℂ)^(-γ))^k*((p:ℂ)^(-δ))^(ν-1-k))*
      a03DiagonalBPrimeCorrection p α β γ δ s

theorem a03DiagonalBPrime_geometric {p : ℕ} (hp : p.Prime) (s : ℂ)
    (hs : -(1/8:ℝ)≤s.re) :
    ((p:ℝ)^(1/64:ℝ))^2*‖(p:ℂ)^(-(1+2*s))‖<1 := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  rw [Complex.norm_natCast_cpow_of_pos hp.pos]
  norm_num [neg_re,add_re,one_re,mul_re]
  have hm : ((p:ℝ)^(1/64:ℝ))^2=(p:ℝ)^(1/32:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hp0.le]
    congr 1
    norm_num
  rw [hm,←Real.rpow_add hp0]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

theorem bblrBPrimeFactorAt_eq_rational {p : ℕ} (hp : p.Prime)
    (α β γ δ s : ℂ) (hα : ‖α‖≤1/64) (hβ : ‖β‖≤1/64)
    (hγ : ‖γ‖≤1/64) (hδ : ‖δ‖≤1/64) (hs : -(1/8:ℝ)≤s.re) (ν : ℕ) :
    bblrBPrimeFactorAt p α β γ δ s ν=a03DiagonalBPrimeRational p α β γ δ s ν := by
  have hd (z : ℂ) (hz : ‖z‖≤1/64) : ‖(p:ℂ)^(-z)‖≤(p:ℝ)^(1/64:ℝ) := by
    apply bblrPrimePowerNorm_le hp
    simp only [neg_re]
    have hh := (abs_le.mp ((Complex.abs_re_le_norm z).trans hz)).1
    linarith
  have he : bblrBPrimeFactorAt p α β γ δ s ν=
      pairShiftedPrimeSeries ((p:ℂ)^(-α)) ((p:ℂ)^(-β))
        ((p:ℂ)^(-γ)) ((p:ℂ)^(-δ)) ((p:ℂ)^(-(1+2*s))) ν /
      pairDiagonalPrimeSeries ((p:ℂ)^(-α)) ((p:ℂ)^(-β))
        ((p:ℂ)^(-γ)) ((p:ℂ)^(-δ)) ((p:ℂ)^(-(1+2*s))) := by
    unfold bblrBPrimeFactorAt pairShiftedPrimeSeries pairDiagonalPrimeSeries
    simp_rw [shiftedPairArithmetic_primePower hp]
  rw [he,pairShiftedPrimeSeries_ratio (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    (hd α hα) (hd β hβ) (hd γ hγ) (hd δ hδ) (a03DiagonalBPrime_geometric hp s hs)]
  unfold a03DiagonalBPrimeRational a03DiagonalBPrimeCorrection bblrEtaCorrection
  have hpC : (p:ℂ)≠0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h₁ : (p:ℂ)^(-α)*(p:ℂ)^(-γ)*(p:ℂ)^(-(1+2*s))=(p:ℂ)^(-(1+(α+γ+2*s))) := by
    rw [←Complex.cpow_add _ _ hpC,←Complex.cpow_add _ _ hpC]
    congr 1
    ring
  have h₂ : (p:ℂ)^(-γ)*(p:ℂ)^(-β)*(p:ℂ)^(-(1+2*s))=(p:ℂ)^(-(1+(β+γ+2*s))) := by
    rw [←Complex.cpow_add _ _ hpC,←Complex.cpow_add _ _ hpC]
    congr 1
    ring
  have h₃ : (p:ℂ)^(-α)*(p:ℂ)^(-δ)*(p:ℂ)^(-γ)*(p:ℂ)^(-β)*((p:ℂ)^(-(1+2*s)))^2=
      (p:ℂ)^(-(2+(α+β+γ+δ+4*s))) := by
    rw [pow_two]
    simp only [←mul_assoc]
    rw [←Complex.cpow_add _ _ hpC,←Complex.cpow_add _ _ hpC,
      ←Complex.cpow_add _ _ hpC,←Complex.cpow_add _ _ hpC,←Complex.cpow_add _ _ hpC]
    congr 1
    ring
  rw [h₁,h₂,h₃]
  ring

theorem a03DiagonalBPrimeCorrection_norm_le {p : ℕ} (hp : p.Prime)
    (α β γ δ s : ℂ) (hα : ‖α‖≤1/64) (hβ : ‖β‖≤1/64)
    (hγ : ‖γ‖≤1/64) (hδ : ‖δ‖≤1/64) (hs : -(1/8:ℝ)≤s.re) :
    ‖a03DiagonalBPrimeCorrection p α β γ δ s‖≤8 := by
  have hr (z : ℂ) (hz : ‖z‖≤1/64) : -(1/64:ℝ)≤z.re :=
    (abs_le.mp ((Complex.abs_re_le_norm z).trans hz)).1
  apply bblrEtaCorrection_norm_le_eight hp
  all_goals norm_num [add_re,one_re,mul_re]
  all_goals linarith [hr α hα,hr β hβ,hr γ hγ,hr δ hδ]

theorem a03DiagonalBPrimeRational_norm_le {p : ℕ} (hp : p.Prime)
    (α β γ δ s : ℂ) (hα : ‖α‖≤1/64) (hβ : ‖β‖≤1/64)
    (hγ : ‖γ‖≤1/64) (hδ : ‖δ‖≤1/64) (hs : -(1/8:ℝ)≤s.re) (ν : ℕ) :
    ‖a03DiagonalBPrimeRational p α β γ δ s ν‖≤8*(ν+1:ℝ)*((p:ℝ)^(1/64:ℝ))^ν := by
  let M : ℝ := (p:ℝ)^(1/64:ℝ)
  have hM : 0≤M := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hd (z : ℂ) (hz : ‖z‖≤1/64) : ‖(p:ℂ)^(-z)‖≤M := by
    apply bblrPrimePowerNorm_le hp
    simp only [neg_re]
    have hh := (abs_le.mp ((Complex.abs_re_le_norm z).trans hz)).1
    linarith
  have hδp := hd δ hδ
  have hC := a03DiagonalBPrimeCorrection_norm_le hp α β γ δ s hα hβ hγ hδ hs
  by_cases hν : ν=0
  · simp [hν,a03DiagonalBPrimeRational]
  have hν1 : 1≤ν := Nat.one_le_iff_ne_zero.mpr hν
  have hsum : ‖∑ k∈Finset.range ν,((p:ℂ)^(-γ))^k*((p:ℂ)^(-δ))^(ν-1-k)‖≤
      (ν:ℝ)*M^(ν-1) := by
    apply (norm_sum_le _ _).trans
    calc
      _≤∑ _k∈Finset.range ν,M^(ν-1) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul,norm_pow,norm_pow]
        calc
          _≤M^k*M^(ν-1-k) := mul_le_mul
            (pow_le_pow_left₀ (norm_nonneg _) (hd γ hγ) _)
            (pow_le_pow_left₀ (norm_nonneg _) (hd δ hδ) _) (by positivity) (by positivity)
          _=M^(ν-1) := by rw [←pow_add]; congr 1; have := Finset.mem_range.mp hk; omega
      _=_ := by simp
  have hc : ‖((p:ℂ)^(-γ))^ν‖≤M^ν := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hd γ hγ) _
  unfold a03DiagonalBPrimeRational
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  calc
    _≤M^ν+M*((ν:ℝ)*M^(ν-1))*8 := by gcongr
    _≤8*(ν+1:ℝ)*M^ν := by
      have hm : M*M^(ν-1)=M^ν := by
        calc
          _=M^(ν-1)*M := mul_comm _ _
          _=M^(ν-1+1) := (pow_succ _ _).symm
          _=_ := by congr 1; omega
      rw [show M*((ν:ℝ)*M^(ν-1))=(ν:ℝ)*M^ν by
        calc
          _=(ν:ℝ)*(M*M^(ν-1)) := by ring
          _=_ := by rw [hm]]
      nlinarith [pow_nonneg hM ν]

end
end Sechstmoment
