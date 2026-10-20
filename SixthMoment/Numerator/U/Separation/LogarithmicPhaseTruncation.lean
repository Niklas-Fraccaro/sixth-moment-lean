import Mathlib.Algebra.Order.Floor.Semiring
import SixthMoment.Numerator.U.Separation.BinomialPhase

namespace SixthMoment
open Complex Real Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phaseBinomial_uniform_power_remainder {θ : ℝ} (hθ : 0≤θ) (M : ℝ) :
    ∃ L : ℝ, 0<L ∧ ∀ T : ℝ, 1≤T → ∀ t r : ℝ,
      |t|≤2*T → 0≤r → r≤1/4 → T*r≤θ*Real.log T → ∀ x : ℂ, ‖x‖≤r →
      ∀ N : ℕ, L*Real.log T≤(N:ℝ) →
        ‖(1+x)^(-(t:ℂ)*I)-∑ k∈Finset.range N,
          phaseBinomialCoefficient (-(t:ℂ)*I) k*x^k‖≤T^(-M) := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let L : ℝ := (|M|+8*θ+1)/Real.log 2
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨L,hL,?_⟩
  intro T hT t r ht hr hr4 hTr x hx N hN
  have htpos : 0<T := zero_lt_one.trans_le hT
  have hlogT : 0≤Real.log T := Real.log_nonneg hT
  have hmul : (M+8*θ)*Real.log T≤Real.log 2*(N:ℝ) := by
    have hNl := mul_le_mul_of_nonneg_left hN hlog2.le
    have he : Real.log 2*(L*Real.log T)=(|M|+8*θ+1)*Real.log T := by
      dsimp [L]
      field_simp
    rw [he] at hNl
    exact (mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) hlogT).trans hNl
  have hb : 4*|t| * r≤8*θ*Real.log T := by
    have htr := mul_le_mul_of_nonneg_right ht hr
    nlinarith
  have hp : (2:ℝ)^N=Real.exp (Real.log 2*(N:ℝ)) := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ (1/(2:ℝ)^N)*Real.exp (4*|t| * r) :=
      phaseBinomial_remainder_exponential_bound hr hr4 t x hx N
    _ ≤ (1/(2:ℝ)^N)*Real.exp (8*θ*Real.log T) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb) (by positivity)
    _ = Real.exp (8*θ*Real.log T-Real.log 2*(N:ℝ)) := by
      rw [hp,one_div,← Real.exp_neg,← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.log T*(-M)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := (Real.rpow_def_of_pos htpos (-M)).symm

theorem phaseBinomial_logarithmic_cutoff {θ : ℝ} (hθ : 0≤θ) (M : ℝ) :
    ∃ L : ℝ, 0<L ∧ ∀ T : ℝ, Real.exp 1≤T →
      (⌈L*Real.log T⌉₊:ℝ)≤(L+1)*Real.log T ∧ ∀ t r : ℝ,
      |t|≤2*T → 0≤r → r≤1/4 → T*r≤θ*Real.log T → ∀ x : ℂ, ‖x‖≤r →
        ‖(1+x)^(-(t:ℂ)*I)-∑ k∈Finset.range ⌈L*Real.log T⌉₊,
          phaseBinomialCoefficient (-(t:ℂ)*I) k*x^k‖≤T^(-M) := by
  obtain ⟨L,hL,hb⟩ := phaseBinomial_uniform_power_remainder hθ M
  refine ⟨L,hL,?_⟩
  intro T hT
  have ht : 0<T := (Real.exp_pos 1).trans_le hT
  have hlog : 1≤Real.log T := (Real.le_log_iff_exp_le ht).mpr hT
  have hT1 : 1≤T := (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ)≤1)).trans hT
  refine ⟨?_,fun t r ht hr hr4 hTr x hx => hb T hT1 t r ht hr hr4 hTr x hx _ (Nat.le_ceil _)⟩
  have he := Nat.ceil_lt_add_one (mul_nonneg hL.le (by linarith : 0≤Real.log T))
  nlinarith

end
end SixthMoment
