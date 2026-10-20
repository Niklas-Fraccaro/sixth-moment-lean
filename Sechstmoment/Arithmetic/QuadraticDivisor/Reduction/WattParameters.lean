import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Sechstmoment.Arithmetic.QuadraticDivisor.Reduction.MassBounds
import Std

namespace DivisorProof
open Real Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

structure WattScales where
  H : ℝ
  C : ℝ
  R : ℝ
  S : ℝ
  V : ℝ
  P : ℝ

def WattScales.product (p : WattScales) : ℝ := p.R*p.S*p.V*p.P
def WattScales.X (p : WattScales) : ℝ := Real.sqrt (p.product/(p.H*p.C))

def naturalWattScales (q : QuadraticScales) (ρ d d₁ d₂ d₃ d₄ : ℝ) : WattScales :=
  ⟨q.H/d,poissonLength q ρ d,q.A/d₁,q.B/d₃,q.M₁/d₂,q.N₁/d₄⟩

theorem naturalWatt_product (q : QuadraticScales) (ρ : ℝ)
    {d d₁ d₂ d₃ d₄ : ℝ} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (h₃ : 0 < d₃) (h₄ : 0 < d₄) (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) :
    (naturalWattScales q ρ d d₁ d₂ d₃ d₄).product = q.A*q.B*q.M₁*q.N₁/d^2 := by
  have hden : d₁*d₃*d₂*d₄ = d^2 := by
    calc _ = (d₁*d₂)*(d₃*d₄) := by ring
      _ = _ := by rw [h₁₂,h₃₄]; ring
  calc _ = q.A*q.B*q.M₁*q.N₁/(d₁*d₃*d₂*d₄) := by
        dsimp [naturalWattScales,WattScales.product]
        field_simp
      _ = _ := by rw [hden]

theorem naturalWatt_product_le_mass (q : QuadraticScales)
    (h : ∀ j, 1 ≤ q.size j) (ρ : ℝ) {d d₁ d₂ d₃ d₄ : ℝ}
    (hd : 1 ≤ d) (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : 0 < d₃) (h₄ : 0 < d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) :
    (naturalWattScales q ρ d d₁ d₂ d₃ d₄).product ≤ q.mass := by
  rw [naturalWatt_product q ρ h₁ h₂ h₃ h₄ h₁₂ h₃₄]
  have hprod := (poisson_scale_bounds q h).2.2.2.2
  have hprod0 : 0 ≤ q.A*q.B*q.M₁*q.N₁ := zero_le_one.trans (by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (h 0) (h 1)) (h 2)) (h 4))
  exact (div_le_self hprod0 (one_le_pow₀ hd)).trans hprod

theorem naturalWatt_X_sq (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    (ρ : ℝ) {d d₁ d₂ d₃ d₄ : ℝ} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (h₃ : 0 < d₃) (h₄ : 0 < d₄) (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) :
    (naturalWattScales q ρ d d₁ d₂ d₃ d₄).X^2 =
      Real.sqrt q.mass/(q.H*q.mass^(10*ρ)) := by
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have hH : 0 < q.H := lt_of_lt_of_le (by norm_num) (h 6)
  have hd : 0 < d := h₁₂ ▸ mul_pos h₁ h₂
  have hM : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hN : 0 < q.N₂ := lt_of_lt_of_le (by norm_num) (h 5)
  have hQpow : 0 < q.mass^(10*ρ) := Real.rpow_pos_of_pos hQ _
  have hsqrt : 0 < Real.sqrt q.mass := Real.sqrt_pos.mpr hQ
  have hprod : 0 ≤ (naturalWattScales q ρ d d₁ d₂ d₃ d₄).product := by
    rw [naturalWatt_product q ρ h₁ h₂ h₃ h₄ h₁₂ h₃₄]
    have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
    have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
    have hM₁ : 0 < q.M₁ := lt_of_lt_of_le (by norm_num) (h 2)
    have hN₁ : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (h 4)
    positivity
  unfold WattScales.X
  rw [Real.sq_sqrt (div_nonneg hprod (by
    change 0 ≤ (q.H/d)*poissonLength q ρ d
    exact mul_nonneg (div_pos hH hd).le (poissonLength_pos q h ρ hd).le))]
  rw [naturalWatt_product q ρ h₁ h₂ h₃ h₄ h₁₂ h₃₄]
  change (q.A*q.B*q.M₁*q.N₁/d^2)/
    ((q.H/d)*(Real.sqrt q.mass/(d*q.M₂*q.N₂)*q.mass^(10*ρ))) = _
  field_simp
  have hm : q.A*q.B*q.M₁*q.N₁*q.M₂*q.N₂ = q.mass := by
    dsimp [QuadraticScales.mass,QuadraticScales.M,QuadraticScales.N]
    ring
  nlinarith [Real.sq_sqrt hQ.le]

theorem naturalWatt_X_identity (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    (ρ : ℝ) {d d₁ d₂ d₃ d₄ : ℝ} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (h₃ : 0 < d₃) (h₄ : 0 < d₄) (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) :
    (naturalWattScales q ρ d d₁ d₂ d₃ d₄).X =
      q.mass^(1/4 : ℝ)*q.H^(-1/2 : ℝ)*q.mass^(-5*ρ) := by
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have hH : 0 < q.H := lt_of_lt_of_le (by norm_num) (h 6)
  have hsq := naturalWatt_X_sq q h ρ h₁ h₂ h₃ h₄ h₁₂ h₃₄
  have hsq' : (q.mass^(1/4 : ℝ)*q.H^(-1/2 : ℝ)*q.mass^(-5*ρ))^2 =
      Real.sqrt q.mass/(q.H*q.mass^(10*ρ)) := by
    rw [mul_pow,mul_pow,← Real.rpow_mul_natCast hQ.le,← Real.rpow_mul_natCast hH.le,
      ← Real.rpow_mul_natCast hQ.le]
    norm_num
    rw [show -(5*ρ*2) = -(10*ρ) by ring,Real.rpow_neg hQ.le,Real.rpow_neg_one,
      Real.sqrt_eq_rpow]
    ring
  have hX : 0 ≤ (naturalWattScales q ρ d d₁ d₂ d₃ d₄).X := Real.sqrt_nonneg _
  have hY : 0 ≤ q.mass^(1/4 : ℝ)*q.H^(-1/2 : ℝ)*q.mass^(-5*ρ) := by positivity
  nlinarith

theorem shift_le_sqrt_AB {ρ δ K : ℝ} (hρ : 0 ≤ ρ) (hK : 1 ≤ K)
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hadm : QuadraticAdmissible ρ δ K bounds q α β W) :
    q.H ≤ K*Real.sqrt (q.A*q.B)*q.mass^ρ := by
  have hAB : 0 < q.A*q.B := lt_of_lt_of_le (by norm_num) (product_AB_le_mass q hadm.1).1
  have hKp : 0 ≤ K := by linarith
  have hpow : (q.A*q.B)^ρ ≤ q.mass^ρ :=
    Real.rpow_le_rpow hAB.le (product_AB_le_mass q hadm.1).2 hρ
  have hH := hadm.2.2.2.1
  rw [Real.rpow_add hAB,← Real.sqrt_eq_rpow] at hH
  apply hH.trans
  calc K*(Real.sqrt (q.A*q.B)*(q.A*q.B)^ρ) =
      (K*Real.sqrt (q.A*q.B))*(q.A*q.B)^ρ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg hKp (Real.sqrt_nonneg _))

theorem sqrt_mass_le_inner_product {ρ : ℝ} (_hρ : 0 ≤ ρ)
    {q : QuadraticScales} (h : ∀ j, 1 ≤ q.size j)
    (hM : q.M₁ ≤ q.M₂*q.mass^ρ) (hN : q.N₁ ≤ q.N₂*q.mass^ρ) :
    Real.sqrt q.mass ≤ Real.sqrt (q.A*q.B)*(q.M₂*q.N₂)*q.mass^ρ := by
  have hAB : 0 < q.A*q.B := lt_of_lt_of_le (by norm_num) (product_AB_le_mass q h).1
  have hM₂ : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hN₂ : 0 < q.N₂ := lt_of_lt_of_le (by norm_num) (h 5)
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have hM₁ : 0 ≤ q.M₁ := zero_le_one.trans (h 2)
  have hN₁ : 0 ≤ q.N₁ := zero_le_one.trans (h 4)
  have hmn : q.M₁*q.N₁ ≤ (q.M₂*q.N₂)*(q.mass^ρ)^2 := by
    calc _ ≤ (q.M₂*q.mass^ρ)*(q.N₂*q.mass^ρ) := mul_le_mul hM hN hN₁ (by positivity)
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_right hmn (mul_nonneg hAB.le (mul_pos hM₂ hN₂).le)
  have hsq : (Real.sqrt q.mass)^2 ≤
      (Real.sqrt (q.A*q.B)*(q.M₂*q.N₂)*q.mass^ρ)^2 := by
    rw [Real.sq_sqrt hQ.le,mul_pow,mul_pow,Real.sq_sqrt hAB.le]
    convert hm using 1 <;> dsimp [QuadraticScales.mass,QuadraticScales.M,QuadraticScales.N] <;> ring
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp hsq

theorem doubled_dyadic_support {U : ℝ} {n : ℕ} (hn : 0 < n)
    (hupper : (n : ℝ) ≤ 2*U) : 1 ≤ 2*U := by
  exact (show (1 : ℝ) ≤ n by exact_mod_cast hn).trans hupper

end
end DivisorProof



namespace DivisorProof
open Real Finset Classical Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

def wattGrowthExponent (ρ δ : ℝ) : ℝ := 1/4-shiftGrowthExponent ρ δ/2-5*ρ

theorem wattGrowthExponent_identity {ρ δ : ℝ} (hδ : 0 < δ) :
    wattGrowthExponent ρ δ = δ/(4*(1+δ))-ρ/(2*(1+δ))-5*ρ := by
  unfold wattGrowthExponent shiftGrowthExponent
  field_simp
  ring

theorem wattGrowthExponent_gt {ρ δ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hbound : ρ ≤ δ/(1000*(1+δ))) : ρ < wattGrowthExponent ρ δ := by
  rw [wattGrowthExponent_identity hδ]
  exact watt_first_size_exponent hδ hρ hbound

theorem cutoff_div_sqrt_bound (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    (ρ : ℝ) {d : ℝ} (hcut : d ≤ gcdCutoff q ρ) :
    d/Real.sqrt (q.A*q.B) ≤ q.mass^(-100*ρ) := by
  have hAB : 0 < q.A*q.B := lt_of_lt_of_le (by norm_num) (product_AB_le_mass q h).1
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hAB)).mpr
  simpa only [gcdCutoff,Real.sqrt_eq_rpow,mul_comm] using hcut

theorem cutoff_second_power_reserve (q : QuadraticScales)
    (h : ∀ j, 1 ≤ q.size j) (ρ : ℝ) {d : ℝ} (hcut : d ≤ gcdCutoff q ρ) :
    (d/Real.sqrt (q.A*q.B))*(q.mass^ρ)^13 ≤ q.mass^(-87*ρ) := by
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  calc _ ≤ q.mass^(-100*ρ)*(q.mass^ρ)^13 :=
      mul_le_mul_of_nonneg_right (cutoff_div_sqrt_bound q h ρ hcut) (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hQ.le,← Real.rpow_add hQ]
      congr 1
      norm_num
      ring

theorem cutoff_square_bound (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    (ρ : ℝ) {d : ℝ} (hd : 0 ≤ d) (hcut : d ≤ gcdCutoff q ρ) :
    d^2 ≤ (q.A*q.B)*q.mass^(-200*ρ) := by
  have hAB : 0 < q.A*q.B := lt_of_lt_of_le (by norm_num) (product_AB_le_mass q h).1
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have hs : d ≤ Real.sqrt (q.A*q.B)*q.mass^(-100*ρ) := by
    simpa only [gcdCutoff,Real.sqrt_eq_rpow] using hcut
  calc d^2 ≤ (Real.sqrt (q.A*q.B)*q.mass^(-100*ρ))^2 :=
      (sq_le_sq₀ hd (by positivity)).mpr hs
    _ = _ := by
      rw [mul_pow,Real.sq_sqrt hAB.le,← Real.rpow_mul_natCast hQ.le]
      congr 2
      norm_num
      ring

theorem cutoff_third_power_reserve (q : QuadraticScales)
    (h : ∀ j, 1 ≤ q.size j) (ρ : ℝ) {d : ℝ} (hd : 0 ≤ d) (hcut : d ≤ gcdCutoff q ρ) :
    (2*d^2/(q.A*q.B))*q.mass^ρ ≤ 2*q.mass^(-199*ρ) := by
  have hAB : 0 < q.A*q.B := lt_of_lt_of_le (by norm_num) (product_AB_le_mass q h).1
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have hdiv : d^2/(q.A*q.B) ≤ q.mass^(-200*ρ) :=
    (div_le_iff₀ hAB).mpr (by simpa only [mul_comm] using cutoff_square_bound q h ρ hd hcut)
  calc _ = 2*(d^2/(q.A*q.B))*q.mass^ρ := by ring
    _ ≤ 2*q.mass^(-200*ρ)*q.mass^ρ := by gcongr
    _ = _ := by
      rw [mul_assoc,← Real.rpow_add hQ]
      congr 2
      ring

theorem admissible_shift_growth_square_constant {ρ δ K : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hgap : 2*ρ < δ) (hK : 1 ≤ K)
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hadm : QuadraticAdmissible ρ δ K bounds q α β W) :
    q.H ≤ K^2*q.mass^(shiftGrowthExponent ρ δ) := by
  have hθ := shiftGrowthExponent_lt_half hδ hgap
  have hKθ : K^(shiftGrowthExponent ρ δ) ≤ K := by
    calc _ ≤ K^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
      _ = _ := Real.rpow_one _
  have hQ : 0 ≤ q.mass := zero_le_one.trans (poisson_scale_bounds q hadm.1).1
  apply (admissible_shift_growth hρ hδ hK hadm).trans
  calc _ ≤ (K*K)*q.mass^(shiftGrowthExponent ρ δ) := by gcongr
    _ = _ := by ring

theorem naturalWatt_X_lower {ρ δ K : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hgap : 2*ρ < δ) (hK : 1 ≤ K)
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hadm : QuadraticAdmissible ρ δ K bounds q α β W)
    {d d₁ d₂ d₃ d₄ : ℝ} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (h₃ : 0 < d₃) (h₄ : 0 < d₄) (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) :
    q.mass^(wattGrowthExponent ρ δ)/K ≤ (naturalWattScales q ρ d d₁ d₂ d₃ d₄).X := by
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q hadm.1).1
  have hH : 0 < q.H := lt_of_lt_of_le (by norm_num) (hadm.1 6)
  have hKp : 0 < K := by linarith
  let θ := shiftGrowthExponent ρ δ
  have hupper := admissible_shift_growth_square_constant hρ hδ hgap hK hadm
  have hHpow : (K^2*q.mass^θ)^(-1/2 : ℝ) ≤ q.H^(-1/2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hH hupper (by norm_num)
  have halg : q.mass^(wattGrowthExponent ρ δ)/K =
      q.mass^(1/4 : ℝ)*(K^2*q.mass^θ)^(-1/2 : ℝ)*q.mass^(-5*ρ) := by
    rw [Real.mul_rpow (sq_nonneg K) (Real.rpow_nonneg hQ.le _),
      ← Real.rpow_natCast,← Real.rpow_mul hKp.le,← Real.rpow_mul hQ.le]
    norm_num
    rw [Real.rpow_neg_one]
    have hexp : wattGrowthExponent ρ δ = (1/4+-(θ*(1/2)))+-(5*ρ) := by
      dsimp [wattGrowthExponent,θ]
      ring
    rw [hexp,Real.rpow_add hQ,Real.rpow_add hQ]
    ring
  rw [halg,naturalWatt_X_identity q hadm.1 ρ h₁ h₂ h₃ h₄ h₁₂ h₃₄]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHpow
    (Real.rpow_nonneg hQ.le _)) (Real.rpow_nonneg hQ.le _)

theorem naturalWatt_first_size_eventually {ρ δ K F : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hbound : ρ ≤ δ/(1000*(1+δ)))
    (hK : 1 ≤ K) (hF : 0 ≤ F) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ (bounds : ℕ → ℝ) (q : QuadraticScales)
      (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
      QuadraticAdmissible ρ δ K bounds q α β W → Q₀ ≤ q.mass →
      ∀ d d₁ d₂ d₃ d₄ : ℝ, 1 ≤ d → 0 < d₁ → 0 < d₂ → 0 < d₃ → 0 < d₄ →
        d₁*d₂ = d → d₃*d₄ = d →
        F*(naturalWattScales q ρ d d₁ d₂ d₃ d₄).product^ρ ≤
          (naturalWattScales q ρ d d₁ d₂ d₃ d₄).X := by
  have hexp : 0 < wattGrowthExponent ρ δ-ρ := by linarith [wattGrowthExponent_gt hδ hρ hbound]
  obtain ⟨Q₁,hQ₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hexp).eventually (eventually_ge_atTop (K*F)))
  refine ⟨max Q₁ 1,le_max_right _ _,?_⟩
  intro bounds q α β W hadm hmass d d₁ d₂ d₃ d₄ hd h₁ h₂ h₃ h₄ h₁₂ h₃₄
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q hadm.1).1
  have hKp : 0 < K := by linarith
  have hp : 0 ≤ (naturalWattScales q ρ d d₁ d₂ d₃ d₄).product := by
    rw [naturalWatt_product q ρ h₁ h₂ h₃ h₄ h₁₂ h₃₄]
    have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (hadm.1 0)
    have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (hadm.1 1)
    have hM : 0 < q.M₁ := lt_of_lt_of_le (by norm_num) (hadm.1 2)
    have hN : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (hadm.1 4)
    positivity
  have hpow : (naturalWattScales q ρ d d₁ d₂ d₃ d₄).product^ρ ≤ q.mass^ρ :=
    Real.rpow_le_rpow hp (naturalWatt_product_le_mass q hadm.1 ρ hd h₁ h₂ h₃ h₄ h₁₂ h₃₄) hρ.le
  have he := hQ₁ q.mass ((le_max_left _ _).trans hmass)
  have he' : F*q.mass^ρ ≤ q.mass^(wattGrowthExponent ρ δ)/K := by
    apply (le_div_iff₀ hKp).mpr
    have hm := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hQ.le ρ)
    rw [← Real.rpow_add hQ,sub_add_cancel] at hm
    nlinarith
  exact (mul_le_mul_of_nonneg_left hpow hF).trans
    (he'.trans (naturalWatt_X_lower hρ hδ (rho_reserve hδ hρ hbound).2 hK hadm h₁ h₂ h₃ h₄ h₁₂ h₃₄))

end
end DivisorProof



namespace DivisorProof
open Real Finset Classical Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 3000000

def WattScales.secondRatio (p : WattScales) : ℝ := p.H^2*p.C/(p.R*p.S)^2
def WattScales.thirdRatio (p : WattScales) (ρ : ℝ) : ℝ :=
  (p.S*p.P/p.V)*p.product^ρ/(p.R*p.S)^2

theorem naturalWatt_second_ratio (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    (ρ d₂ d₄ : ℝ) {d d₁ d₃ : ℝ} (hd : 0 < d) (h₁ : 0 < d₁) (h₃ : 0 < d₃) :
    (naturalWattScales q ρ d d₁ d₂ d₃ d₄).secondRatio =
      ((d₁*d₃)^2*q.H^2*Real.sqrt q.mass*q.mass^(10*ρ))/
        (d^3*q.M₂*q.N₂*(q.A*q.B)^2) := by
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hM : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hN : 0 < q.N₂ := lt_of_lt_of_le (by norm_num) (h 5)
  dsimp [WattScales.secondRatio,naturalWattScales,poissonLength]
  field_simp

theorem naturalWatt_third_ratio (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    (ρ : ℝ) {d d₁ d₂ d₃ d₄ : ℝ} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (h₃ : 0 < d₃) (_h₄ : 0 < d₄) (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) :
    (naturalWattScales q ρ d d₁ d₂ d₃ d₄).thirdRatio ρ =
      (d₁*d₃^2*q.B*q.N₁/(q.M₁*(q.A*q.B)^2))*
        (naturalWattScales q ρ d d₁ d₂ d₃ d₄).product^ρ := by
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hM : 0 < q.M₁ := lt_of_lt_of_le (by norm_num) (h 2)
  have hd : 0 < d := h₁₂ ▸ mul_pos h₁ h₂
  have hd₂ : d₂ = d/d₁ := (eq_div_iff h₁.ne').mpr (by nlinarith [h₁₂])
  have hd₄ : d₄ = d/d₃ := (eq_div_iff h₃.ne').mpr (by nlinarith [h₃₄])
  have halg : ((q.B/d₃)*(q.N₁/d₄)/(q.M₁/d₂))/((q.A/d₁)*(q.B/d₃))^2 =
      d₁*d₃^2*q.B*q.N₁/(q.M₁*(q.A*q.B)^2) := by
    rw [hd₂,hd₄]
    field_simp
  change ((q.B/d₃)*(q.N₁/d₄)/(q.M₁/d₂))*
    (naturalWattScales q ρ d d₁ d₂ d₃ d₄).product^ρ/((q.A/d₁)*(q.B/d₃))^2 = _
  rw [mul_div_right_comm,halg]

theorem naturalWatt_second_ratio_le {ρ δ K : ℝ} (hρ : 0 < ρ) (hK : 1 ≤ K)
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hadm : QuadraticAdmissible ρ δ K bounds q α β W)
    {d d₁ d₂ d₃ d₄ : ℝ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    (h₃ : 1 ≤ d₃) (h₄ : 1 ≤ d₄) (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d)
    (hcut : d ≤ gcdCutoff q ρ) :
    (naturalWattScales q ρ d d₁ d₂ d₃ d₄).secondRatio ≤ K^2*q.mass^(-87*ρ) := by
  have h := hadm.1
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hM : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hN : 0 < q.N₂ := lt_of_lt_of_le (by norm_num) (h 5)
  have hH : 0 ≤ q.H := zero_le_one.trans (h 6)
  have hAB : 0 < q.A*q.B := mul_pos hA hB
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have hd : 0 < d := h₁₂ ▸ mul_pos (by linarith) (by linarith)
  have hKp : 0 ≤ K := by linarith
  have hd₁ : d₁ ≤ d := by nlinarith
  have hd₃ : d₃ ≤ d := by nlinarith
  have hdd : (d₁*d₃)^2 ≤ d^4 := by
    calc _ ≤ (d*d)^2 := by gcongr
      _ = _ := by ring
  have hHs : q.H^2 ≤ K^2*(q.A*q.B)*(q.mass^ρ)^2 := by
    have hh := pow_le_pow_left₀ hH (shift_le_sqrt_AB hρ.le hK hadm) 2
    simpa only [mul_pow,Real.sq_sqrt hAB.le] using hh
  have hroot := sqrt_mass_le_inner_product hρ.le h hadm.2.1 hadm.2.2.1
  have h10 : q.mass^(10*ρ) = (q.mass^ρ)^10 := by
    rw [← Real.rpow_mul_natCast hQ.le]
    congr 1
    norm_num
    ring
  rw [naturalWatt_second_ratio q h ρ d₂ d₄ hd (by linarith) (by linarith),h10]
  calc _ ≤ (d^4*(K^2*(q.A*q.B)*(q.mass^ρ)^2)*
      (Real.sqrt (q.A*q.B)*(q.M₂*q.N₂)*q.mass^ρ)*(q.mass^ρ)^10)/
        (d^3*q.M₂*q.N₂*(q.A*q.B)^2) := by
          gcongr
    _ = K^2*((d/Real.sqrt (q.A*q.B))*(q.mass^ρ)^13) := by
      have hs : (Real.sqrt (q.A*q.B))^2 = q.A*q.B := Real.sq_sqrt hAB.le
      have hr : 0 < Real.sqrt (q.A*q.B) := Real.sqrt_pos.mpr hAB
      field_simp
      ring_nf
      rw [hs]
    _ ≤ _ := mul_le_mul_of_nonneg_left (cutoff_second_power_reserve q h ρ hcut) (sq_nonneg K)

theorem naturalWatt_third_ratio_le {ρ δ K : ℝ} (hρ : 0 < ρ)
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hadm : QuadraticAdmissible ρ δ K bounds q α β W)
    {d d₁ d₂ d₃ d₄ : ℝ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    (h₃ : 1 ≤ d₃) (h₄ : 1 ≤ d₄) (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d)
    (hd₃B : d₃ ≤ 2*q.B) (hcut : d ≤ gcdCutoff q ρ) :
    (naturalWattScales q ρ d d₁ d₂ d₃ d₄).thirdRatio ρ ≤ 2*q.mass^(-199*ρ) := by
  have h := hadm.1
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hM : 0 < q.M₁ := lt_of_lt_of_le (by norm_num) (h 2)
  have hN : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (h 4)
  have hAB : 0 < q.A*q.B := mul_pos hA hB
  have hd : 1 ≤ d := by nlinarith
  have hd₁ : d₁ ≤ d := by nlinarith
  have hd₃ : d₃ ≤ d := by nlinarith
  have hprod : d₁*d₃ ≤ d^2 := by
    calc d₁*d₃ ≤ d*d := by gcongr
      _ = _ := by ring
  have hcoef : d₁*d₃^2 ≤ 2*q.B*d^2 := by
    calc d₁*d₃^2 = (d₁*d₃)*d₃ := by ring
      _ ≤ d^2*(2*q.B) := mul_le_mul hprod hd₃B (by linarith) (sq_nonneg _)
      _ = _ := by ring
  have horient : q.B*q.N₁ ≤ q.A*q.M₁ := hadm.2.2.2.2.2.2.2.1
  have hnum : d₁*d₃^2*q.B*q.N₁ ≤ 2*d^2*(q.A*q.B*q.M₁) := by
    calc _ = (d₁*d₃^2)*(q.B*q.N₁) := by ring
      _ ≤ (2*q.B*d^2)*(q.A*q.M₁) := mul_le_mul hcoef horient (by positivity) (by positivity)
      _ = _ := by ring
  have hbase : d₁*d₃^2*q.B*q.N₁/(q.M₁*(q.A*q.B)^2) ≤ 2*d^2/(q.A*q.B) := by
    apply (div_le_div_iff₀ (by positivity) hAB).mpr
    convert mul_le_mul_of_nonneg_right hnum hAB.le using 1
    ring
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have hp0 : 0 ≤ (naturalWattScales q ρ d d₁ d₂ d₃ d₄).product := by
    rw [naturalWatt_product q ρ (by linarith) (by linarith) (by linarith) (by linarith) h₁₂ h₃₄]
    positivity
  have hpow := Real.rpow_le_rpow hp0
    (naturalWatt_product_le_mass q h ρ hd (by linarith) (by linarith) (by linarith) (by linarith) h₁₂ h₃₄) hρ.le
  rw [naturalWatt_third_ratio q h ρ (by linarith) (by linarith) (by linarith) (by linarith) h₁₂ h₃₄]
  exact (mul_le_mul hbase hpow (Real.rpow_nonneg hp0 ρ) (by positivity)).trans
    (cutoff_third_power_reserve q h ρ (by linarith) hcut)

end
end DivisorProof



namespace DivisorProof
open Real Finset Classical Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2500000

theorem naturalWatt_all_sizes_eventually {ρ δ K F : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hbound : ρ ≤ δ/(1000*(1+δ)))
    (hK : 1 ≤ K) (hF : 0 ≤ F) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ (bounds : ℕ → ℝ) (q : QuadraticScales)
      (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
      QuadraticAdmissible ρ δ K bounds q α β W → Q₀ ≤ q.mass →
      ∀ d d₁ d₂ d₃ d₄ : ℝ, 1 ≤ d → 1 ≤ d₁ → 1 ≤ d₂ → 1 ≤ d₃ → 1 ≤ d₄ →
        d₁*d₂ = d → d₃*d₄ = d → d₃ ≤ 2*q.B → d ≤ gcdCutoff q ρ →
        let p := naturalWattScales q ρ d d₁ d₂ d₃ d₄
        F*p.product^ρ ≤ p.X ∧ F*(p.H^2*p.C) ≤ (p.R*p.S)^2 ∧
          F*(p.S*p.P/p.V)*p.product^ρ ≤ (p.R*p.S)^2 := by
  obtain ⟨Q₁,hQ₁,hfirst⟩ := naturalWatt_first_size_eventually hρ hδ hbound hK hF
  have he₂ := (tendsto_rpow_atTop (by linarith : 0 < 87*ρ)).eventually
    (eventually_ge_atTop (F*K^2))
  have he₃ := (tendsto_rpow_atTop (by linarith : 0 < 199*ρ)).eventually
    (eventually_ge_atTop (2*F))
  obtain ⟨Q₂,hQ₂⟩ := eventually_atTop.mp (he₂.and he₃)
  refine ⟨max Q₁ Q₂,hQ₁.trans (le_max_left _ _),?_⟩
  intro bounds q α β W hadm hmass d d₁ d₂ d₃ d₄ hd h₁ h₂ h₃ h₄ h₁₂ h₃₄ hd₃B hcut
  dsimp only
  let p := naturalWattScales q ρ d d₁ d₂ d₃ d₄
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q hadm.1).1
  obtain ⟨hpow₂,hpow₃⟩ := hQ₂ q.mass ((le_max_right _ _).trans hmass)
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (hadm.1 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (hadm.1 1)
  have hden : 0 < (p.R*p.S)^2 := by
    change 0 < ((q.A/d₁)*(q.B/d₃))^2
    positivity
  have hsecond : F*p.secondRatio ≤ 1 := by
    calc _ ≤ F*(K^2*q.mass^(-87*ρ)) := mul_le_mul_of_nonneg_left
          (naturalWatt_second_ratio_le hρ hK hadm h₁ h₂ h₃ h₄ h₁₂ h₃₄ hcut) hF
      _ = (F*K^2)/q.mass^(87*ρ) := by rw [show -87*ρ = -(87*ρ) by ring,Real.rpow_neg hQ.le]; ring
      _ ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hQ _)).mpr hpow₂
  have hthird : F*p.thirdRatio ρ ≤ 1 := by
    calc _ ≤ F*(2*q.mass^(-199*ρ)) := mul_le_mul_of_nonneg_left
          (naturalWatt_third_ratio_le hρ hadm h₁ h₂ h₃ h₄ h₁₂ h₃₄ hd₃B hcut) hF
      _ = (2*F)/q.mass^(199*ρ) := by rw [show -199*ρ = -(199*ρ) by ring,Real.rpow_neg hQ.le]; ring
      _ ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hQ _)).mpr hpow₃
  refine ⟨hfirst bounds q α β W hadm ((le_max_left _ _).trans hmass)
    d d₁ d₂ d₃ d₄ hd (by linarith) (by linarith) (by linarith) (by linarith) h₁₂ h₃₄,?_,?_⟩
  · apply (div_le_one hden).mp
    convert hsecond using 1
    dsimp [WattScales.secondRatio]
    ring
  · apply (div_le_one hden).mp
    convert hthird using 1
    dsimp [WattScales.thirdRatio]
    ring

theorem canonical_divisor_upper_bounds {q : QuadraticScales}
    (h : ∀ j, 1 ≤ q.size j) {n : Fin 5 → ℕ} (hn : n ∈ quadraticMainIndexSet q) :
    (splitLeft (n 0) (outerGCD n) : ℝ) ≤ 2*q.A ∧
      (splitRight (n 0) (outerGCD n) : ℝ) ≤ 2*q.M₁ ∧
      (splitLeft (n 1) (outerGCD n) : ℝ) ≤ 2*q.B ∧
      (splitRight (n 1) (outerGCD n) : ℝ) ≤ 2*q.N₁ := by
  have hpos (j : Fin 5) := (quadraticMainIndexSet_coordinate_bounds q h hn j).1
  have hd := outerGCD_pos hn
  have hdiv₁ : outerGCD n ∣ n 0*n 2 := Nat.gcd_dvd_left _ _
  have hdiv₂ : outerGCD n ∣ n 1*n 3 := Nat.gcd_dvd_right _ _
  have h₁ : splitLeft (n 0) (outerGCD n) ≤ n 0 := Nat.le_of_dvd (hpos 0) (Nat.gcd_dvd_left _ _)
  have h₂ : splitRight (n 0) (outerGCD n) ≤ n 2 :=
    Nat.le_of_dvd (hpos 2) (splitRight_dvd_inner hd hdiv₁)
  have h₃ : splitLeft (n 1) (outerGCD n) ≤ n 1 := Nat.le_of_dvd (hpos 1) (Nat.gcd_dvd_left _ _)
  have h₄ : splitRight (n 1) (outerGCD n) ≤ n 3 :=
    Nat.le_of_dvd (hpos 3) (splitRight_dvd_inner hd hdiv₂)
  exact ⟨(by exact_mod_cast h₁ : (splitLeft (n 0) (outerGCD n) : ℝ) ≤ n 0).trans
      (quadraticMainIndexSet_coordinate_bounds q h hn 0).2,
    (by exact_mod_cast h₂ : (splitRight (n 0) (outerGCD n) : ℝ) ≤ n 2).trans
      (quadraticMainIndexSet_coordinate_bounds q h hn 2).2,
    (by exact_mod_cast h₃ : (splitLeft (n 1) (outerGCD n) : ℝ) ≤ n 1).trans
      (quadraticMainIndexSet_coordinate_bounds q h hn 1).2,
    (by exact_mod_cast h₄ : (splitRight (n 1) (outerGCD n) : ℝ) ≤ n 3).trans
      (quadraticMainIndexSet_coordinate_bounds q h hn 3).2⟩

def canonicalWattScales (q : QuadraticScales) (ρ : ℝ) (n : Fin 5 → ℕ) : WattScales :=
  naturalWattScales q ρ (outerGCD n) (splitLeft (n 0) (outerGCD n))
    (splitRight (n 0) (outerGCD n)) (splitLeft (n 1) (outerGCD n))
    (splitRight (n 1) (outerGCD n))

theorem canonicalWatt_all_sizes_eventually {ρ δ K F : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hbound : ρ ≤ δ/(1000*(1+δ)))
    (hK : 1 ≤ K) (hF : 0 ≤ F) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ (bounds : ℕ → ℝ) (q : QuadraticScales)
      (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
      QuadraticAdmissible ρ δ K bounds q α β W → Q₀ ≤ q.mass →
      ∀ n ∈ quadraticMainIndexSet q, (outerGCD n : ℝ) ≤ gcdCutoff q ρ →
        let p := canonicalWattScales q ρ n
        F*p.product^ρ ≤ p.X ∧ F*(p.H^2*p.C) ≤ (p.R*p.S)^2 ∧
          F*(p.S*p.P/p.V)*p.product^ρ ≤ (p.R*p.S)^2 := by
  obtain ⟨Q₀,hQ₀,hsize⟩ := naturalWatt_all_sizes_eventually hρ hδ hbound hK hF
  refine ⟨Q₀,hQ₀,?_⟩
  intro bounds q α β W hadm hmass n hn hcut
  have hd := outerGCD_pos hn
  have h₁ : (1 : ℝ) ≤ splitLeft (n 0) (outerGCD n) := by exact_mod_cast splitLeft_pos (n 0) hd
  have h₂ : (1 : ℝ) ≤ splitRight (n 0) (outerGCD n) := by exact_mod_cast splitRight_pos (n 0) hd
  have h₃ : (1 : ℝ) ≤ splitLeft (n 1) (outerGCD n) := by exact_mod_cast splitLeft_pos (n 1) hd
  have h₄ : (1 : ℝ) ≤ splitRight (n 1) (outerGCD n) := by exact_mod_cast splitRight_pos (n 1) hd
  have h₁₂ : (splitLeft (n 0) (outerGCD n) : ℝ)*splitRight (n 0) (outerGCD n) = outerGCD n := by
    exact_mod_cast split_factors_mul (n 0) (outerGCD n)
  have h₃₄ : (splitLeft (n 1) (outerGCD n) : ℝ)*splitRight (n 1) (outerGCD n) = outerGCD n := by
    exact_mod_cast split_factors_mul (n 1) (outerGCD n)
  exact hsize bounds q α β W hadm hmass _ _ _ _ _ (by exact_mod_cast hd)
    h₁ h₂ h₃ h₄ h₁₂ h₃₄ (canonical_divisor_upper_bounds hadm.1 hn).2.2.1 hcut

theorem canonicalWatt_doubled_scales_ge_one {bounds : ℕ → ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (ρ : ℝ) {n : Fin 5 → ℕ} (hn : n ∈ quadraticMainIndexSet q)
    (hne : poissonOuterWeight q α β W n ≠ 0) {l : ℤ} (hl : l ≠ 0)
    (hcut : sourceCutoff ((l : ℝ)/poissonLength q ρ (outerGCD n)) ≠ 0) :
    let p := canonicalWattScales q ρ n
    1 ≤ 2*p.H ∧ 1 ≤ 2*p.C ∧ 1 ≤ 2*p.R ∧ 1 ≤ 2*p.S ∧
      1 ≤ 2*p.V ∧ 1 ≤ 2*p.P := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := canonical_divisor_upper_bounds h hn
  have hd := outerGCD_pos hn
  have hdr : (0 : ℝ) < outerGCD n := by exact_mod_cast hd
  have hdl₁ : (0 : ℝ) < splitLeft (n 0) (outerGCD n) := by exact_mod_cast splitLeft_pos (n 0) hd
  have hdr₁ : (0 : ℝ) < splitRight (n 0) (outerGCD n) := by exact_mod_cast splitRight_pos (n 0) hd
  have hdl₂ : (0 : ℝ) < splitLeft (n 1) (outerGCD n) := by exact_mod_cast splitLeft_pos (n 1) hd
  have hdr₂ : (0 : ℝ) < splitRight (n 1) (outerGCD n) := by exact_mod_cast splitRight_pos (n 1) hd
  have hL := poissonLength_pos q h ρ hdr
  have hLhalf : 1/2 < poissonLength q ρ (outerGCD n) := by
    by_contra hh
    exact hcut (sourceCutoff_zero_of_short hL (not_lt.mp hh) hl)
  have hk : (1 : ℝ) ≤ n 4 := by exact_mod_cast (quadraticMainIndexSet_coordinate_bounds q h hn 4).1
  have hdH : (outerGCD n : ℝ) ≤ 2*q.H :=
    (le_mul_of_one_le_right hdr.le hk).trans (outer_weight_shift_bound h hw hne)
  dsimp only [canonicalWattScales,naturalWattScales]
  refine ⟨?_,by linarith,?_,?_,?_,?_⟩
  all_goals rw [← mul_div_assoc]
  · exact (one_le_div hdr).mpr hdH
  · exact (one_le_div hdl₁).mpr h₁
  · exact (one_le_div hdl₂).mpr h₃
  · exact (one_le_div hdr₁).mpr h₂
  · exact (one_le_div hdr₂).mpr h₄

end
end DivisorProof
