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
import SixthMoment.Arithmetic.QuadraticDivisor.Reduction.WattWeights
import SixthMoment.Arithmetic.QuadraticDivisor.Reduction.WeilAssembly
import Std



namespace DivisorProof
open Real Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000

def wattComparisonY (q : QuadraticScales) : ℝ := Real.sqrt (q.B*q.N/q.H)
def wattDivisorShape (d e f : ℝ) : ℝ := e^3*f^4/d^3

theorem one_add_product_quarter_le {t z : ℝ} (ht : 0 ≤ t) (hz : 0 ≤ z) :
    (1+t*z)^(1/4:ℝ) ≤ max 1 (t^(1/4:ℝ))*(1+z)^(1/4:ℝ) := by
  by_cases ht1 : t ≤ 1
  · have hp := Real.rpow_le_rpow ht ht1 (by norm_num : (0:ℝ) ≤ 1/4)
    rw [Real.one_rpow] at hp
    rw [max_eq_left hp,one_mul]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    nlinarith
  · have ht1' : 1 ≤ t := le_of_not_ge ht1
    have hp := Real.one_le_rpow ht1' (by norm_num : (0:ℝ) ≤ 1/4)
    rw [max_eq_right hp,← Real.mul_rpow ht (by positivity : 0 ≤ 1+z)]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    nlinarith

theorem watt_divisor_absorption {d e e' f M Z : ℝ}
    (hd : 1 ≤ d) (he : 1 ≤ e) (he' : 0 < e') (hf : 1 ≤ f)
    (heprod : e*e' = d) (hed : e ≤ d) (hfd : f ≤ d)
    (hM : 0 ≤ M) (hZ : 0 ≤ Z) :
    ((1/e)*(M/e'+Z/f))*max 1 ((wattDivisorShape d e f)^(1/4:ℝ)) ≤ M+Z := by
  have hdp : 0 < d := by linarith
  have hep : 0 < e := by linarith
  have hfp : 0 < f := by linarith
  have ht : 0 < wattDivisorShape d e f := by unfold wattDivisorShape; positivity
  have he₀ := Real.log_nonneg he
  have hd₀ := Real.log_nonneg hd
  have he₁ := Real.log_le_log hep hed
  have hf₁ := Real.log_le_log hfp hfd
  have htd : (wattDivisorShape d e f)^(1/4:ℝ) ≤ d := by
    apply (Real.log_le_log_iff (Real.rpow_pos_of_pos ht _) hdp).mp
    simp (disch := positivity) only [wattDivisorShape,Real.log_rpow,Real.log_div,
      Real.log_mul,Real.log_pow]
    linarith
  have htef : (wattDivisorShape d e f)^(1/4:ℝ) ≤ e*f := by
    apply (Real.log_le_log_iff (Real.rpow_pos_of_pos ht _) (mul_pos hep hfp)).mp
    simp (disch := positivity) only [wattDivisorShape,Real.log_rpow,Real.log_div,
      Real.log_mul,Real.log_pow]
    linarith
  let F := max 1 ((wattDivisorShape d e f)^(1/4:ℝ))
  have hFd : F ≤ d := max_le hd htd
  have hFef : F ≤ e*f := max_le (one_le_mul_of_one_le_of_one_le he hf) htef
  calc _ = M*(F/d)+Z*(F/(e*f)) := by
        dsimp only [F]
        rw [← heprod]
        field_simp
    _ ≤ M*1+Z*1 := add_le_add
      (mul_le_mul_of_nonneg_left ((div_le_one hdp).mpr hFd) hM)
      (mul_le_mul_of_nonneg_left ((div_le_one (mul_pos hep hfp)).mpr hFef) hZ)
    _ = _ := by ring

theorem WattScales.X_sq_of_pos {p : WattScales}
    (hprod : 0 < p.product) (hH : 0 < p.H) (hC : 0 < p.C) :
    p.X^2 = p.product/(p.H*p.C) :=
  Real.sq_sqrt (div_pos hprod (mul_pos hH hC)).le

theorem naturalWatt_positive {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) {d d₁ d₂ d₃ d₄ : ℝ}
    (hd : 0 < d) (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : 0 < d₃) (h₄ : 0 < d₄) :
    let p := naturalWattScales q ρ d d₁ d₂ d₃ d₄
    0 < p.H ∧ 0 < p.C ∧ 0 < p.R ∧ 0 < p.S ∧ 0 < p.V ∧ 0 < p.P ∧ 0 < p.product := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hL := poissonLength_pos q h.scales ρ hd
  dsimp [naturalWattScales,WattScales.product]
  exact ⟨by positivity,hL,by positivity,by positivity,by positivity,by positivity,by positivity⟩

theorem naturalWatt_last_ratio {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) {d d₁ d₂ d₃ d₄ : ℝ}
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : 0 < d₃) (h₄ : 0 < d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) :
    let p := naturalWattScales q ρ d d₁ d₂ d₃ d₄
    p.H^2*p.C*p.P*p.X^2/(p.R^4*p.S^3*p.V) = wattDivisorShape d d₁ d₃*wattShape q := by
  have hd : 0 < d := h₁₂ ▸ mul_pos h₁ h₂
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  obtain ⟨hpH,hpC,hpR,hpS,hpV,hpP,hprod⟩ := naturalWatt_positive h hd h₁ h₂ h₃ h₄
  dsimp only
  rw [WattScales.X_sq_of_pos hprod hpH hpC]
  dsimp [naturalWattScales,WattScales.product,wattDivisorShape,wattShape]
  have hL := poissonLength_pos q h.scales ρ hd
  have heq₂ : d₂ = d/d₁ := (eq_div_iff h₁.ne').mpr (by nlinarith)
  have heq₄ : d₄ = d/d₃ := (eq_div_iff h₃.ne').mpr (by nlinarith)
  rw [heq₂,heq₄]
  field_simp

theorem naturalWatt_first_bracket_ratio {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 ≤ ρ)
    {d d₁ d₂ d₃ d₄ : ℝ} (hd : 1 ≤ d)
    (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂) (h₃ : 1 ≤ d₃) (h₄ : 1 ≤ d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) :
    let p := naturalWattScales q ρ d d₁ d₂ d₃ d₄
    p.H*p.C/(p.R*p.S) ≤ K*q.mass^(12*ρ) := by
  have hdp : 0 < d := by linarith
  have hep : 0 < d₁ := by linarith
  have hfp : 0 < d₃ := by linarith
  have hed : d₁ ≤ d := by nlinarith
  have hfd : d₃ ≤ d := by nlinarith
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  obtain ⟨hlog,hM,hN,hshift,_,_⟩ := h.log_bounds hK
  have he := Real.log_le_log hep hed
  have hf := Real.log_le_log hfp hfd
  have hAB := Real.log_le_log (mul_pos hA hB) (product_AB_le_mass q h.scales).2
  rw [Real.log_mul hA.ne' hB.ne'] at hAB
  have hABρ := mul_le_mul_of_nonneg_left hAB hρ
  have hsqrt : 0 < Real.sqrt q.mass := Real.sqrt_pos.mpr hQ
  have hLp := poissonLength_pos q h.scales ρ hdp
  dsimp only
  apply (Real.log_le_log_iff (by dsimp [naturalWattScales]; positivity) (by positivity)).mp
  simp (disch := positivity) only [naturalWattScales,poissonLength,Real.log_mul,
    Real.log_div,Real.log_rpow,Real.log_sqrt hQ.le]
  linarith

theorem naturalWatt_second_bracket_ratio {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) {d d₁ d₂ d₃ d₄ : ℝ}
    (_h₁ : 0 < d₁) (_h₂ : 0 < d₂) (_h₃ : 0 < d₃) (h₄ : 0 < d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) (h₃B : d₃ ≤ 2*q.B) :
    let p := naturalWattScales q ρ d d₁ d₂ d₃ d₄
    p.P/(p.R*p.V) ≤ 2 := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have heq : d₁*d₂ = d₃*d₄ := h₁₂.trans h₃₄.symm
  have hid : (q.N₁/d₄)/((q.A/d₁)*(q.M₁/d₂)) = d₃*q.N₁/(q.A*q.M₁) := by
    field_simp
    nlinarith
  dsimp only [naturalWattScales]
  rw [hid]
  apply (div_le_iff₀ (mul_pos hA hM₁)).mpr
  have he := mul_le_mul_of_nonneg_right h₃B hN₁.le
  nlinarith [h.orientation]

theorem naturalWatt_X_le_comparison {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 ≤ ρ)
    {d d₁ d₂ d₃ d₄ : ℝ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : 0 < d₃) (h₄ : 0 < d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) :
    (naturalWattScales q ρ d d₁ d₂ d₃ d₄).X ≤ K*wattComparisonY q := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hN : 0 < q.N := by unfold QuadraticScales.N; positivity
  have hE : 1 ≤ q.mass^(10*ρ) := Real.one_le_rpow (poisson_scale_bounds q h.scales).1 (by positivity)
  have hY : 0 ≤ wattComparisonY q := Real.sqrt_nonneg _
  have hYsq : wattComparisonY q^2 = q.B*q.N/q.H := Real.sq_sqrt (by positivity)
  have hQbound : Real.sqrt q.mass ≤ K*(q.B*q.N) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hQ.le]
    have hm : q.mass = (q.A*q.M)*(q.B*q.N) := mass_eq_balanced_product q
    rw [hm]
    have ht := mul_le_mul_of_nonneg_right h.balanceM (mul_pos hB hN).le
    nlinarith [sq_nonneg (q.B*q.N)]
  have hs := naturalWatt_X_sq q h.scales ρ h₁ h₂ h₃ h₄ h₁₂ h₃₄
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  change (naturalWattScales q ρ d d₁ d₂ d₃ d₄).X^2 ≤ (K*wattComparisonY q)^2
  rw [hs,mul_pow,hYsq]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity : 0 < q.H*q.mass^(10*ρ)) hH).mpr
  have hk : K ≤ K^2 := by nlinarith
  have hkBN := mul_le_mul_of_nonneg_right hk (mul_pos hB hN).le
  calc _ ≤ (K^2*(q.B*q.N))*q.H := mul_le_mul_of_nonneg_right (hQbound.trans hkBN) hH.le
    _ ≤ ((K^2*(q.B*q.N))*q.H)*q.mass^(10*ρ) :=
      le_mul_of_one_le_right (by positivity) hE
    _ = _ := by ring

theorem wattComparisonY_pos {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) : 0 < wattComparisonY q := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  unfold wattComparisonY QuadraticScales.N
  exact Real.sqrt_pos.mpr (by positivity)

theorem first_inner_scale_le_watt_comparison {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 ≤ ρ) (hρhalf : ρ ≤ 1/2) :
    q.M₁ ≤ K*q.mass^ρ*q.B*wattComparisonY q := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hKp : 0 < K := by linarith
  have hY := wattComparisonY_pos h
  obtain ⟨_,hM,_,hshift,hbalance,_⟩ := h.log_bounds hK
  obtain ⟨ha,hb,hq,_⟩ := h.log_nonneg hK
  have hcoarse : Real.log q.H ≤ Real.log K+Real.log q.A+Real.log q.B := by
    have hc : (1/2+ρ)*(Real.log q.A+Real.log q.B) ≤ Real.log q.A+Real.log q.B :=
      mul_le_of_le_one_left (by linarith) (by linarith)
    linarith
  have hρq := mul_nonneg hρ hq
  apply (Real.log_le_log_iff hM₁ (by positivity)).mp
  simp (disch := positivity) only [wattComparisonY,QuadraticScales.N,Real.log_mul,
    Real.log_div,Real.log_sqrt,Real.log_rpow]
  linarith

def WattScales.totalProduct (p : WattScales) : ℝ := p.H*p.C*p.product

theorem WattScales.doubled_totalProduct (p : WattScales) :
    p.doubled.totalProduct = 64*p.totalProduct := by
  rw [WattScales.totalProduct,p.doubled_product]
  dsimp [WattScales.doubled,WattScales.totalProduct]
  ring

theorem naturalWatt_totalProduct_bound {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1/100)
    {d d₁ d₂ d₃ d₄ : ℝ} (hd : 1 ≤ d)
    (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂) (h₃ : 1 ≤ d₃) (h₄ : 1 ≤ d₄) :
    (naturalWattScales q ρ d d₁ d₂ d₃ d₄).totalProduct ≤ K*q.mass^3 := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hKp : 0 < K := by linarith
  have hd₀ := Real.log_nonneg hd
  have h₁₀ := Real.log_nonneg h₁
  have h₂₀ := Real.log_nonneg h₂
  have h₃₀ := Real.log_nonneg h₃
  have h₄₀ := Real.log_nonneg h₄
  have hM₂₀ := Real.log_nonneg (h.scales 3)
  have hN₂₀ := Real.log_nonneg (h.scales 5)
  change 0 ≤ Real.log q.M₂ at hM₂₀
  change 0 ≤ Real.log q.N₂ at hN₂₀
  have hQ₀ := Real.log_nonneg (poisson_scale_bounds q h.scales).1
  obtain ⟨hlog,_,_,hshift,_,_⟩ := h.log_bounds hK
  have hAB := Real.log_le_log (mul_pos hA hB) (product_AB_le_mass q h.scales).2
  rw [Real.log_mul hA.ne' hB.ne'] at hAB
  have hAB' := mul_le_mul_of_nonneg_left hAB (show 0 ≤ 1/2+ρ by linarith)
  have hrest := mul_nonneg (show 0 ≤ 1-11*ρ by linarith) hQ₀
  have hdp : 0 < d := by linarith
  have hLp := poissonLength_pos q h.scales ρ hdp
  apply (Real.log_le_log_iff (by
    dsimp [WattScales.totalProduct,WattScales.product,naturalWattScales]; positivity) (by positivity)).mp
  simp (disch := positivity) only [WattScales.totalProduct,WattScales.product,
    naturalWattScales,poissonLength,Real.log_mul,Real.log_div,Real.log_sqrt,
    Real.log_rpow,Real.log_pow]
  linarith

theorem WattScales.doubled_first_ratio (p : WattScales) :
    p.doubled.H*p.doubled.C/(p.doubled.R*p.doubled.S) = p.H*p.C/(p.R*p.S) := by
  dsimp [WattScales.doubled]
  ring

theorem WattScales.doubled_second_ratio (p : WattScales) :
    p.doubled.P/(p.doubled.R*p.doubled.V) = (p.P/(p.R*p.V))/2 := by
  dsimp [WattScales.doubled]
  ring

theorem WattScales.doubled_last_ratio (p : WattScales) :
    p.doubled.H^2*p.doubled.C*p.doubled.P*p.doubled.X^2/
      (p.doubled.R^4*p.doubled.S^3*p.doubled.V) =
        (p.H^2*p.C*p.P*p.X^2/(p.R^4*p.S^3*p.V))/4 := by
  rw [p.doubled_X]
  dsimp [WattScales.doubled]
  ring

end
end DivisorProof




namespace DivisorProof
open Real Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000

def concreteWattScales (q : QuadraticScales) (ρ : ℝ) (d e f : ℕ) : WattScales :=
  (naturalWattScales q ρ d e (d/e:ℕ) f (d/f:ℕ)).doubled

def actualWattSum (positive frequencyPositive : Bool) (q : QuadraticScales)
    (ρ : ℝ) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (d e f : ℕ) (x : ℝ) : ℂ :=
  weightedWattSum (positive != frequencyPositive) (concreteWattScales q ρ d e f)
    (actualWattCoefficient α e (d/e)) (actualWattCoefficient β f (d/f))
    (wattShiftWeight q W d) (wattFrequencyWeight q ρ d x frequencyPositive)
    (actualWattGamma q W e (d/e) f (d/f) x)

theorem wattIndexSet_eq_empty_of_small {p : WattScales} {i : Fin 6} (hi : p.size i < 1) :
    wattIndexSet p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  have hmi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hm i)
  have hfloor : ⌊p.size i⌋₊ = 0 := Nat.floor_eq_zero.mpr hi
  omega

theorem wattMajorant_nonneg {p : WattScales} {Δ η : ℝ} (hΔ : 0 ≤ Δ)
    (hH : 0 ≤ p.H) (hC : 0 ≤ p.C) (hR : 0 ≤ p.R) (hS : 0 ≤ p.S)
    (hV : 0 ≤ p.V) (hP : 0 ≤ p.P) : 0 ≤ wattMajorant p Δ η := by
  have hX : 0 ≤ p.X := Real.sqrt_nonneg _
  unfold wattMajorant
  positivity

theorem WeightedWattBound.actual_fibre_bound (hWatt : WeightedWattBound)
    {ρ δ K : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hbound : ρ ≤ δ/(1000*(1+δ))) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ Q₀ C : ℝ, 1 ≤ Q₀ ∧ 0 ≤ C ∧
      ∀ (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
        ScaleGeometry ρ K q → (q.A*q.B)^δ ≤ K*q.M*q.N →
        NormalizedWeightData bounds q α β W → Q₀ ≤ q.mass →
        ∀ d ∈ smallGcdSet q ρ, ∀ e ∈ d.divisors, ∀ f ∈ d.divisors,
          ∀ x ∈ Icc (poissonRadius q d/4) (2*poissonRadius q d),
            ∀ positive frequencyPositive : Bool,
              ‖actualWattSum positive frequencyPositive q ρ α β W d e f x‖ ≤
                C*wattMajorant (concreteWattScales q ρ d e f) (q.mass^(-10*ρ)) ρ := by
  obtain ⟨b,hb',hdata⟩ := actualWatt_weight_data hρ hK bounds hb
  have hg : ∀ i j, 0 ≤ actualWattGammaBounds bounds K i j :=
    actualWattGammaBounds_nonneg hb (by linarith : 0 ≤ K)
  obtain ⟨Q₀,C,hQ₀,hC,happly⟩ := weightedWatt_at_doubled_natural_scales
    hWatt hρ hδ hbound hK b hb' (actualWattGammaBounds bounds K) hg
  refine ⟨Q₀,C,hQ₀,hC,?_⟩
  intro q α β W h hsize hw hmass d hd e he f hf x hx positive frequencyPositive
  have hadm := hw.admissible h hρ.le hK hsize
  have hdp : 0 < d := (Finset.mem_Icc.mp (mem_filter.mp hd).1).1
  have hep := Nat.pos_of_mem_divisors he
  have hfp := Nat.pos_of_mem_divisors hf
  have hediv := (Nat.mem_divisors.mp he).1
  have hfdiv := (Nat.mem_divisors.mp hf).1
  have he₂p := Nat.div_pos (Nat.le_of_dvd hdp hediv) hep
  have hf₄p := Nat.div_pos (Nat.le_of_dvd hdp hfdiv) hfp
  have heprod := Nat.mul_div_cancel' hediv
  have hfprod := Nat.mul_div_cancel' hfdiv
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hdp
  have he' : (1:ℝ) ≤ e := by exact_mod_cast hep
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hfp
  have he₂' : (1:ℝ) ≤ (d/e:ℕ) := by exact_mod_cast he₂p
  have hf₄' : (1:ℝ) ≤ (d/f:ℕ) := by exact_mod_cast hf₄p
  have heprod' : (e:ℝ)*(d/e:ℕ) = d := by exact_mod_cast heprod
  have hfprod' : (f:ℝ)*(d/f:ℕ) = d := by exact_mod_cast hfprod
  let p := concreteWattScales q ρ d e f
  have hQ := (poisson_scale_bounds q h.scales).1
  have hQp : 0 < q.mass := by linarith
  have hΔ : 0 < q.mass^(-10*ρ) := Real.rpow_pos_of_pos hQp _
  by_cases hscales : ∀ i, 1 ≤ p.size i
  · have hfB : (f:ℝ) ≤ 2*q.B := by
      have hs := hscales 3
      change 1 ≤ 2*(q.B/(f:ℝ)) at hs
      have hfr : (0:ℝ) < f := by exact_mod_cast hfp
      rw [← mul_div_assoc] at hs
      simpa only [one_mul] using (le_div_iff₀ hfr).mp hs
    have hΔ₁ : q.mass^(-10*ρ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQ (by nlinarith)
    exact happly bounds q α β W hadm hmass d e (d/e:ℕ) f (d/f:ℕ)
      hd' he' he₂' hf' hf₄' heprod' hfprod' hfB (mem_filter.mp hd).2
      _ _ _ _ _ _ hscales hΔ hΔ₁
      (hdata q α β W h hw d e (d/e) f (d/f) hep he₂p hfp hf₄p
        heprod hfprod hscales x hx frequencyPositive) (positive != frequencyPositive)
  · push Not at hscales
    obtain ⟨i,hi⟩ := hscales
    have hempty := wattIndexSet_eq_empty_of_small hi
    have hz : actualWattSum positive frequencyPositive q ρ α β W d e f x = 0 := by
      unfold actualWattSum weightedWattSum
      rw [hempty]
      simp only [filter_empty,sum_empty]
    rw [hz,norm_zero]
    apply mul_nonneg hC
    obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,_⟩ := h.pos
    have hL := poissonLength_pos q h.scales ρ (by exact_mod_cast hdp : (0:ℝ) < d)
    apply wattMajorant_nonneg hΔ.le
    all_goals dsimp [concreteWattScales,WattScales.doubled,naturalWattScales]; positivity

end
end DivisorProof




namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000

def frequencyPair (l : ℤ) : Bool × ℕ := (decide (0 ≤ l),l.natAbs)

theorem signedShift_frequencyPair (l : ℤ) :
    signedShift (frequencyPair l).1 (frequencyPair l).2 = l := by
  by_cases hl : 0 ≤ l
  · simpa only [frequencyPair,decide_eq_true hl,signedShift,ite_true]
      using Int.natAbs_of_nonneg hl
  · have hln := le_of_lt (lt_of_not_ge hl)
    simp only [frequencyPair,decide_eq_false hl,signedShift,Bool.false_eq_true,ite_false]
    exact (Int.eq_neg_natAbs_of_nonpos hln).symm

theorem frequencyPair_signedShift (b : Bool) {n : ℕ} (hn : 0 < n) :
    frequencyPair (signedShift b n) = (b,n) := by
  cases b <;> simp [frequencyPair,signedShift,hn.ne']

theorem signed_frequency_sum_eq {E : Type*} [AddCommMonoid E]
    {L : ℝ} (hL : 0 ≤ L) (F : ℤ → E) :
    (∑ l ∈ frequencySet L, if l = 0 then 0 else F l) =
      ∑ b : Bool, ∑ n ∈ Finset.Icc 1 ⌊L⌋₊, F (signedShift b n) := by
  rw [← Finset.sum_product']
  apply Finset.sum_bij_ne_zero (fun l _ _ => frequencyPair l)
  · intro l hl hne
    have hl0 : l ≠ 0 := by intro hh; exact hne (by simp [hh])
    refine mem_product.mpr ⟨mem_univ _,Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hl0,?_⟩⟩
    apply (Nat.le_floor_iff hL).mpr
    simpa only [frequencyPair,Nat.cast_natAbs,Int.cast_abs] using (mem_frequencySet L l).mp hl
  · intro l _ _ k _ _ hpair
    have heq := congrArg (fun p : Bool × ℕ => signedShift p.1 p.2) hpair
    simpa only [signedShift_frequencyPair] using heq
  · intro p hp hne
    have hn := (Finset.mem_Icc.mp (mem_product.mp hp).2).1
    have hbound : (p.2:ℝ) ≤ L :=
      (show (p.2:ℝ) ≤ (⌊L⌋₊:ℝ) by exact_mod_cast (Finset.mem_Icc.mp (mem_product.mp hp).2).2).trans
        (Nat.floor_le hL)
    have hl0 : signedShift p.1 p.2 ≠ 0 := by
      intro hz
      have hh := congrArg Int.natAbs hz
      rw [signedShift_natAbs] at hh
      simp only [Int.natAbs_zero] at hh
      omega
    have hl : signedShift p.1 p.2 ∈ frequencySet L := by
      apply (mem_frequencySet L _).mpr
      have he : |(signedShift p.1 p.2:ℝ)| = (p.2:ℝ) := by cases p.1 <;> simp [signedShift]
      rwa [he]
    refine ⟨signedShift p.1 p.2,hl,?_,?_⟩
    · simpa only [ite_eq_right hl0] using hne
    · exact frequencyPair_signedShift p.1 hn
  · intro l _ hne
    have hl0 : l ≠ 0 := by intro hh; exact hne (by simp [hh])
    rw [ite_eq_right hl0,signedShift_frequencyPair]

def originalPositiveWattBlock (positive frequencyPositive : Bool) (q : QuadraticScales)
    (ρ : ℝ) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (d : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ (quadraticMainIndexSet q).filter (fun n => outerGCD n = d),
    ∑ l ∈ Finset.Icc 1 ⌊2*poissonLength q ρ d⌋₊,
      originalWattTerm positive frequencyPositive q ρ α β W d x n l

theorem sourceCutoff_signed_frequency (b : Bool) (n : ℕ) (L : ℝ) :
    sourceCutoff ((signedShift b n:ℝ)/L) = sourceCutoff ((n:ℝ)/L) := by
  cases b <;> simp [signedShift,neg_div,sourceCutoff_even]

theorem gcdBlockIntegrand_eq_signed_blocks {q : QuadraticScales}
    (hq : ∀ j, 1 ≤ q.size j) (positive : Bool) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) {d : ℕ} (hd : 0 < d) (x : ℝ) :
    gcdBlockIntegrand positive q ρ α β W d x =
      ∑ frequencyPositive : Bool, originalPositiveWattBlock positive frequencyPositive q ρ α β W d x := by
  have hL := poissonLength_pos q hq ρ (by exact_mod_cast hd : (0:ℝ) < d)
  rw [gcdBlockIntegrand_eq_frequency_sum,signed_frequency_sum_eq (by positivity : 0 ≤ 2*poissonLength q ρ d)]
  apply sum_congr rfl
  intro frequencyPositive _
  unfold fixedGcdFourierSum originalPositiveWattBlock
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro l _
  rw [sourceCutoff_signed_frequency]
  unfold originalWattTerm
  ring

theorem originalPositiveWattBlock_eq_fibres (positive frequencyPositive : Bool)
    (q : QuadraticScales) (ρ : ℝ) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ)
    {d : ℕ} (hd : 0 < d) (x : ℝ) :
    originalPositiveWattBlock positive frequencyPositive q ρ α β W d x =
      ∑ e ∈ d.divisors, ∑ f ∈ d.divisors, ∑ p ∈ originalWattFibre q ρ d e f,
        originalWattTerm positive frequencyPositive q ρ α β W d x p.1 p.2 := by
  unfold originalWattFibre
  simp_rw [Finset.sum_filter]
  symm
  have heq : (∑ e ∈ d.divisors, ∑ f ∈ d.divisors,
      ∑ p ∈ quadraticMainIndexSet q ×ˢ Finset.Icc 1 ⌊2*poissonLength q ρ d⌋₊,
        if outerGCD p.1 = d ∧ splitLeft (p.1 0) d = e ∧ splitLeft (p.1 1) d = f then
          originalWattTerm positive frequencyPositive q ρ α β W d x p.1 p.2 else 0) =
      ∑ p ∈ quadraticMainIndexSet q ×ˢ Finset.Icc 1 ⌊2*poissonLength q ρ d⌋₊,
        ∑ e ∈ d.divisors, ∑ f ∈ d.divisors,
          if outerGCD p.1 = d ∧ splitLeft (p.1 0) d = e ∧ splitLeft (p.1 1) d = f then
            originalWattTerm positive frequencyPositive q ρ α β W d x p.1 p.2 else 0 := by
    calc _ = ∑ e ∈ d.divisors,
          ∑ p ∈ quadraticMainIndexSet q ×ˢ Finset.Icc 1 ⌊2*poissonLength q ρ d⌋₊,
            ∑ f ∈ d.divisors,
              if outerGCD p.1 = d ∧ splitLeft (p.1 0) d = e ∧ splitLeft (p.1 1) d = f then
                originalWattTerm positive frequencyPositive q ρ α β W d x p.1 p.2 else 0 := by
          apply sum_congr rfl; intro e _; rw [sum_comm]
      _ = _ := by rw [sum_comm]
  rw [heq]
  have hsource : originalPositiveWattBlock positive frequencyPositive q ρ α β W d x =
      ∑ p ∈ quadraticMainIndexSet q ×ˢ Finset.Icc 1 ⌊2*poissonLength q ρ d⌋₊,
        if outerGCD p.1 = d then originalWattTerm positive frequencyPositive q ρ α β W d x p.1 p.2 else 0 := by
    unfold originalPositiveWattBlock
    rw [Finset.sum_filter,Finset.sum_product]
    apply sum_congr rfl; intro n _
    by_cases hg : outerGCD n = d <;> simp [hg]
  rw [hsource]
  apply sum_congr rfl
  intro p _
  have he : splitLeft (p.1 0) d ∈ d.divisors := Nat.mem_divisors.mpr ⟨splitLeft_dvd _ _,hd.ne'⟩
  have hf : splitLeft (p.1 1) d ∈ d.divisors := Nat.mem_divisors.mpr ⟨splitLeft_dvd _ _,hd.ne'⟩
  by_cases hg : outerGCD p.1 = d
  · simp only [hg,true_and,ite_true]
    have hinner (e : ℕ) : (∑ f ∈ d.divisors,
        if splitLeft (p.1 0) d = e ∧ splitLeft (p.1 1) d = f then
          originalWattTerm positive frequencyPositive q ρ α β W d x p.1 p.2 else 0) =
        if splitLeft (p.1 0) d = e then originalWattTerm positive frequencyPositive q ρ α β W d x p.1 p.2 else 0 := by
      by_cases hee : splitLeft (p.1 0) d = e <;> simp [hee,hf]
    simp_rw [hinner]
    simp [he]
  · simp [hg]

theorem gcdBlockIntegrand_eq_actualWattSums {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hq : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (positive : Bool) (ρ : ℝ) {d : ℕ} (hd : 0 < d) (x : ℝ) :
    gcdBlockIntegrand positive q ρ α β W d x =
      ∑ frequencyPositive : Bool, ∑ e ∈ d.divisors, ∑ f ∈ d.divisors,
        actualWattSum positive frequencyPositive q ρ α β W d e f x := by
  rw [gcdBlockIntegrand_eq_signed_blocks hq positive ρ α β W hd x]
  apply sum_congr rfl
  intro frequencyPositive _
  rw [originalPositiveWattBlock_eq_fibres positive frequencyPositive q ρ α β W hd x]
  apply sum_congr rfl; intro e he
  apply sum_congr rfl; intro f hf
  exact originalWattFibre_sum_eq hq hw positive frequencyPositive ρ hd he hf x

end
end DivisorProof




namespace DivisorProof
open Real Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000

theorem watt_prefactor_absorbed {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 ≤ ρ) (hρhalf : ρ ≤ 1/2)
    {d d₁ d₂ d₃ d₄ : ℝ} (hd : 1 ≤ d)
    (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂) (h₃ : 1 ≤ d₃) (h₄ : 1 ≤ d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) :
    let p := naturalWattScales q ρ d d₁ d₂ d₃ d₄
    p.doubled.H*p.doubled.C*p.doubled.R*(p.doubled.V+p.doubled.S*p.doubled.X)*
      max 1 ((wattDivisorShape d d₁ d₃)^(1/4:ℝ)) ≤
        (32*K*(K+1))*q.mass^ρ*q.A*q.B*q.H*poissonLength q ρ d*wattComparisonY q/d := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hdp : 0 < d := by linarith
  have h₁p : 0 < d₁ := by linarith
  have h₂p : 0 < d₂ := by linarith
  have h₃p : 0 < d₃ := by linarith
  have h₄p : 0 < d₄ := by linarith
  have hLp := poissonLength_pos q h.scales ρ hdp
  have hY := wattComparisonY_pos h
  let p := naturalWattScales q ρ d d₁ d₂ d₃ d₄
  have hX : p.X ≤ K*wattComparisonY q := naturalWatt_X_le_comparison h hK hρ
    h₁p h₂p h₃p h₄p h₁₂ h₃₄
  have hVX : p.doubled.V+p.doubled.S*p.doubled.X ≤
      4*K*(q.M₁/d₂+q.B*wattComparisonY q/d₃) := by
    rw [p.doubled_X]
    change 2*(q.M₁/d₂)+(2*(q.B/d₃))*(2*p.X) ≤ _
    have hx := mul_le_mul_of_nonneg_left hX (by positivity : 0 ≤ 4*q.B/d₃)
    have hm := mul_le_mul_of_nonneg_right (show 2 ≤ 4*K by linarith) (div_pos hM₁ h₂p).le
    convert add_le_add hm hx using 1 <;> ring
  have habs := watt_divisor_absorption hd h₁ h₂p h₃ h₁₂
    (by nlinarith : d₁ ≤ d) (by nlinarith : d₃ ≤ d) hM₁.le (mul_pos hB hY).le
  have hMbound := first_inner_scale_le_watt_comparison h hK hρ hρhalf
  have hE := Real.one_le_rpow (poisson_scale_bounds q h.scales).1 hρ
  have hMsum : q.M₁+q.B*wattComparisonY q ≤ (K+1)*q.mass^ρ*q.B*wattComparisonY q := by
    have he := mul_le_mul_of_nonneg_right hE (mul_pos hB hY).le
    nlinarith
  let F := max 1 ((wattDivisorShape d d₁ d₃)^(1/4:ℝ))
  have hF : 0 ≤ F := le_trans (by norm_num) (le_max_left _ _)
  calc _ ≤ (p.doubled.H*p.doubled.C*p.doubled.R)*
        (4*K*(q.M₁/d₂+q.B*wattComparisonY q/d₃))*F := by
        apply mul_le_mul_of_nonneg_right _ hF
        apply mul_le_mul_of_nonneg_left hVX
        change 0 ≤ (2*(q.H/d))*(2*poissonLength q ρ d)*(2*(q.A/d₁))
        positivity
    _ = (32*K*q.H*poissonLength q ρ d*q.A/d)*
        (((1/d₁)*(q.M₁/d₂+q.B*wattComparisonY q/d₃))*F) := by
        dsimp only [p,naturalWattScales,WattScales.doubled]
        ring
    _ ≤ (32*K*q.H*poissonLength q ρ d*q.A/d)*(q.M₁+q.B*wattComparisonY q) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ (32*K*q.H*poissonLength q ρ d*q.A/d)*
        ((K+1)*q.mass^ρ*q.B*wattComparisonY q) := mul_le_mul_of_nonneg_left hMsum (by positivity)
    _ = _ := by ring

theorem watt_first_bracket_bound {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 ≤ ρ)
    {d d₁ d₂ d₃ d₄ : ℝ} (hd : 1 ≤ d)
    (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂) (h₃ : 1 ≤ d₃) (h₄ : 1 ≤ d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) :
    let p := (naturalWattScales q ρ d d₁ d₂ d₃ d₄).doubled
    (1+p.H*p.C/(p.R*p.S))^(1/2:ℝ) ≤ (1+K)^(1/2:ℝ)*q.mass^(6*ρ) := by
  have hratio := naturalWatt_first_bracket_ratio h hK hρ hd h₁ h₂ h₃ h₄ h₁₂ h₃₄
  have hQp := h.pos.2.2.2.2.2.2.2
  have hE := Real.one_le_rpow (poisson_scale_bounds q h.scales).1 (by positivity : 0 ≤ 12*ρ)
  obtain ⟨hpH,hpC,hpR,hpS,hpV,hpP,hprod⟩ := naturalWatt_positive h (by linarith : 0 < d) (by linarith : 0 < d₁)
    (by linarith : 0 < d₂) (by linarith : 0 < d₃) (by linarith : 0 < d₄)
  dsimp only
  rw [WattScales.doubled_first_ratio]
  calc _ ≤ ((1+K)*q.mass^(12*ρ))^(1/2:ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow (by linarith : 0 ≤ 1+K) (Real.rpow_nonneg hQp.le _),
        ← Real.rpow_mul hQp.le]
      congr 2
      ring

theorem watt_second_bracket_bound {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) {d d₁ d₂ d₃ d₄ : ℝ}
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : 0 < d₃) (h₄ : 0 < d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) (h₃B : d₃ ≤ 2*q.B) :
    let p := (naturalWattScales q ρ d d₁ d₂ d₃ d₄).doubled
    (1+p.P/(p.R*p.V))^(1/2:ℝ) ≤ 2 := by
  have hratio := naturalWatt_second_bracket_ratio h h₁ h₂ h₃ h₄ h₁₂ h₃₄ h₃B
  obtain ⟨hpH,hpC,hpR,hpS,hpV,hpP,hprod⟩ := naturalWatt_positive h (h₁₂ ▸ mul_pos h₁ h₂) h₁ h₂ h₃ h₄
  dsimp only
  rw [WattScales.doubled_second_ratio]
  calc _ ≤ (4:ℝ)^(1/2:ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    _ = _ := by norm_num [← Real.sqrt_eq_rpow]

theorem watt_last_bracket_bound {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) {d d₁ d₂ d₃ d₄ : ℝ}
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : 0 < d₃) (h₄ : 0 < d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) :
    let p := (naturalWattScales q ρ d d₁ d₂ d₃ d₄).doubled
    (1+p.H^2*p.C*p.P*p.X^2/(p.R^4*p.S^3*p.V))^(1/4:ℝ) ≤
      max 1 ((wattDivisorShape d d₁ d₃)^(1/4:ℝ))*(1+wattShape q)^(1/4:ℝ) := by
  have hd : 0 < d := h₁₂ ▸ mul_pos h₁ h₂
  have ht : 0 ≤ wattDivisorShape d d₁ d₃ := by unfold wattDivisorShape; positivity
  have hz : 0 ≤ wattShape q := by
    obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
    unfold wattShape
    positivity
  dsimp only
  rw [WattScales.doubled_last_ratio,naturalWatt_last_ratio h h₁ h₂ h₃ h₄ h₁₂ h₃₄]
  apply le_trans _ (one_add_product_quarter_le ht hz)
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  nlinarith

theorem multiply_six_bounds (a b : Fin 6 → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) :
    a 0*a 1*a 2*a 3*a 4*a 5 ≤ b 0*b 1*b 2*b 3*b 4*b 5 := by
  have hp := Finset.prod_le_prod₀ (fun i (_ : i ∈ (univ:Finset (Fin 6))) => ha i)
    (fun i (_ : i ∈ (univ:Finset (Fin 6))) => hab i)
  simpa [Fin.prod_univ_succ,mul_assoc] using hp

def wattEvaluationConstant (ρ K : ℝ) : ℝ :=
  64*K*(K+1)*(1+K)^(1/2:ℝ)*(64*K)^(20*ρ)

theorem wattEvaluationConstant_nonneg {ρ K : ℝ} (hK : 0 ≤ K) :
    0 ≤ wattEvaluationConstant ρ K := by unfold wattEvaluationConstant; positivity

theorem actual_watt_majorant_bound {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1/100)
    {d d₁ d₂ d₃ d₄ : ℝ} (hd : 1 ≤ d)
    (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂) (h₃ : 1 ≤ d₃) (h₄ : 1 ≤ d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) (h₃B : d₃ ≤ 2*q.B) :
    let p := (naturalWattScales q ρ d d₁ d₂ d₃ d₄).doubled
    wattMajorant p (q.mass^(-10*ρ)) ρ ≤
      wattEvaluationConstant ρ K*q.mass^(102*ρ)*q.A*q.B*q.H*poissonLength q ρ d*
        wattComparisonY q/d*(1+wattShape q)^(1/4:ℝ) := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hdp : 0 < d := by linarith
  have h₁p : 0 < d₁ := by linarith
  have h₂p : 0 < d₂ := by linarith
  have h₃p : 0 < d₃ := by linarith
  have h₄p : 0 < d₄ := by linarith
  have hLp := poissonLength_pos q h.scales ρ hdp
  obtain ⟨hpH,hpC,hpR,hpS,hpV,hpP,hprod⟩ := naturalWatt_positive h hdp h₁p h₂p h₃p h₄p
  let p := naturalWattScales q ρ d d₁ d₂ d₃ d₄
  let u := p.doubled
  let F := max 1 ((wattDivisorShape d d₁ d₃)^(1/4:ℝ))
  let Z := (1+wattShape q)^(1/4:ℝ)
  let C₁ := (1+K)^(1/2:ℝ)
  let C₂₀ := (64*K)^(20*ρ)
  let P := u.H*u.C*u.R*(u.V+u.S*u.X)
  have hpre : P*F ≤ (32*K*(K+1))*q.mass^ρ*q.A*q.B*q.H*poissonLength q ρ d*wattComparisonY q/d :=
    watt_prefactor_absorbed h hK hρ (by linarith) hd h₁ h₂ h₃ h₄ h₁₂ h₃₄
  have hfirst : (1+u.H*u.C/(u.R*u.S))^(1/2:ℝ) ≤ C₁*q.mass^(6*ρ) :=
    watt_first_bracket_bound h hK hρ hd h₁ h₂ h₃ h₄ h₁₂ h₃₄
  have hsecond : (1+u.P/(u.R*u.V))^(1/2:ℝ) ≤ 2 :=
    watt_second_bracket_bound h h₁p h₂p h₃p h₄p h₁₂ h₃₄ h₃B
  have hlast : (1+u.H^2*u.C*u.P*u.X^2/(u.R^4*u.S^3*u.V))^(1/4:ℝ) ≤ F*Z :=
    watt_last_bracket_bound h h₁p h₂p h₃p h₄p h₁₂ h₃₄
  have htotal : u.totalProduct ≤ (64*K)*q.mass^3 := by
    rw [show u.totalProduct = 64*p.totalProduct from p.doubled_totalProduct]
    have ht := mul_le_mul_of_nonneg_left
      (naturalWatt_totalProduct_bound h hK hρ hρsmall hd h₁ h₂ h₃ h₄) (by norm_num : (0:ℝ) ≤ 64)
    convert ht using 1
    ring
  have hfull : u.H*u.C*u.R*u.S*u.V*u.P = u.totalProduct := by
    dsimp [WattScales.totalProduct,WattScales.product]
    ring
  have htotalpos : 0 ≤ u.totalProduct := by
    rw [show u.totalProduct = 64*p.totalProduct from p.doubled_totalProduct]
    dsimp [WattScales.totalProduct]
    positivity
  have hbudget : (u.H*u.C*u.R*u.S*u.V*u.P)^(20*ρ) ≤ C₂₀*q.mass^(60*ρ) := by
    rw [hfull]
    calc _ ≤ ((64*K)*q.mass^3)^(20*ρ) := Real.rpow_le_rpow htotalpos htotal (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (by positivity : 0 ≤ 64*K) (pow_nonneg hQ.le 3),
          ← Real.rpow_natCast q.mass 3,← Real.rpow_mul hQ.le]
        congr 2
        ring
  have hdelta : (q.mass^(-10*ρ))^(-7/2:ℝ) = q.mass^(35*ρ) := by
    rw [← Real.rpow_mul hQ.le]
    congr 1
    ring
  have hF : 0 ≤ F := le_trans (by norm_num) (le_max_left _ _)
  have hz : 0 ≤ wattShape q := by unfold wattShape; positivity
  have hUX : 0 ≤ u.X := Real.sqrt_nonneg _
  have hUH : 0 ≤ u.H := show 0 ≤ 2*p.H from mul_nonneg (by norm_num) hpH.le
  have hUC : 0 ≤ u.C := show 0 ≤ 2*p.C from mul_nonneg (by norm_num) hpC.le
  have hUR : 0 ≤ u.R := show 0 ≤ 2*p.R from mul_nonneg (by norm_num) hpR.le
  have hUS : 0 ≤ u.S := show 0 ≤ 2*p.S from mul_nonneg (by norm_num) hpS.le
  have hUV : 0 ≤ u.V := show 0 ≤ 2*p.V from mul_nonneg (by norm_num) hpV.le
  have hUP : 0 ≤ u.P := show 0 ≤ 2*p.P from mul_nonneg (by norm_num) hpP.le
  have hPnonneg : 0 ≤ P := by dsimp only [P]; positivity
  have hbound := multiply_six_bounds
    ![(q.mass^(-10*ρ))^(-7/2:ℝ),P,(1+u.H*u.C/(u.R*u.S))^(1/2:ℝ),
      (1+u.P/(u.R*u.V))^(1/2:ℝ),(1+u.H^2*u.C*u.P*u.X^2/(u.R^4*u.S^3*u.V))^(1/4:ℝ),
      (u.H*u.C*u.R*u.S*u.V*u.P)^(20*ρ)]
    ![q.mass^(35*ρ),P,C₁*q.mass^(6*ρ),2,F*Z,C₂₀*q.mass^(60*ρ)]
    (by
      intro i; fin_cases i <;> dsimp
      all_goals positivity)
    (by
      intro i; fin_cases i <;> dsimp
      · exact hdelta.le
      · exact le_rfl
      · exact hfirst
      · exact hsecond
      · exact hlast
      · exact hbudget)
  have hpartial : wattMajorant u (q.mass^(-10*ρ)) ρ ≤
      q.mass^(35*ρ)*P*(C₁*q.mass^(6*ρ))*2*(F*Z)*(C₂₀*q.mass^(60*ρ)) := by
    simpa [wattMajorant,P,mul_assoc] using hbound
  have hmerge : q.mass^(35*ρ)*q.mass^(6*ρ)*q.mass^(60*ρ) = q.mass^(101*ρ) := by
    rw [← Real.rpow_add hQ,← Real.rpow_add hQ]
    congr 1
    ring
  have hmerge' : q.mass^(101*ρ)*q.mass^ρ = q.mass^(102*ρ) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  calc _ ≤ q.mass^(35*ρ)*P*(C₁*q.mass^(6*ρ))*2*(F*Z)*(C₂₀*q.mass^(60*ρ)) := hpartial
    _ = (2*C₁*C₂₀)*(q.mass^(35*ρ)*q.mass^(6*ρ)*q.mass^(60*ρ))*(P*F)*Z := by ring
    _ = (2*C₁*C₂₀)*q.mass^(101*ρ)*(P*F)*Z := by rw [hmerge]
    _ ≤ (2*C₁*C₂₀)*q.mass^(101*ρ)*
        ((32*K*(K+1))*q.mass^ρ*q.A*q.B*q.H*poissonLength q ρ d*wattComparisonY q/d)*Z := by
        apply mul_le_mul_of_nonneg_right _ (by dsimp [Z]; positivity)
        apply mul_le_mul_of_nonneg_left hpre
        dsimp [C₁,C₂₀]
        positivity
    _ = _ := by
      calc _ = (64*K*(K+1)*C₁*C₂₀)*(q.mass^(101*ρ)*q.mass^ρ)*
          q.A*q.B*q.H*poissonLength q ρ d*wattComparisonY q/d*Z := by ring
        _ = _ := by rw [hmerge']; rfl

end
end DivisorProof




namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000

theorem rho_le_one_hundredth {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hbound : ρ ≤ δ/(1000*(1+δ))) : ρ ≤ 1/100 := by
  have ht := (le_div_iff₀ (by positivity : 0 < 1000*(1+δ))).mp hbound
  have hrδ := mul_pos hρ hδ
  by_contra hh
  have hlow : 1/100 < ρ := lt_of_not_ge hh
  nlinarith

theorem actualWattSum_zero_of_short_beta {q : QuadraticScales} {ρ : ℝ}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ} {d e f : ℕ}
    (hf : 0 < f) (hshort : 2*q.B < (f:ℝ)) (positive frequencyPositive : Bool) (x : ℝ) :
    actualWattSum positive frequencyPositive q ρ α β W d e f x = 0 := by
  have hfr : (0:ℝ) < f := by exact_mod_cast hf
  have hs : (concreteWattScales q ρ d e f).size 3 < 1 := by
    change 2*(q.B/(f:ℝ)) < 1
    rw [← mul_div_assoc]
    exact (div_lt_one hfr).mpr hshort
  unfold actualWattSum weightedWattSum
  rw [wattIndexSet_eq_empty_of_small hs]
  simp only [filter_empty,sum_empty]

theorem watt_H_mul_comparisonY {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) : q.H*wattComparisonY q = (q.B*q.N*q.H)^(1/2:ℝ) := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hN : 0 < q.N := by unfold QuadraticScales.N; positivity
  unfold wattComparisonY
  rw [← Real.sqrt_eq_rpow]
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ q.B*q.N/q.H),
    Real.sq_sqrt (by positivity : 0 ≤ q.B*q.N*q.H)]
  field_simp

theorem WeightedWattBound.actual_pointwise_watt_bound (hWatt : WeightedWattBound)
    {ρ δ K : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hbound : ρ ≤ δ/(1000*(1+δ))) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ Q₀ C : ℝ, 1 ≤ Q₀ ∧ 0 ≤ C ∧
      ∀ (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
        ScaleGeometry ρ K q → (q.A*q.B)^δ ≤ K*q.M*q.N →
        NormalizedWeightData bounds q α β W → Q₀ ≤ q.mass →
        ∀ positive : Bool, ∀ d ∈ smallGcdSet q ρ, ∀ x : ℝ,
          ‖gcdBlockIntegrand positive q ρ α β W d x‖ ≤
            C*q.mass^(104*ρ)*q.A*q.B*q.H*poissonLength q ρ d*wattComparisonY q/(d:ℝ)*
              (1+wattShape q)^(1/4:ℝ) := by
  obtain ⟨Q₀,C,hQ₀,hC,hfibre⟩ := hWatt.actual_fibre_bound hρ hδ hbound hK bounds hb
  obtain ⟨D,hD,hτ⟩ := divisor_count_sq_subpower (by positivity : 0 < 2*ρ)
  have hEval := wattEvaluationConstant_nonneg (ρ := ρ) (by linarith : 0 ≤ K)
  refine ⟨Q₀,2*C*wattEvaluationConstant ρ K*D,hQ₀,by positivity,?_⟩
  intro q α β W h hsize hw hmass positive d hd x
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hdp : 0 < d := (Finset.mem_Icc.mp (mem_filter.mp hd).1).1
  have hdr : (0:ℝ) < d := by exact_mod_cast hdp
  have hLp := poissonLength_pos q h.scales ρ hdr
  have hY := wattComparisonY_pos h
  have hQ₁ := (poisson_scale_bounds q h.scales).1
  have hz : 0 ≤ wattShape q := by unfold wattShape; positivity
  by_cases hx : x ∈ Icc (poissonRadius q d/4) (2*poissonRadius q d)
  · let B := C*wattEvaluationConstant ρ K*q.mass^(102*ρ)*q.A*q.B*q.H*
      poissonLength q ρ d*wattComparisonY q/(d:ℝ)*(1+wattShape q)^(1/4:ℝ)
    have hB' : 0 ≤ B := by dsimp [B]; positivity
    have hpair (frequencyPositive : Bool) (e : ℕ) (he : e ∈ d.divisors)
        (f : ℕ) (hf : f ∈ d.divisors) :
        ‖actualWattSum positive frequencyPositive q ρ α β W d e f x‖ ≤ B := by
      have hep := Nat.pos_of_mem_divisors he
      have hfp := Nat.pos_of_mem_divisors hf
      by_cases hfB : (f:ℝ) ≤ 2*q.B
      · have hediv := (Nat.mem_divisors.mp he).1
        have hfdiv := (Nat.mem_divisors.mp hf).1
        have he₂p := Nat.div_pos (Nat.le_of_dvd hdp hediv) hep
        have hf₄p := Nat.div_pos (Nat.le_of_dvd hdp hfdiv) hfp
        have heprod : (e:ℝ)*(d/e:ℕ) = d := by exact_mod_cast Nat.mul_div_cancel' hediv
        have hfprod : (f:ℝ)*(d/f:ℕ) = d := by exact_mod_cast Nat.mul_div_cancel' hfdiv
        have heval := actual_watt_majorant_bound h hK hρ.le (rho_le_one_hundredth hρ hδ hbound)
          (by exact_mod_cast hdp : (1:ℝ) ≤ d) (by exact_mod_cast hep : (1:ℝ) ≤ e)
          (by exact_mod_cast he₂p : (1:ℝ) ≤ (d/e:ℕ)) (by exact_mod_cast hfp : (1:ℝ) ≤ f)
          (by exact_mod_cast hf₄p : (1:ℝ) ≤ (d/f:ℕ)) heprod hfprod hfB
        exact (hfibre q α β W h hsize hw hmass d hd e he f hf x hx positive frequencyPositive).trans
          ((mul_le_mul_of_nonneg_left heval hC).trans_eq (by dsimp [B]; ring))
      · rw [actualWattSum_zero_of_short_beta hfp (lt_of_not_ge hfB),norm_zero]
        exact hB'
    have htri : ‖gcdBlockIntegrand positive q ρ α β W d x‖ ≤
        2*(d.divisors.card:ℝ)^2*B := by
      rw [gcdBlockIntegrand_eq_actualWattSums h.scales hw positive ρ hdp x]
      apply (norm_sum_le _ _).trans
      have hs : (∑ frequencyPositive : Bool,
          ‖∑ e ∈ d.divisors, ∑ f ∈ d.divisors,
            actualWattSum positive frequencyPositive q ρ α β W d e f x‖) ≤
          ∑ _frequencyPositive : Bool, ∑ _e ∈ d.divisors, ∑ _f ∈ d.divisors, B := by
        apply sum_le_sum; intro frequencyPositive _
        apply (norm_sum_le _ _).trans
        apply sum_le_sum; intro e he
        apply (norm_sum_le _ _).trans
        exact sum_le_sum (fun f hf => hpair frequencyPositive e he f hf)
      exact hs.trans_eq (by simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_bool]; ring)
    have hrootQ : q.mass^(1/2:ℝ) ≤ q.mass :=
      (Real.rpow_le_rpow_of_exponent_le hQ₁ (by norm_num : (1/2:ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
    have hdQ : (d:ℝ) ≤ q.mass := (mem_filter.mp hd).2.trans
      ((gcdCutoff_le_sqrt_mass q h.scales hρ.le).2.trans hrootQ)
    have hτd : (d.divisors.card:ℝ)^2 ≤ D*q.mass^(2*ρ) :=
      (hτ d hdp.ne').trans (by gcongr)
    calc _ ≤ 2*(D*q.mass^(2*ρ))*B := htri.trans (by gcongr)
      _ = _ := by
        dsimp [B]
        have he : q.mass^(2*ρ)*q.mass^(102*ρ) = q.mass^(104*ρ) := by
          rw [← Real.rpow_add hQ]
          congr 1
          ring
        calc _ = (2*C*wattEvaluationConstant ρ K*D)*(q.mass^(2*ρ)*q.mass^(102*ρ))*
            q.A*q.B*q.H*poissonLength q ρ d*wattComparisonY q/(d:ℝ)*(1+wattShape q)^(1/4:ℝ) := by ring
          _ = _ := by rw [he]
  · rw [gcdBlockIntegrand_eq_zero_off_support h.scales hw positive ρ d hx,norm_zero]
    positivity

theorem WeightedWattBound.actual_integrated_watt_bound (hWatt : WeightedWattBound)
    {ρ δ K : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hbound : ρ ≤ δ/(1000*(1+δ))) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ Q₀ C : ℝ, 1 ≤ Q₀ ∧ 0 ≤ C ∧
      ∀ (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
        ScaleGeometry ρ K q → (q.A*q.B)^δ ≤ K*q.M*q.N →
        NormalizedWeightData bounds q α β W → Q₀ ≤ q.mass →
        ∀ positive : Bool, ∀ d ∈ smallGcdSet q ρ,
          gcdBlockMass positive q ρ α β W d ≤
            C*q.mass^(200*ρ)*wattSummationCoefficient q/(d:ℝ) := by
  obtain ⟨Q₀,C,hQ₀,hC,hpoint⟩ := hWatt.actual_pointwise_watt_bound hρ hδ hbound hK bounds hb
  refine ⟨Q₀,2*K*C,hQ₀,by positivity,?_⟩
  intro q α β W h hsize hw hmass positive d hd
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hQ₁ := (poisson_scale_bounds q h.scales).1
  have hdp : 0 < d := (Finset.mem_Icc.mp (mem_filter.mp hd).1).1
  have hdr : (0:ℝ) < d := by exact_mod_cast hdp
  have hY := wattComparisonY_pos h
  have hLp := poissonLength_pos q h.scales ρ hdr
  have hrad := poissonRadius_pos q h.scales hdr
  have hLr := poissonLength_radius_le h hK hdr
  have hz : 0 ≤ wattShape q := by unfold wattShape; positivity
  have hcoef : 0 ≤ wattSummationCoefficient q := by
    unfold wattSummationCoefficient QuadraticScales.N
    positivity
  have hpoint' := hpoint q α β W h hsize hw hmass positive d hd
  have hmass' := gcdBlockMass_le_of_pointwise h.scales hw positive ρ hdp hpoint'
  have hmerge : q.mass^(104*ρ)*q.mass^(10*ρ) = q.mass^(114*ρ) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  calc _ ≤ 2*poissonRadius q d*
        (C*q.mass^(104*ρ)*q.A*q.B*q.H*poissonLength q ρ d*wattComparisonY q/(d:ℝ)*
          (1+wattShape q)^(1/4:ℝ)) := hmass'
    _ = (2*C)*q.mass^(104*ρ)*(poissonLength q ρ d*poissonRadius q d)*
        (q.A*q.B*q.H*wattComparisonY q/(d:ℝ)*(1+wattShape q)^(1/4:ℝ)) := by ring
    _ ≤ (2*C)*q.mass^(104*ρ)*(K*q.mass^(10*ρ))*
        (q.A*q.B*q.H*wattComparisonY q/(d:ℝ)*(1+wattShape q)^(1/4:ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hLr (by positivity)
    _ = (2*K*C)*q.mass^(114*ρ)*wattSummationCoefficient q/(d:ℝ) := by
      unfold wattSummationCoefficient
      rw [← watt_H_mul_comparisonY h]
      calc _ = (2*K*C)*(q.mass^(104*ρ)*q.mass^(10*ρ))*q.A*q.B*
          (q.H*wattComparisonY q)*(1+wattShape q)^(1/4:ℝ)/(d:ℝ) := by ring
        _ = _ := by rw [hmerge]; ring
    _ ≤ _ := by
      gcongr
      norm_num

end
end DivisorProof




namespace DivisorProof
open Real MeasureTheory Set Finset Classical Filter Asymptotics
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1200000

theorem analyticApplicationEstimates_of_watt
    (hWatt : WeightedWattBound) : AnalyticApplicationEstimates := by
  intro δ hδ ρ hρ hbound K hK bounds hb
  obtain ⟨CWeil,hCWeil,hweil⟩ := Estermann.actual_pointwise_weil_bound hρ hK bounds hb
  obtain ⟨Q₀,CWatt,hQ₀,hCWatt,hwatt⟩ :=
    hWatt.actual_integrated_watt_bound hρ hδ hbound hK bounds hb
  refine ⟨Q₀,CWeil,CWatt,hQ₀,hCWeil,hCWatt,?_⟩
  intro q α β W h hsize hw hmass positive
  constructor
  · intro d hd x
    have hdp : 0 < d := (Finset.mem_Icc.mp (mem_filter.mp hd).1).1
    exact hweil q α β W h hw positive d hdp x
  · exact hwatt q α β W h hsize hw hmass positive

theorem quantifiedDivisorBound_of_watt
    (hWatt : WeightedWattBound) : QuantifiedDivisorBound :=
  quantifiedDivisorBound_of_analytic_applications
    (analyticApplicationEstimates_of_watt hWatt)

theorem separatedDivisorBound_of_watt
    (hWatt : WeightedWattBound) : SeparatedDivisorBound :=
  separatedDivisorBound_of_quantified (quantifiedDivisorBound_of_watt hWatt)

theorem actual_source_bound_of_watt
    (hWatt : WeightedWattBound)
    {ε δ K : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ),
      QuadraticAdmissible (inputExponent ε δ) δ K bounds q α β W →
      ∀ positive : Bool, ∀ X T D r K₀ : ℝ,
      0 < X → 0 < T → 0 ≤ D → 0 < K₀ → q.mass = q.A*q.B*X^2 →
      q.mass ≤ D*T^r → q.mass*q.H^2 ≤ D*T^r →
      q.H ≤ K₀*(q.A*q.B)^(1/2:ℝ)*X/T →
      ‖reconstructedDivisorError positive q α β W T X‖ ≤
        C*(D^ε*T^(r*ε))*sourceReconstructionMajorant q X T K₀ :=
  actual_source_bound_of_separated (separatedDivisorBound_of_watt hWatt)
    hε hδ hK bounds hb

theorem actual_source_error_isLittleO_of_watt
    (hWatt : WeightedWattBound)
    {a b s u K D Dmass : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hrange : 3*a+5*b < 2)
    (hs : 0 ≤ s) (hs' : s ≤ sourceGap a b/64)
    (hu : 0 ≤ u) (hu' : u ≤ sourceGap a b/64)
    (hK : 1 ≤ K) (hD : 1 ≤ D) (hDmass : 0 ≤ Dmass)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j)
    (q : ℝ → QuadraticScales) (α β : ℝ → ℕ → ℂ) (W : ℝ → Fin 5 → ℝ → ℝ)
    (X K₀ : ℝ → ℝ) (positive : Bool) (k : ℕ)
    (hdata : ∀ᶠ T : ℝ in atTop,
      QuadraticAdmissible (inputExponent (sourceGap a b/64) 1) 1 K bounds
        (q T) (α T) (β T) (W T) ∧
      0 < X T ∧ 0 < K₀ T ∧ (q T).mass = (q T).A*(q T).B*(X T)^2 ∧
      (q T).mass ≤ Dmass*T^4 ∧ (q T).mass*(q T).H^2 ≤ Dmass*T^4 ∧
      (q T).H ≤ K₀ T*((q T).A*(q T).B)^(1/2:ℝ)*X T/T ∧
      (q T).A ≤ D*T^a ∧ (q T).B ≤ D*T^b ∧
      X T ≤ D*T^(1+u/2) ∧ K₀ T ≤ D*T^s) :
    (fun T : ℝ => ((Real.log T)^k:ℂ)*
      reconstructedDivisorError positive (q T) (α T) (β T) (W T) T (X T)) =o[atTop]
      (fun T : ℝ => T) :=
  actual_source_error_isLittleO_of_separated (separatedDivisorBound_of_watt hWatt)
    ha hab hrange hs hs' hu hu' hK hD hDmass bounds hb q α β W X K₀ positive k hdata

end
end DivisorProof
