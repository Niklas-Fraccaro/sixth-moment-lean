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
import SixthMoment.Arithmetic.QuadraticDivisor.Reduction.WattParameters
import Std

namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

structure ScaleGeometry (ρ K : ℝ) (q : QuadraticScales) : Prop where
  scales : ∀ j, 1 ≤ q.size j
  orderM : q.M₁ ≤ q.M₂*q.mass^ρ
  orderN : q.N₁ ≤ q.N₂*q.mass^ρ
  shift : q.H ≤ K*(q.A*q.B)^(1/2+ρ)
  balanceM : q.A*q.M ≤ K*q.B*q.N
  balanceN : q.B*q.N ≤ K*q.A*q.M
  orientation : q.B*q.N₁ ≤ q.A*q.M₁

theorem QuadraticAdmissible.geometry {ρ δ K : ℝ} {bounds : ℕ → ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : QuadraticAdmissible ρ δ K bounds q α β W) : ScaleGeometry ρ K q := by
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1⟩

theorem ScaleGeometry.pos {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) :
    0 < q.A ∧ 0 < q.B ∧ 0 < q.M₁ ∧ 0 < q.M₂ ∧
      0 < q.N₁ ∧ 0 < q.N₂ ∧ 0 < q.H ∧ 0 < q.mass := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | exact lt_of_lt_of_le (by norm_num) (h.scales 0)
    | exact lt_of_lt_of_le (by norm_num) (h.scales 1)
    | exact lt_of_lt_of_le (by norm_num) (h.scales 2)
    | exact lt_of_lt_of_le (by norm_num) (h.scales 3)
    | exact lt_of_lt_of_le (by norm_num) (h.scales 4)
    | exact lt_of_lt_of_le (by norm_num) (h.scales 5)
    | exact lt_of_lt_of_le (by norm_num) (h.scales 6)
    | exact lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h.scales).1

theorem ScaleGeometry.log_bounds {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) :
    Real.log q.mass = Real.log q.A+Real.log q.B+Real.log q.M₁+
      Real.log q.M₂+Real.log q.N₁+Real.log q.N₂ ∧
    Real.log q.M₁ ≤ Real.log q.M₂+ρ*Real.log q.mass ∧
    Real.log q.N₁ ≤ Real.log q.N₂+ρ*Real.log q.mass ∧
    Real.log q.H ≤ Real.log K+(1/2+ρ)*(Real.log q.A+Real.log q.B) ∧
    Real.log q.A+Real.log q.M₁+Real.log q.M₂ ≤
      Real.log K+Real.log q.B+Real.log q.N₁+Real.log q.N₂ ∧
    Real.log q.B+Real.log q.N₁+Real.log q.N₂ ≤
      Real.log K+Real.log q.A+Real.log q.M₁+Real.log q.M₂ := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hKp : 0 < K := by linarith
  have h₁ := Real.log_le_log hM₁ h.orderM
  have h₂ := Real.log_le_log hN₁ h.orderN
  have h₃ := Real.log_le_log hH h.shift
  have h₄ := Real.log_le_log (by dsimp [QuadraticScales.M]; positivity) h.balanceM
  have h₅ := Real.log_le_log (by dsimp [QuadraticScales.N]; positivity) h.balanceN
  simp (disch := positivity) only [QuadraticScales.M,QuadraticScales.N,
    Real.log_mul,Real.log_rpow] at h₁ h₂ h₃ h₄ h₅
  refine ⟨?_,h₁,h₂,h₃,?_,?_⟩
  · simp (disch := positivity) only [QuadraticScales.mass,QuadraticScales.M,
      QuadraticScales.N,Real.log_mul]
    ring
  · linarith
  · linarith

theorem ScaleGeometry.log_nonneg {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) :
    0 ≤ Real.log q.A ∧ 0 ≤ Real.log q.B ∧ 0 ≤ Real.log q.mass ∧ 0 ≤ Real.log K := by
  exact ⟨Real.log_nonneg (h.scales 0),Real.log_nonneg (h.scales 1),
    Real.log_nonneg (poisson_scale_bounds q h.scales).1,Real.log_nonneg hK⟩

theorem weil_tail_first_monomial {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 ≤ ρ) :
    q.A^(1/4:ℝ)*q.B^(3/4:ℝ)*q.N₁^(3/2:ℝ)*q.H ≤
      K^2*q.mass^(2*ρ)*E₁ q := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hKp : 0 < K := by linarith
  obtain ⟨hlog,hM,hN,hshift,hbalM,hbalN⟩ := h.log_bounds hK
  obtain ⟨ha,hb,hq,hk⟩ := h.log_nonneg hK
  have habq : Real.log q.A+Real.log q.B ≤ Real.log q.mass := by
    have hh := Real.log_le_log (mul_pos hA hB) (product_AB_le_mass q h.scales).2
    simpa only [Real.log_mul hA.ne' hB.ne'] using hh
  have hshift' : Real.log q.H ≤ Real.log K+
      (Real.log q.A+Real.log q.B)/2+ρ*Real.log q.mass := by nlinarith
  apply (Real.log_le_log_iff (by positivity) (by unfold E₁; positivity)).mp
  simp (disch := positivity) only [E₁,Real.log_mul,Real.log_pow,Real.log_rpow]
  nlinarith

theorem weil_tail_second_monomial {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 ≤ ρ) :
    q.A^(1/4:ℝ)*q.B^(-1/4:ℝ)*q.M₁*q.N₁^(1/2:ℝ)*q.H ≤
      K^2*q.mass^(2*ρ)*E₁ q := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hKp : 0 < K := by linarith
  obtain ⟨hlog,hM,hN,hshift,hbalM,hbalN⟩ := h.log_bounds hK
  obtain ⟨ha,hb,hq,hk⟩ := h.log_nonneg hK
  have habq : Real.log q.A+Real.log q.B ≤ Real.log q.mass := by
    have hh := Real.log_le_log (mul_pos hA hB) (product_AB_le_mass q h.scales).2
    simpa only [Real.log_mul hA.ne' hB.ne'] using hh
  have hshift' : Real.log q.H ≤ Real.log K+
      (Real.log q.A+Real.log q.B)/2+ρ*Real.log q.mass := by nlinarith
  apply (Real.log_le_log_iff (by positivity) (by unfold E₁; positivity)).mp
  simp (disch := positivity) only [E₁,Real.log_mul,Real.log_pow,Real.log_rpow]
  nlinarith

def wattShape (q : QuadraticScales) : ℝ := q.N₁^2*q.H/(q.A^3*q.B^2)

def wattSummationCoefficient (q : QuadraticScales) : ℝ :=
  q.A*q.B*(q.B*q.N*q.H)^(1/2:ℝ)*(1+wattShape q)^(1/4:ℝ)

theorem watt_base_monomial {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) :
    q.A*q.B*(q.B*q.N*q.H)^(1/2:ℝ) ≤ K^2*E₀ q := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hKp : 0 < K := by linarith
  obtain ⟨hlog,_,_,_,_,hbal⟩ := h.log_bounds hK
  have hk := (h.log_nonneg hK).2.2.2
  apply (Real.log_le_log_iff (by dsimp [QuadraticScales.N]; positivity)
    (by unfold E₀; positivity)).mp
  simp (disch := positivity) only [E₀,QuadraticScales.N,
    Real.log_mul,Real.log_pow,Real.log_rpow]
  linarith

theorem watt_extra_monomial {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 ≤ ρ) :
    q.A*q.B*(q.B*q.N*q.H)^(1/2:ℝ)*(wattShape q)^(1/4:ℝ) ≤
      K^2*q.mass^ρ*E₂ q := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hKp : 0 < K := by linarith
  obtain ⟨hlog,_,hN,_,_,hbal⟩ := h.log_bounds hK
  have hk := (h.log_nonneg hK).2.2.2
  have hq := (h.log_nonneg hK).2.2.1
  apply (Real.log_le_log_iff (by dsimp [QuadraticScales.N,wattShape]; positivity)
    (by unfold E₂; positivity)).mp
  simp (disch := positivity) only [E₂,wattShape,QuadraticScales.N,
    Real.log_mul,Real.log_div,Real.log_pow,Real.log_rpow]
  nlinarith

theorem watt_summation_coefficient_le {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 ≤ ρ) :
    wattSummationCoefficient q ≤ K^2*q.mass^ρ*(E₀ q+E₂ q) := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hz : 0 ≤ wattShape q := by unfold wattShape; positivity
  have hroot : (1+wattShape q)^(1/4:ℝ) ≤ 1+(wattShape q)^(1/4:ℝ) := by
    simpa using Real.rpow_add_le_add_rpow (by norm_num : (0:ℝ) ≤ 1) hz
      (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) ≤ 1)
  have hE₀ : 0 ≤ E₀ q := by unfold E₀; positivity
  have hbase := watt_base_monomial h hK
  have hbase' : q.A*q.B*(q.B*q.N*q.H)^(1/2:ℝ) ≤ K^2*q.mass^ρ*E₀ q :=
    hbase.trans (by
      calc K^2*E₀ q ≤ (K^2*E₀ q)*q.mass^ρ :=
          le_mul_of_one_le_right (by positivity)
            (Real.one_le_rpow (poisson_scale_bounds q h.scales).1 hρ)
        _ = _ := by ring)
  calc wattSummationCoefficient q ≤
      q.A*q.B*(q.B*q.N*q.H)^(1/2:ℝ)*(1+(wattShape q)^(1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hroot (by dsimp [QuadraticScales.N]; positivity)
    _ = q.A*q.B*(q.B*q.N*q.H)^(1/2:ℝ)+
        q.A*q.B*(q.B*q.N*q.H)^(1/2:ℝ)*(wattShape q)^(1/4:ℝ) := by ring
    _ ≤ K^2*q.mass^ρ*E₀ q+K^2*q.mass^ρ*E₂ q :=
      add_le_add hbase' (watt_extra_monomial h hK hρ)
    _ = _ := by ring

def weilSummationCoefficient (q : QuadraticScales) (ρ : ℝ) : ℝ :=
  q.A*q.H*(q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁)*(gcdCutoff q ρ)^(-3/2:ℝ)

theorem weil_cutoff_first_identity {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) :
    q.A*q.H*(q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁)*(gcdCutoff q ρ)^(-3/2:ℝ) =
      q.mass^(150*ρ)*(q.A^(1/4:ℝ)*q.B^(3/4:ℝ)*q.N₁^(3/2:ℝ)*q.H) := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi]
    unfold gcdCutoff
    positivity
  · simp only [Set.mem_Ioi]
    positivity
  · simp (disch := positivity) only [gcdCutoff,Real.log_mul,Real.log_rpow]
    ring

theorem weil_cutoff_second_identity {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) :
    q.A*q.H*(q.B*q.N₁)^(1/2:ℝ)*q.M₁*(gcdCutoff q ρ)^(-3/2:ℝ) =
      q.mass^(150*ρ)*(q.A^(1/4:ℝ)*q.B^(-1/4:ℝ)*q.M₁*q.N₁^(1/2:ℝ)*q.H) := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi]
    unfold gcdCutoff
    positivity
  · simp only [Set.mem_Ioi]
    positivity
  · simp (disch := positivity) only [gcdCutoff,Real.log_mul,Real.log_rpow]
    ring

theorem weil_summation_coefficient_le {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 ≤ ρ) :
    weilSummationCoefficient q ρ ≤ 2*K^2*q.mass^(152*ρ)*E₁ q := by
  have hQ := h.pos.2.2.2.2.2.2.2
  have hp : 0 ≤ q.mass^(150*ρ) := Real.rpow_nonneg hQ.le _
  have hmul : q.mass^(150*ρ)*q.mass^(2*ρ) = q.mass^(152*ρ) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  unfold weilSummationCoefficient
  rw [mul_add,add_mul,weil_cutoff_first_identity h,weil_cutoff_second_identity h]
  calc _ ≤ q.mass^(150*ρ)*(K^2*q.mass^(2*ρ)*E₁ q)+
      q.mass^(150*ρ)*(K^2*q.mass^(2*ρ)*E₁ q) :=
        add_le_add (mul_le_mul_of_nonneg_left (weil_tail_first_monomial h hK hρ) hp)
          (mul_le_mul_of_nonneg_left (weil_tail_second_monomial h hK hρ) hp)
    _ = 2*K^2*(q.mass^(150*ρ)*q.mass^(2*ρ))*E₁ q := by ring
    _ = _ := by rw [hmul]

end
end DivisorProof



namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def gcdBlockMass (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (d : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, ‖gcdBlockIntegrand positive q ρ α β W d x‖

theorem gcdBlockMass_nonneg (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (d : ℕ) :
    0 ≤ gcdBlockMass positive q ρ α β W d := integral_nonneg (fun _ => norm_nonneg _)

theorem norm_gcdBlockIntegral_le (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (d : ℕ) :
    ‖∫ x : ℝ in Ioi 0, gcdBlockIntegrand positive q ρ α β W d x‖ ≤
      gcdBlockMass positive q ρ α β W d := norm_integral_le_integral_norm _

theorem outerProfile_nonzero_spatial_bounds {bounds : ℕ → ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    {n : Fin 5 → ℕ} (hn : n ∈ quadraticMainIndexSet q)
    (hweight : poissonOuterWeight q α β W n ≠ 0) {x : ℝ}
    (hprofile : outerPoissonProfile q W n x ≠ 0) :
    x ∈ Icc (poissonRadius q (outerGCD n)/4) (2*poissonRadius q (outerGCD n)) := by
  have hY : (0:ℝ) < outerRight n := by exact_mod_cast outerRight_pos hn
  have hd : (0:ℝ) < outerGCD n := by exact_mod_cast outerGCD_pos hn
  have hM : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hN : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (h 4)
  have hw₂ : W 2 (((outerRight n : ℝ)/((outerGCD n : ℝ)*q.M₂))*x) ≠ 0 := by
    intro hz
    exact hprofile (by simp [outerPoissonProfile,poissonProfile,hz])
  have hs := (hw.smooth 2).2 (subset_tsupport _ hw₂)
  have hx : 0 < x := by
    by_contra hh
    have ha := div_pos hY (mul_pos hd hM)
    have hz := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hh)
    linarith [hs.1]
  obtain ⟨_,hYlo,hYhi⟩ := outer_products_bounds h hw hn hweight
  have h₁ : (outerGCD n : ℝ)*q.M₂ ≤ (outerRight n : ℝ)*x := by
    have ht := (le_div_iff₀ (mul_pos hd hM)).mp
      (show 1 ≤ (outerRight n : ℝ)*x/((outerGCD n : ℝ)*q.M₂) by
        simpa only [div_mul_eq_mul_div] using hs.1)
    simpa using ht
  have h₂ : (outerRight n : ℝ)*x ≤ 2*((outerGCD n : ℝ)*q.M₂) := by
    apply (div_le_iff₀ (mul_pos hd hM)).mp
    simpa only [div_mul_eq_mul_div] using hs.2
  constructor
  · unfold poissonRadius
    rw [div_div]
    apply (div_le_iff₀ (by positivity : 0 < q.B*q.N₁*4)).mpr
    have ht := mul_le_mul_of_nonneg_right hYhi hx.le
    nlinarith
  · unfold poissonRadius
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (mul_pos hB hN)).mpr
    have ht := mul_le_mul_of_nonneg_right hYlo hx.le
    nlinarith

theorem gcdBlockIntegrand_eq_zero_off_support {bounds : ℕ → ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (positive : Bool) (ρ : ℝ) (d : ℕ) {x : ℝ}
    (hx : x ∉ Icc (poissonRadius q d/4) (2*poissonRadius q d)) :
    gcdBlockIntegrand positive q ρ α β W d x = 0 := by
  apply sum_eq_zero
  intro n hn
  obtain ⟨hn,hgd⟩ := mem_filter.mp hn
  by_cases hz : poissonOuterWeight q α β W n = 0
  · simp [hz]
  by_cases hp : outerPoissonProfile q W n x = 0
  · simp [outerFourierIntegrand,hp]
  have hs := outerProfile_nonzero_spatial_bounds h hw hn hz hp
  rw [hgd] at hs
  exact (hx hs).elim

theorem gcdBlockMass_le_of_pointwise {bounds : ℕ → ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (positive : Bool) (ρ : ℝ) {d : ℕ} (hd : 0 < d) {C : ℝ}
    (hpoint : ∀ x, ‖gcdBlockIntegrand positive q ρ α β W d x‖ ≤ C) :
    gcdBlockMass positive q ρ α β W d ≤ 2*poissonRadius q d*C := by
  have hr := poissonRadius_pos q h (by exact_mod_cast hd : (0:ℝ) < d)
  have hint := (gcdBlockIntegrand_integrable h hw.smooth positive ρ α β d).norm
  have hs₁ : (∫ x : ℝ in Ioi 0, ‖gcdBlockIntegrand positive q ρ α β W d x‖) =
      ∫ x : ℝ, ‖gcdBlockIntegrand positive q ρ α β W d x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [gcdBlockIntegrand_eq_zero_off_support h hw positive ρ d (by
      intro hh
      have hx' : x ≤ 0 := le_of_not_gt hx
      linarith [hh.1]),norm_zero]
  have hs₂ : (∫ x : ℝ in Icc 0 (2*poissonRadius q d),
      ‖gcdBlockIntegrand positive q ρ α β W d x‖) =
      ∫ x : ℝ, ‖gcdBlockIntegrand positive q ρ α β W d x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [gcdBlockIntegrand_eq_zero_off_support h hw positive ρ d (by
      intro hh
      exact hx ⟨by linarith [hh.1],hh.2⟩),norm_zero]
  unfold gcdBlockMass
  rw [hs₁,← hs₂]
  calc _ ≤ ∫ _x : ℝ in Icc 0 (2*poissonRadius q d), C :=
      setIntegral_mono_on hint.integrableOn continuous_const.integrableOn_Icc
        measurableSet_Icc (fun x _ => hpoint x)
    _ = _ := by simp [hr.le,mul_comm]

theorem poissonLength_radius_le {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) {d : ℝ} (hd : 0 < d) :
    poissonLength q ρ d*poissonRadius q d ≤ K*q.mass^(10*ρ) := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hN : 0 < q.N := by dsimp [QuadraticScales.N]; positivity
  have hKp : 0 < K := by linarith
  have hq : q.mass ≤ K*(q.B*q.N)^2 := by
    rw [mass_eq_balanced_product]
    calc (q.A*q.M)*(q.B*q.N) ≤ (K*q.B*q.N)*(q.B*q.N) :=
        mul_le_mul_of_nonneg_right h.balanceM (mul_pos hB hN).le
      _ = _ := by ring
  have hs : Real.sqrt q.mass ≤ K*(q.B*q.N) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hQ.le,mul_pow]
    have hkk : K ≤ K^2 := by nlinarith
    exact hq.trans (mul_le_mul_of_nonneg_right hkk (sq_nonneg _))
  rw [poissonLength_mul_radius q h.scales ρ hd]
  exact mul_le_mul_of_nonneg_right ((div_le_iff₀ (mul_pos hB hN)).mpr hs)
    (Real.rpow_nonneg hQ.le _)

end
end DivisorProof



namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def smallGcdSet (q : QuadraticScales) (ρ : ℝ) : Finset ℕ :=
  (gcdIndexSet q).filter (fun d : ℕ => (d:ℝ) ≤ gcdCutoff q ρ)

def largeGcdSet (q : QuadraticScales) (ρ : ℝ) : Finset ℕ :=
  (gcdIndexSet q).filter (fun d : ℕ => gcdCutoff q ρ < (d:ℝ))

def smallGcdMass (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) : ℝ :=
  ∑ d ∈ smallGcdSet q ρ, gcdBlockMass positive q ρ α β W d

def largeGcdMass (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) : ℝ :=
  ∑ d ∈ largeGcdSet q ρ, gcdBlockMass positive q ρ α β W d

theorem smallGcdMass_nonneg (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) :
    0 ≤ smallGcdMass positive q ρ α β W :=
  sum_nonneg (fun d _ => gcdBlockMass_nonneg positive q ρ α β W d)

theorem largeGcdMass_nonneg (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) :
    0 ≤ largeGcdMass positive q ρ α β W :=
  sum_nonneg (fun d _ => gcdBlockMass_nonneg positive q ρ α β W d)

theorem actual_discrepancy_le_block_masses (positive : Bool) (q : QuadraticScales)
    (ρ : ℝ) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) :
    ‖signedQuadraticDiscrepancy positive q α β W‖ ≤
      smallGcdMass positive q ρ α β W+largeGcdMass positive q ρ α β W+
        ‖normalFormError positive q ρ α β W‖ := by
  rw [actual_normal_form_one_cutoff ρ positive α β W]
  calc _ ≤ ‖∑ d ∈ smallGcdSet q ρ,
      ∫ x : ℝ in Ioi 0, gcdBlockIntegrand positive q ρ α β W d x‖+
      ‖∑ d ∈ largeGcdSet q ρ,
      ∫ x : ℝ in Ioi 0, gcdBlockIntegrand positive q ρ α β W d x‖+
      ‖normalFormError positive q ρ α β W‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add
      ((norm_sum_le _ _).trans (sum_le_sum (fun d _ => norm_gcdBlockIntegral_le positive q ρ α β W d)))
      ((norm_sum_le _ _).trans (sum_le_sum (fun d _ => norm_gcdBlockIntegral_le positive q ρ α β W d)))) le_rfl

theorem smallGcdSet_harmonic_le {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hρ : 0 < ρ) :
    ∑ d ∈ smallGcdSet q ρ, (1:ℝ)/d ≤ (1+1/ρ)*q.mass^ρ := by
  have hD := gcdCutoff_pos q (ρ := ρ) h.scales
  have hsub : smallGcdSet q ρ ⊆ Icc 1 ⌊gcdCutoff q ρ⌋₊ := by
    intro d hd
    obtain ⟨hd,hcut⟩ := mem_filter.mp hd
    exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1,(Nat.le_floor_iff hD.le).mpr hcut⟩
  have hQ := (poisson_scale_bounds q h.scales).1
  have hDQ : gcdCutoff q ρ ≤ q.mass :=
    (gcdCutoff_le_sqrt_mass q h.scales hρ.le).2.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ
        (by norm_num : (1/2:ℝ) ≤ 1))
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)).trans
    (harmonic_sum_le_subpower hρ hQ _ hDQ)

theorem smallGcdMass_bound_of_integral_estimate {ρ K C : ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (positive : Bool)
    (hblock : ∀ d ∈ smallGcdSet q ρ,
      gcdBlockMass positive q ρ α β W d ≤
        C*q.mass^(200*ρ)*wattSummationCoefficient q/(d:ℝ)) :
    smallGcdMass positive q ρ α β W ≤
      (C*(1+1/ρ)*K^2)*q.mass^(210*ρ)*(E₀ q+E₂ q) := by
  have hQ := h.pos.2.2.2.2.2.2.2
  have hQ₁ := (poisson_scale_bounds q h.scales).1
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,_⟩ := h.pos
  have hcoeff : 0 ≤ wattSummationCoefficient q := by
    dsimp [wattSummationCoefficient,wattShape,QuadraticScales.N]
    positivity
  have hE : 0 ≤ E₀ q+E₂ q := by unfold E₀ E₂; positivity
  have hpow : q.mass^(200*ρ)*q.mass^ρ*q.mass^ρ = q.mass^(202*ρ) := by
    rw [← Real.rpow_add hQ,← Real.rpow_add hQ]
    congr 1
    ring
  unfold smallGcdMass
  calc _ ≤ ∑ d ∈ smallGcdSet q ρ, C*q.mass^(200*ρ)*wattSummationCoefficient q/(d:ℝ) :=
      sum_le_sum hblock
    _ = (C*q.mass^(200*ρ)*wattSummationCoefficient q)*
        ∑ d ∈ smallGcdSet q ρ, (1:ℝ)/d := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ (C*q.mass^(200*ρ)*wattSummationCoefficient q)*((1+1/ρ)*q.mass^ρ) :=
      mul_le_mul_of_nonneg_left (smallGcdSet_harmonic_le h hρ) (by positivity)
    _ = C*(1+1/ρ)*q.mass^(200*ρ)*q.mass^ρ*wattSummationCoefficient q := by ring
    _ ≤ C*(1+1/ρ)*q.mass^(200*ρ)*q.mass^ρ*(K^2*q.mass^ρ*(E₀ q+E₂ q)) :=
      mul_le_mul_of_nonneg_left (watt_summation_coefficient_le h hK hρ.le) (by positivity)
    _ = (C*(1+1/ρ)*K^2)*(q.mass^(200*ρ)*q.mass^ρ*q.mass^ρ)*(E₀ q+E₂ q) := by ring
    _ = (C*(1+1/ρ)*K^2)*q.mass^(202*ρ)*(E₀ q+E₂ q) := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ₁ (by linarith))
        (by positivity)) hE

theorem largeGcdMass_bound_of_integral_estimate {ρ K C : ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (positive : Bool)
    (hblock : ∀ d ∈ largeGcdSet q ρ,
      gcdBlockMass positive q ρ α β W d ≤
        C*q.mass^(15*ρ)*q.A*q.H*(q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁)*
          (d:ℝ)^(-5/2:ℝ)) :
    largeGcdMass positive q ρ α β W ≤
      ((10/3:ℝ)*C*K^2)*q.mass^(170*ρ)*E₁ q := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hD := gcdCutoff_pos q (ρ := ρ) h.scales
  have hQ₁ := (poisson_scale_bounds q h.scales).1
  have hE : 0 ≤ E₁ q := by unfold E₁; positivity
  have hpow : q.mass^(15*ρ)*q.mass^(152*ρ) = q.mass^(167*ρ) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  unfold largeGcdMass
  calc _ ≤ ∑ d ∈ largeGcdSet q ρ,
      C*q.mass^(15*ρ)*q.A*q.H*(q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁)*(d:ℝ)^(-5/2:ℝ) :=
      sum_le_sum hblock
    _ = (C*q.mass^(15*ρ)*q.A*q.H*(q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁))*
        ∑ d ∈ largeGcdSet q ρ, (d:ℝ)^(-5/2:ℝ) := by rw [mul_sum]
    _ ≤ (C*q.mass^(15*ρ)*q.A*q.H*(q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁))*
        ((5/3:ℝ)*(gcdCutoff q ρ)^(-3/2:ℝ)) :=
      mul_le_mul_of_nonneg_left (tail_rpow_bound hD ⌊2*q.H⌋₊) (by positivity)
    _ = ((5/3:ℝ)*C)*q.mass^(15*ρ)*weilSummationCoefficient q ρ := by
      unfold weilSummationCoefficient
      ring
    _ ≤ ((5/3:ℝ)*C)*q.mass^(15*ρ)*(2*K^2*q.mass^(152*ρ)*E₁ q) :=
      mul_le_mul_of_nonneg_left (weil_summation_coefficient_le h hK hρ.le) (by positivity)
    _ = ((10/3:ℝ)*C*K^2)*(q.mass^(15*ρ)*q.mass^(152*ρ))*E₁ q := by ring
    _ = ((10/3:ℝ)*C*K^2)*q.mass^(167*ρ)*E₁ q := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ₁ (by linarith))
        (by positivity)) hE

theorem weil_pointwise_to_block_integral {ρ K C : ℝ}
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ}
    {W : Fin 5 → ℝ → ℝ} (h : ScaleGeometry ρ K q) (hK : 1 ≤ K)
    (hw : NormalizedWeightData bounds q α β W) (hC : 0 ≤ C)
    (positive : Bool) {d : ℕ} (hd : 0 < d)
    (hpoint : ∀ x, ‖gcdBlockIntegrand positive q ρ α β W d x‖ ≤
      C*q.mass^(5*ρ)*q.A*poissonLength q ρ d*q.H*
        (q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁)*(d:ℝ)^(-5/2:ℝ)) :
    gcdBlockMass positive q ρ α β W d ≤
      (2*K*C)*q.mass^(15*ρ)*q.A*q.H*(q.B*q.N₁)^(1/2:ℝ)*
        (q.B*q.N₁+q.M₁)*(d:ℝ)^(-5/2:ℝ) := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hpow : q.mass^(5*ρ)*q.mass^(10*ρ) = q.mass^(15*ρ) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  calc _ ≤ 2*poissonRadius q d*(C*q.mass^(5*ρ)*q.A*poissonLength q ρ d*q.H*
        (q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁)*(d:ℝ)^(-5/2:ℝ)) :=
      gcdBlockMass_le_of_pointwise h.scales hw positive ρ hd hpoint
    _ = (2*C*q.mass^(5*ρ)*q.A*q.H*(q.B*q.N₁)^(1/2:ℝ)*
        (q.B*q.N₁+q.M₁)*(d:ℝ)^(-5/2:ℝ))*(poissonLength q ρ d*poissonRadius q d) := by ring
    _ ≤ (2*C*q.mass^(5*ρ)*q.A*q.H*(q.B*q.N₁)^(1/2:ℝ)*
        (q.B*q.N₁+q.M₁)*(d:ℝ)^(-5/2:ℝ))*(K*q.mass^(10*ρ)) :=
      mul_le_mul_of_nonneg_left (poissonLength_radius_le h hK hd') (by positivity)
    _ = (2*K*C)*(q.mass^(5*ρ)*q.mass^(10*ρ))*q.A*q.H*(q.B*q.N₁)^(1/2:ℝ)*
        (q.B*q.N₁+q.M₁)*(d:ℝ)^(-5/2:ℝ) := by ring
    _ = _ := by rw [hpow]

end
end DivisorProof



namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1600000

theorem kloostermanSum_one (u v : ℤ) : kloostermanSum 1 u v = 1 := by
  have hinv : inverseRepresentative 0 1 = 0 := by
    unfold inverseRepresentative
    have hz : ((0:ZMod 1)⁻¹) = 0 := Subsingleton.elim _ _
    change ((0:ZMod 1)⁻¹).val = 0
    rw [hz]
    rfl
  simp [kloostermanSum,hinv]

theorem Estermann.fixed_second_parameter
    {c : ℕ} (hc : 0 < c) (u v : ℤ) :
    ‖kloostermanSum c u v‖ ≤ twoAdicWeight c*(c.divisors.card:ℝ)*(c:ℝ)^(1/2:ℝ)*
      (Nat.gcd v.natAbs c:ℝ)^(1/2:ℝ) := by
  have hdiv : Nat.gcd (Nat.gcd u.natAbs v.natAbs) c ∣ Nat.gcd v.natAbs c := by
    exact Nat.dvd_gcd
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)) (Nat.gcd_dvd_right _ _)
  have hle : Nat.gcd (Nat.gcd u.natAbs v.natAbs) c ≤ Nat.gcd v.natAbs c :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ hc) hdiv
  apply (kloostermanSum_estermann hc u v).trans
  gcongr

structure WattWeightData (b : ℕ → ℝ) (g : ℕ → ℕ → ℝ)
    (p : WattScales) (Δ : ℝ) (a bcoeff : ℕ → ℂ)
    (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ) : Prop where
  alpha_support : ∀ n : ℕ, (n:ℝ) ∉ Icc (p.R/2) p.R → a n = 0
  beta_support : ∀ n : ℕ, (n:ℝ) ∉ Icc (p.S/2) p.S → bcoeff n = 0
  alpha_bound : ∀ n, ‖a n‖ ≤ 1
  beta_bound : ∀ n, ‖bcoeff n‖ ≤ 1
  smooth₀ : ContDiff ℝ ∞ u₀
  smooth₁ : ContDiff ℝ ∞ u₁
  support₀ : tsupport u₀ ⊆ Icc (1/2) p.H
  support₁ : tsupport u₁ ⊆ Icc (1/2) p.C
  derivatives : ∀ j x, 0 < x →
    ‖iteratedDeriv j u₀ x‖+‖iteratedDeriv j u₁ x‖ ≤ b j*(Δ*x)^(-(j:ℝ))
  gamma_smooth : ∀ r s, ContDiff ℝ ∞ (fun z : ℝ × ℝ => γ r s z.1 z.2)
  gamma_support : ∀ r s,
    tsupport (fun z : ℝ × ℝ => γ r s z.1 z.2) ⊆
      (Icc (p.V/2) p.V) ×ˢ (Icc (p.P/2) p.P)
  gamma_derivatives : ∀ r s i j x y, 0 < x → 0 < y →
    ‖iteratedDeriv j (fun y => iteratedDeriv i (fun x => γ r s x y) x) y‖ ≤
      g i j*x^(-(i:ℝ))*y^(-(j:ℝ))

def WattScales.size (p : WattScales) : Fin 6 → ℝ := ![p.H,p.C,p.R,p.S,p.V,p.P]

def wattIndexSet (p : WattScales) : Finset (Fin 6 → ℕ) :=
  Fintype.piFinset (fun i => Icc 1 ⌊p.size i⌋₊)

def weightedWattSum (positive : Bool) (p : WattScales)
    (a b : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ) : ℂ :=
  ∑ n ∈ (wattIndexSet p).filter (fun n => (n 2*n 4).Coprime (n 3*n 5)),
    u₀ (n 0)*u₁ (n 1)*a (n 2)*b (n 3)*γ (n 2) (n 3) (n 4) (n 5)*
      ePhase ((if positive then (1:ℝ) else -1)*(n 0:ℝ)*n 1*
        (inverseRepresentative (n 2*n 4) (n 3*n 5):ℝ)/(n 3*n 5:ℕ))

def wattMajorant (p : WattScales) (Δ η : ℝ) : ℝ :=
  Δ^(-7/2:ℝ)*p.H*p.C*p.R*(p.V+p.S*p.X)*
    (1+p.H*p.C/(p.R*p.S))^(1/2:ℝ)*
    (1+p.P/(p.R*p.V))^(1/2:ℝ)*
    (1+p.H^2*p.C*p.P*p.X^2/(p.R^4*p.S^3*p.V))^(1/4:ℝ)*
    (p.H*p.C*p.R*p.S*p.V*p.P)^(20*η)

def WeightedWattBound : Prop :=
  ∀ η : ℝ, 0 < η → ∀ b : ℕ → ℝ, (∀ j, 0 ≤ b j) →
  ∀ g : ℕ → ℕ → ℝ, (∀ i j, 0 ≤ g i j) →
    ∃ C F : ℝ, 0 ≤ C ∧ 1 ≤ F ∧
      ∀ (p : WattScales) (Δ : ℝ) (a bcoeff : ℕ → ℂ)
        (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ),
        (∀ i, 1 ≤ p.size i) → 0 < Δ → Δ ≤ 1 →
        WattWeightData b g p Δ a bcoeff u₀ u₁ γ →
        F*p.product^η ≤ p.X → p.H^2*p.C ≤ (p.R*p.S)^2 →
        (p.S*p.P/p.V)*p.product^η ≤ (p.R*p.S)^2 →
        ∀ positive : Bool,
          ‖weightedWattSum positive p a bcoeff u₀ u₁ γ‖ ≤ C*wattMajorant p Δ η

end
end DivisorProof
