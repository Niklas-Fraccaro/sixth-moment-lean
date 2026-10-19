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
import Sechstmoment.Arithmetic.QuadraticDivisor.Reduction.Ranges
import Std

/-! ## Large Mass

The small-shift condition is derived uniformly from the original admissibility
conditions.  Its threshold depends only on the fixed exponents and K.
-/
namespace DivisorProof
open MeasureTheory Set Finset Classical Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

def shiftGrowthExponent (ρ δ : ℝ) : ℝ := (1/2+ρ)/(1+δ)

theorem shiftGrowthExponent_pos {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    0 < shiftGrowthExponent ρ δ := by unfold shiftGrowthExponent; positivity

theorem shiftGrowthExponent_lt_half {ρ δ : ℝ} (hδ : 0 < δ) (hgap : 2*ρ < δ) :
    shiftGrowthExponent ρ δ < 1/2 := by
  unfold shiftGrowthExponent
  exact (div_lt_iff₀ (by linarith : 0 < 1+δ)).mpr (by linarith)

theorem admissible_AB_power {ρ δ K : ℝ} {bounds : ℕ → ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hadm : QuadraticAdmissible ρ δ K bounds q α β W) :
    (q.A*q.B)^(1+δ) ≤ K*q.mass := by
  obtain ⟨h,_,_,_,hsize,_⟩ := hadm
  have hAB := (product_AB_le_mass q h).1
  have hABp : 0 < q.A*q.B := by linarith
  calc (q.A*q.B)^(1+δ) = (q.A*q.B)*(q.A*q.B)^δ := by
        rw [Real.rpow_add hABp,Real.rpow_one]
    _ ≤ (q.A*q.B)*(K*q.M*q.N) := mul_le_mul_of_nonneg_left hsize hABp.le
    _ = K*q.mass := by dsimp [QuadraticScales.mass]; ring

theorem admissible_AB_le_mass_power {ρ δ K : ℝ} (hδ : 0 < δ) (hK : 1 ≤ K)
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hadm : QuadraticAdmissible ρ δ K bounds q α β W) :
    q.A*q.B ≤ (K*q.mass)^((1+δ)⁻¹) := by
  have h := hadm.1
  have hAB : 0 ≤ q.A*q.B := zero_le_one.trans (product_AB_le_mass q h).1
  have hQ : 0 ≤ q.mass := zero_le_one.trans (poisson_scale_bounds q h).1
  exact (Real.le_rpow_inv_iff_of_pos hAB (mul_nonneg (by linarith) hQ)
    (by linarith : 0 < 1+δ)).mpr (admissible_AB_power hadm)

theorem admissible_shift_growth {ρ δ K : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hK : 1 ≤ K)
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hadm : QuadraticAdmissible ρ δ K bounds q α β W) :
    q.H ≤ (K*K^(shiftGrowthExponent ρ δ))*q.mass^(shiftGrowthExponent ρ δ) := by
  have hcopy := hadm
  obtain ⟨h,_,_,hH,_⟩ := hcopy
  have hAB := (product_AB_le_mass q h).1
  have hQ := (poisson_scale_bounds q h).1
  have hKp : 0 < K := by linarith
  have hQp : 0 < q.mass := by linarith
  calc q.H ≤ K*(q.A*q.B)^(1/2+ρ) := hH
    _ ≤ K*((K*q.mass)^((1+δ)⁻¹))^(1/2+ρ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith)
        (admissible_AB_le_mass_power hδ hK hadm) (by linarith)) hKp.le
    _ = K*(K*q.mass)^(shiftGrowthExponent ρ δ) := by
      rw [← Real.rpow_mul (mul_pos hKp hQp).le]
      congr 2
      unfold shiftGrowthExponent
      ring
    _ = _ := by rw [Real.mul_rpow hKp.le hQp.le]; ring

theorem sqrt_mass_le_balanced_left {q : QuadraticScales}
    (h : ∀ j, 1 ≤ q.size j) {K : ℝ} (hK : 1 ≤ K)
    (hbal : q.B*q.N ≤ K*q.A*q.M) : Real.sqrt q.mass ≤ K*(q.A*q.M) := by
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
  have hM₁ : 0 < q.M₁ := lt_of_lt_of_le (by norm_num) (h 2)
  have hM₂ : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hu : 0 < q.A*q.M := by dsimp [QuadraticScales.M]; positivity
  have hKp : 0 < K := by linarith
  have hQp : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have hQle : q.mass ≤ K*(q.A*q.M)^2 := by
    rw [mass_eq_balanced_product]
    calc (q.A*q.M)*(q.B*q.N) ≤ (q.A*q.M)*(K*q.A*q.M) :=
        mul_le_mul_of_nonneg_left hbal hu.le
      _ = _ := by ring
  have hKK : K ≤ K^2 := by nlinarith
  have hsq : (Real.sqrt q.mass)^2 ≤ (K*(q.A*q.M))^2 := by
    rw [Real.sq_sqrt hQp.le,mul_pow]
    exact hQle.trans (mul_le_mul_of_nonneg_right hKK (sq_nonneg _))
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hKp.le hu.le)).mp hsq

/-- A single threshold works for all admissible data with the fixed parameters. -/
theorem admissible_eventually_small_shift {ρ δ K : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hgap : 2*ρ < δ) (hK : 1 ≤ K) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ (bounds : ℕ → ℝ) (q : QuadraticScales)
      (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
      QuadraticAdmissible ρ δ K bounds q α β W → Q₀ ≤ q.mass →
        2*q.H < q.A*q.M := by
  let θ := shiftGrowthExponent ρ δ
  have hθ : θ < 1/2 := shiftGrowthExponent_lt_half hδ hgap
  have hp : 0 < 1/2-θ := by linarith
  have hlim := (tendsto_rpow_atTop hp).eventually
    (eventually_gt_atTop (2*K^2*K^θ))
  obtain ⟨Q₁,hQ₁⟩ := eventually_atTop.mp hlim
  refine ⟨max Q₁ 1,le_max_right _ _,?_⟩
  intro bounds q α β W hadm hmass
  have hQ := (poisson_scale_bounds q hadm.1).1
  have hQp : 0 < q.mass := by linarith
  have hKp : 0 < K := by linarith
  have hbound : 2*K^2*K^θ < q.mass^(1/2-θ) :=
    hQ₁ q.mass ((le_max_left _ _).trans hmass)
  have hmul := mul_lt_mul_of_pos_right hbound (Real.rpow_pos_of_pos hQp θ)
  have hroot : 2*K^2*K^θ*q.mass^θ < Real.sqrt q.mass := by
    have hid : q.mass^(1/2-θ)*q.mass^θ = Real.sqrt q.mass := by
      rw [← Real.rpow_add hQp,sub_add_cancel,Real.sqrt_eq_rpow]
    rwa [hid] at hmul
  have hgrowth := admissible_shift_growth hρ hδ hK hadm
  change q.H ≤ (K*K^θ)*q.mass^θ at hgrowth
  have hbal : q.B*q.N ≤ K*q.A*q.M := hadm.2.2.2.2.2.2.1
  have hbalance := sqrt_mass_le_balanced_left hadm.1 hK hbal
  have hH : 2*K*q.H < K*(q.A*q.M) := by
    have hm := mul_le_mul_of_nonneg_left hgrowth (by positivity : 0 ≤ 2*K)
    nlinarith
  nlinarith

/-- The exact normal form applies to the original admissibility class after
the proved normalization, for all sufficiently large masses. -/
theorem admissible_normalized_finite_poisson_normal_form {ρ δ K : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hbound : ρ ≤ δ/(1000*(1+δ)))
    (hK : 1 ≤ K) (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ Q₀ C : ℝ, 1 ≤ Q₀ ∧ 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ), QuadraticAdmissible ρ δ K bounds q α β W →
      Q₀ ≤ q.mass → ∀ positive : Bool,
        ‖normalFormError positive q ρ
          (fun n => α n/((K*q.A^ρ : ℝ) : ℂ))
          (fun n => β n/((K*q.B^ρ : ℝ) : ℂ))
          (fun i x => q.mass^(-ρ)*W i x)‖ ≤ C*q.mass^(2*ρ)*q.H^2 := by
  obtain ⟨Q₀,hQ₀,hsmall⟩ := admissible_eventually_small_shift hρ hδ
    (rho_reserve hδ hρ hbound).2 hK
  obtain ⟨C,hC,hform⟩ := normalized_finite_poisson_normal_form hK hρ bounds hb
  refine ⟨Q₀,C,hQ₀,hC,?_⟩
  intro q α β W hadm hmass positive
  have hcopy := hadm
  obtain ⟨h,_,_,hH,_,hbal₁,hbal₂,_⟩ := hcopy
  exact hform q _ _ _ h (admissible_normalized_weight_data hK hadm)
    (shiftScale_le_mass q h (by linarith) (rho_lt_half hδ hbound).le hH)
    hbal₁ hbal₂ (hsmall bounds q α β W hadm hmass) positive

end
end DivisorProof



/-! ## Bounded Mass

A genuine uniform crude bound for the actual normalized discrepancy.  This
settles the bounded-mass range without using any divisor-sum estimate.
-/
namespace DivisorProof
open MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem quadraticIndexSet_card_le (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j) :
    ((quadraticIndexSet q).card : ℝ) ≤ 128*q.mass*q.H := by
  have hs (j : Fin 7) : 0 ≤ q.size j := zero_le_one.trans (h j)
  have hc : ((quadraticIndexSet q).card : ℝ) = ∏ j : Fin 7, (⌊2*q.size j⌋₊ : ℝ) := by
    simp only [quadraticIndexSet,Fintype.card_piFinset,Nat.card_Icc,
      Nat.add_sub_cancel,Nat.cast_prod]
  rw [hc]
  calc _ ≤ ∏ j : Fin 7, 2*q.size j :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun j _ => Nat.floor_le (mul_nonneg (by norm_num) (hs j)))
    _ = _ := by
      simp [QuadraticScales.size,QuadraticScales.mass,QuadraticScales.M,QuadraticScales.N,
        Fin.prod_univ_succ]
      ring

theorem quadraticSummand_norm_le {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hw : NormalizedWeightData bounds q α β W) (n : Fin 7 → ℕ) :
    ‖quadraticSummand q α β W n‖ ≤ (bounds 0)^5 := by
  change ‖quadraticPreWeight q α β W n*(W 4 (n 5/q.N₂) : ℂ)‖ ≤ _
  rw [norm_mul,Complex.norm_real]
  calc _ ≤ (bounds 0)^4*bounds 0 :=
      mul_le_mul (quadraticPreWeight_norm_le q α β W (hw.bounds_nonneg 0)
        hw.alpha_bound hw.beta_bound hw.weight_norm n) (hw.weight_norm 4 _)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem signedQuadraticSum_crude_bound {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ} (h : ∀ j, 1 ≤ q.size j)
    (hw : NormalizedWeightData bounds q α β W) (positive : Bool) :
    ‖signedQuadraticSum positive q α β W‖ ≤ 128*q.mass*q.H*(bounds 0)^5 := by
  have hb := hw.bounds_nonneg 0
  unfold signedQuadraticSum
  calc _ ≤ ∑ n ∈ quadraticIndexSet q,
        ‖if signedQuadraticRelation positive n then quadraticSummand q α β W n else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ quadraticIndexSet q, (bounds 0)^5 := by
      apply sum_le_sum
      intro n _
      split_ifs
      · exact quadraticSummand_norm_le hw n
      · simpa only [norm_zero] using pow_nonneg hb 5
    _ = ((quadraticIndexSet q).card : ℝ)*(bounds 0)^5 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (quadraticIndexSet_card_le q h) (pow_nonneg hb _)

theorem outer_zero_integral_bound {K : ℝ} (hK : 1 ≤ K) {bounds : ℕ → ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (hbal : q.A*q.M ≤ K*q.B*q.N) {n : Fin 5 → ℕ}
    (hn : n ∈ quadraticMainIndexSet q) (hne : poissonOuterWeight q α β W n ≠ 0) :
    ‖∫ x : ℝ in Ioi 0, outerPoissonProfile q W n x‖ ≤
      4*q.mass*profileFourierBound bounds (4*K) 0 := by
  obtain ⟨hX,hY,hY'⟩ := outer_products_bounds h hw hn hne
  have hdp : (0 : ℝ) < outerGCD n := by exact_mod_cast outerGCD_pos hn
  have hYp : (0 : ℝ) < outerRight n := by exact_mod_cast outerRight_pos hn
  have hM : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hr := poissonRadius_pos q h hdp
  obtain ⟨ha,hb,haK,hbK⟩ := normalized_poisson_slopes q h hK hdp
    (Nat.cast_nonneg (outerLeft n)) hX hY hY' hbal
  have hc := poissonCoefficient_decay (hw.smooth 2) (hw.smooth 4) hr ha hb haK hbK
    (fun j x => hw.derivatives j 2 x) (fun j x => hw.derivatives j 4 x) 0 0
  rw [poissonCoefficient_zero (hw.smooth 2) (div_pos hYp (mul_pos hdp hM))] at hc
  change ‖∫ x : ℝ in Ioi 0, outerPoissonProfile q W n x‖ ≤ _ at hc
  simp only [pow_zero,div_one] at hc
  have hdY : (outerGCD n : ℝ) ≤ (outerRight n : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (outerRight_pos hn)
      (Nat.gcd_dvd_right (outerLeft n) (outerRight n))
  exact hc.trans (mul_le_mul_of_nonneg_right (poissonRadius_upper q h (hdY.trans hY'))
    (profileFourierBound_nonneg hw.bounds_nonneg (by linarith) _))

theorem quadraticZeroMode_crude_bound {K : ℝ} (hK : 1 ≤ K) {bounds : ℕ → ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (hH : q.H ≤ K*q.mass) (hbal : q.A*q.M ≤ K*q.B*q.N) :
    ‖quadraticZeroMode q α β W‖ ≤
      128*K*(bounds 0)^3*profileFourierBound bounds (4*K) 0*q.mass^3 := by
  have hQp : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have hb := hw.bounds_nonneg 0
  have hC := profileFourierBound_nonneg hw.bounds_nonneg (by linarith : 0 ≤ 4*K) 0
  have hterm (n) (hn : n ∈ quadraticMainIndexSet q) :
      ‖quadraticZeroModeSummand q α β W n‖ ≤
        (bounds 0)^3*(4*q.mass*profileFourierBound bounds (4*K) 0) := by
    rw [zeroModeSummand_eq_outer,norm_mul]
    by_cases hz : poissonOuterWeight q α β W n = 0
    · simp only [hz,norm_zero,zero_mul]
      positivity
    · exact mul_le_mul (poissonOuterWeight_norm_le q α β W hb hw.alpha_bound hw.beta_bound
        hw.weight_norm n) (outer_zero_integral_bound hK h hw hbal hn hz) (norm_nonneg _) (by positivity)
  unfold quadraticZeroMode
  calc _ ≤ ∑ n ∈ quadraticMainIndexSet q, ‖quadraticZeroModeSummand q α β W n‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _n ∈ quadraticMainIndexSet q,
        (bounds 0)^3*(4*q.mass*profileFourierBound bounds (4*K) 0) := sum_le_sum hterm
    _ = ((quadraticMainIndexSet q).card : ℝ)*
        ((bounds 0)^3*(4*q.mass*profileFourierBound bounds (4*K) 0)) := by simp
    _ ≤ (32*K*q.mass^2)*((bounds 0)^3*(4*q.mass*profileFourierBound bounds (4*K) 0)) :=
      mul_le_mul_of_nonneg_right (quadraticMainIndexSet_card_le_mass_sq q h hH) (by positivity)
    _ = _ := by ring

def crudeDiscrepancyConstant (bounds : ℕ → ℝ) (K : ℝ) : ℝ :=
  128*K*((bounds 0)^5+(bounds 0)^3*profileFourierBound bounds (4*K) 0)

/-- An unconditional polynomial bound on the actual normalized discrepancy. -/
theorem normalized_discrepancy_crude_bound {K : ℝ} (hK : 1 ≤ K) {bounds : ℕ → ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (hH : q.H ≤ K*q.mass) (hbal : q.A*q.M ≤ K*q.B*q.N) (positive : Bool) :
    ‖signedQuadraticDiscrepancy positive q α β W‖ ≤ crudeDiscrepancyConstant bounds K*q.mass^3 := by
  have hQ := (poisson_scale_bounds q h).1
  have hQp : 0 < q.mass := by linarith
  have hb := hw.bounds_nonneg 0
  have hKp : 0 ≤ K := by linarith
  have hS := signedQuadraticSum_crude_bound h hw positive
  have hZ := quadraticZeroMode_crude_bound hK h hw hH hbal
  have hS' : 128*q.mass*q.H*(bounds 0)^5 ≤ 128*K*(bounds 0)^5*q.mass^3 := by
    calc _ ≤ 128*q.mass*(K*q.mass)*(bounds 0)^5 := by gcongr
      _ = 128*K*(bounds 0)^5*q.mass^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hQ (by norm_num : 2 ≤ 3)) (by positivity)
  unfold signedQuadraticDiscrepancy
  calc _ ≤ ‖signedQuadraticSum positive q α β W‖+‖quadraticZeroMode q α β W‖ := norm_sub_le _ _
    _ ≤ 128*K*(bounds 0)^5*q.mass^3+
      128*K*(bounds 0)^3*profileFourierBound bounds (4*K) 0*q.mass^3 :=
        add_le_add (hS.trans hS') hZ
    _ = _ := by unfold crudeDiscrepancyConstant; ring

/-- A fixed bounded mass range is uniformly absorbed, with an explicit constant. -/
theorem normalized_discrepancy_bounded_mass {K Q₀ : ℝ} (hK : 1 ≤ K) (_hQ₀ : 1 ≤ Q₀)
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (hH : q.H ≤ K*q.mass) (hbal : q.A*q.M ≤ K*q.B*q.N)
    (hmass : q.mass ≤ Q₀) (positive : Bool) :
    ‖signedQuadraticDiscrepancy positive q α β W‖ ≤ crudeDiscrepancyConstant bounds K*Q₀^3 := by
  have hb := hw.bounds_nonneg 0
  have hC := profileFourierBound_nonneg hw.bounds_nonneg (by linarith : 0 ≤ 4*K) 0
  apply (normalized_discrepancy_crude_bound hK h hw hH hbal positive).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (zero_le_one.trans (poisson_scale_bounds q h).1) hmass _) (by
      unfold crudeDiscrepancyConstant
      positivity)

end
end DivisorProof



/-! ## Normal Form Scaling

Exact multilinearity of the actual finite normal form, followed by its return
to the original, unnormalized coefficients and weights.
-/
namespace DivisorProof
open MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

theorem poissonOuterWeight_scale (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) (cα cβ : ℂ) (cW : ℝ) (n : Fin 5 → ℕ) :
    poissonOuterWeight q (fun m => cα*α m) (fun m => cβ*β m)
      (fun i x => cW*W i x) n =
        (cα*cβ*(cW : ℂ)^3)*poissonOuterWeight q α β W n := by
  simp only [poissonOuterWeight,Complex.ofReal_mul]
  ring

theorem outerPoissonProfile_scale (q : QuadraticScales) (W : Fin 5 → ℝ → ℝ)
    (cW : ℝ) (n : Fin 5 → ℕ) (x : ℝ) :
    outerPoissonProfile q (fun i y => cW*W i y) n x =
      (cW : ℂ)^2*outerPoissonProfile q W n x := by
  simp only [outerPoissonProfile,poissonProfile,Complex.ofReal_mul]
  ring

theorem outerFourierIntegrand_scale (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (W : Fin 5 → ℝ → ℝ) (cW : ℝ) (n : Fin 5 → ℕ) (x : ℝ) :
    outerFourierIntegrand positive q ρ (fun i y => cW*W i y) n x =
      (cW : ℂ)^2*outerFourierIntegrand positive q ρ W n x := by
  simp only [outerFourierIntegrand,outerPoissonProfile_scale,mul_assoc]

theorem gcdBlockIntegrand_scale (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (cα cβ : ℂ) (cW : ℝ) (d : ℕ) (x : ℝ) :
    gcdBlockIntegrand positive q ρ (fun m => cα*α m) (fun m => cβ*β m)
      (fun i y => cW*W i y) d x =
        (cα*cβ*(cW : ℂ)^5)*gcdBlockIntegrand positive q ρ α β W d x := by
  unfold gcdBlockIntegrand
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro n _
  rw [poissonOuterWeight_scale,outerFourierIntegrand_scale]
  ring

theorem normalFormError_scale (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (cα cβ : ℂ) (cW : ℝ) :
    normalFormError positive q ρ (fun m => cα*α m) (fun m => cβ*β m)
      (fun i y => cW*W i y) =
        (cα*cβ*(cW : ℂ)^5)*normalFormError positive q ρ α β W := by
  unfold normalFormError
  simp_rw [gcdBlockIntegrand_scale,integral_const_mul]
  rw [signedQuadraticDiscrepancy_scale,← Finset.mul_sum,mul_sub]

theorem normalFormError_normalize (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) {cα cβ : ℂ} {cW : ℝ}
    (hα : cα ≠ 0) (hβ : cβ ≠ 0) (hW : cW ≠ 0) :
    normalFormError positive q ρ α β W =
      (cα*cβ*(cW : ℂ)^5)*normalFormError positive q ρ
        (fun n => α n/cα) (fun n => β n/cβ) (fun i x => W i x/cW) := by
  rw [← normalFormError_scale]
  have hα' : (fun n => cα*(α n/cα)) = α := by
    funext n
    field_simp
  have hβ' : (fun n => cβ*(β n/cβ)) = β := by
    funext n
    field_simp
  have hW' : (fun i x => cW*(W i x/cW)) = W := by
    funext i x
    field_simp
  rw [hα',hβ',hW']

theorem normalFormError_pdf_normalization_identity (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) {K ρ : ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hK : 1 ≤ K) :
    normalFormError positive q ρ α β W =
      ((K^2*(q.A*q.B)^ρ*q.mass^(5*ρ) : ℝ) : ℂ) *
      normalFormError positive q ρ
        (fun n => α n / ((K*q.A^ρ : ℝ) : ℂ))
        (fun n => β n / ((K*q.B^ρ : ℝ) : ℂ))
        (fun i x => q.mass^(-ρ)*W i x) := by
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  obtain ⟨hAB, hABQ⟩ := product_AB_le_mass q h
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (hAB.trans hABQ)
  have hKp : 0 < K := by linarith
  have hα : ((K*q.A^ρ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos hKp (Real.rpow_pos_of_pos hA ρ)).ne'
  have hβ : ((K*q.B^ρ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos hKp (Real.rpow_pos_of_pos hB ρ)).ne'
  have he := normalFormError_normalize positive q ρ α β W hα hβ
    (Real.rpow_pos_of_pos hQ ρ).ne'
  have hw : (fun i x => W i x/q.mass^ρ) = (fun i x => q.mass^(-ρ)*W i x) := by
    funext i x
    rw [Real.rpow_neg hQ.le]
    ring
  have hf : ((K*q.A^ρ : ℝ) : ℂ)*((K*q.B^ρ : ℝ) : ℂ)*((q.mass^ρ : ℝ) : ℂ)^5 =
      ((K^2*(q.A*q.B)^ρ*q.mass^(5*ρ) : ℝ) : ℂ) := by
    exact_mod_cast normalization_scalar_identity (K := K) (ρ := ρ) hA.le hB.le hQ.le
  rw [hw, hf] at he
  exact he


end
end DivisorProof



/-! ## Actual Normal Form

The complete finite Poisson reduction for the original input data.  The
bounded-mass range is also proved directly for the original discrepancy.
-/
namespace DivisorProof
open MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000

/-- Equation (22) returned to the original weights: the total error costs `8ρ`. -/
theorem admissible_actual_finite_poisson_normal_form {ρ δ K : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hbound : ρ ≤ δ/(1000*(1+δ)))
    (hK : 1 ≤ K) (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ Q₀ C : ℝ, 1 ≤ Q₀ ∧ 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ), QuadraticAdmissible ρ δ K bounds q α β W →
      Q₀ ≤ q.mass → ∀ positive : Bool,
        ‖normalFormError positive q ρ α β W‖ ≤ C*q.mass^(8*ρ)*q.H^2 := by
  obtain ⟨Q₀,C,hQ₀,hC,hform⟩ := admissible_normalized_finite_poisson_normal_form
    hρ hδ hbound hK bounds hb
  refine ⟨Q₀,K^2*C,hQ₀,mul_nonneg (sq_nonneg _) hC,?_⟩
  intro q α β W hadm hmass positive
  have h := hadm.1
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have hAB : 0 < q.A*q.B := lt_of_lt_of_le (by norm_num) (product_AB_le_mass q h).1
  have hfac : 0 ≤ K^2*(q.A*q.B)^ρ*q.mass^(5*ρ) := by positivity
  have he := hform q α β W hadm hmass positive
  rw [normalFormError_pdf_normalization_identity positive q α β W h hK,
    norm_mul,Complex.norm_real,Real.norm_of_nonneg hfac]
  calc _ ≤ (K^2*(q.A*q.B)^ρ*q.mass^(5*ρ))*(C*q.mass^(2*ρ)*q.H^2) :=
      mul_le_mul_of_nonneg_left he hfac
    _ ≤ (K^2*(q.mass^ρ)^6)*(C*q.mass^(2*ρ)*q.H^2) :=
      mul_le_mul_of_nonneg_right (normalization_factor_le q h hρ.le) (by positivity)
    _ = (K^2*C)*((q.mass^ρ)^6*q.mass^(2*ρ))*q.H^2 := by ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hQ.le,← Real.rpow_add hQ]
      congr 3
      norm_num
      ring

theorem crudeDiscrepancyConstant_nonneg {bounds : ℕ → ℝ} {K : ℝ}
    (hb : ∀ j, 0 ≤ bounds j) (hK : 0 ≤ K) : 0 ≤ crudeDiscrepancyConstant bounds K := by
  have hb₀ := hb 0
  have hC := profileFourierBound_nonneg hb (by positivity : 0 ≤ 4*K) 0
  unfold crudeDiscrepancyConstant
  positivity

def boundedMassConstant (bounds : ℕ → ℝ) (K ρ Q₀ : ℝ) : ℝ :=
  (K^2*(Q₀^ρ)^6)*(crudeDiscrepancyConstant bounds K*Q₀^3)

theorem boundedMassConstant_nonneg {bounds : ℕ → ℝ} {K ρ Q₀ : ℝ}
    (hb : ∀ j, 0 ≤ bounds j) (hK : 0 ≤ K) (hQ₀ : 0 ≤ Q₀) :
    0 ≤ boundedMassConstant bounds K ρ Q₀ := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (Real.rpow_nonneg hQ₀ _) _))
    (mul_nonneg (crudeDiscrepancyConstant_nonneg hb hK) (pow_nonneg hQ₀ _))

/-- The bounded-mass estimate for the actual unnormalized source discrepancy. -/
theorem admissible_bounded_mass_discrepancy {ρ δ K Q₀ : ℝ}
    (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hK : 1 ≤ K) (hQ₀ : 1 ≤ Q₀)
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hadm : QuadraticAdmissible ρ δ K bounds q α β W) (hmass : q.mass ≤ Q₀)
    (positive : Bool) :
    ‖signedQuadraticDiscrepancy positive q α β W‖ ≤ boundedMassConstant bounds K ρ Q₀ := by
  have hw := admissible_normalized_weight_data hK hadm
  have h := hadm.1
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have hAB : 0 < q.A*q.B := lt_of_lt_of_le (by norm_num) (product_AB_le_mass q h).1
  have hH : q.H ≤ K*q.mass := shiftScale_le_mass q h (by linarith) hρhalf hadm.2.2.2.1
  have hbal : q.A*q.M ≤ K*q.B*q.N := hadm.2.2.2.2.2.1
  have hb := hw.bounds_nonneg
  have hC : 0 ≤ crudeDiscrepancyConstant bounds K := crudeDiscrepancyConstant_nonneg hb (by linarith)
  have hfactor : 0 ≤ K^2*(q.A*q.B)^ρ*q.mass^(5*ρ) := by positivity
  have herror := normalized_discrepancy_bounded_mass hK hQ₀ h hw hH hbal hmass positive
  rw [pdf_normalization_identity positive q α β W h hK,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg hfactor]
  calc _ ≤ (K^2*(q.A*q.B)^ρ*q.mass^(5*ρ))*(crudeDiscrepancyConstant bounds K*Q₀^3) :=
      mul_le_mul_of_nonneg_left herror hfactor
    _ ≤ (K^2*(q.mass^ρ)^6)*(crudeDiscrepancyConstant bounds K*Q₀^3) :=
      mul_le_mul_of_nonneg_right (normalization_factor_le q h hρ.le) (by positivity)
    _ ≤ (K^2*(Q₀^ρ)^6)*(crudeDiscrepancyConstant bounds K*Q₀^3) := by gcongr
    _ = _ := rfl

/-- The bounded range already has exactly the target shape of (9), without
assuming the still-open large-mass divisor bound. -/
theorem admissible_bounded_mass_target {ρ δ K Q₀ : ℝ}
    (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hK : 1 ≤ K) (hQ₀ : 1 ≤ Q₀)
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hadm : QuadraticAdmissible ρ δ K bounds q α β W) (hmass : q.mass ≤ Q₀)
    (positive : Bool) :
    ‖signedQuadraticDiscrepancy positive q α β W‖ ≤
      boundedMassConstant bounds K ρ Q₀*q.mass^(1000*ρ)*(orientedQuadraticMajorant q+q.H^2) := by
  have h := hadm.1
  have hQ := (poisson_scale_bounds q h).1
  have hH : 1 ≤ q.H := h 6
  have hA : 0 ≤ q.A := zero_le_one.trans (h 0)
  have hB : 0 ≤ q.B := zero_le_one.trans (h 1)
  have hE := orientedMajorant_nonneg q hA hB (zero_le_one.trans hQ) (zero_le_one.trans hH)
  have hw := admissible_normalized_weight_data hK hadm
  have hC := boundedMassConstant_nonneg (ρ := ρ) hw.bounds_nonneg
    (by linarith : 0 ≤ K) (by linarith : 0 ≤ Q₀)
  apply (admissible_bounded_mass_discrepancy hρ hρhalf hK hQ₀ hadm hmass positive).trans
  calc boundedMassConstant bounds K ρ Q₀ ≤ boundedMassConstant bounds K ρ Q₀*q.mass^(1000*ρ) :=
      le_mul_of_one_le_right hC (Real.one_le_rpow hQ (by linarith))
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (by nlinarith [one_le_pow₀ hH (n := 2)])

end
end DivisorProof
