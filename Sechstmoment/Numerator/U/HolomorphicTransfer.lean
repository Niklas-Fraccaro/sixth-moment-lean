import Mathlib.Analysis.Complex.LocallyUniformLimit
import Sechstmoment.Numerator.U.MainTerm.HolomorphicDerivativeTransfer
import Sechstmoment.Numerator.U.PolynomialMoment

/-!
# Holomorphic limits and exact normalization of the actual U numerator

This module transfers an explicitly supplied uniform disk limit to all
ordinary derivatives and then to the literal finite polynomial operator.
The limit is an arbitrary function `H`; no identification with a manuscript
generator or its profile integral is assumed or claimed.
-/

namespace Sechstmoment
open Complex Metric Set Filter Polynomial
open scoped Topology BigOperators
noncomputable section

set_option maxHeartbeats 2000000

/-- Uniform convergence on a fixed positive disk of a holomorphic family
implies convergence of every ordinary derivative at its center. The
holomorphy of the limit follows from Weierstrass and is not an extra input. -/
theorem holomorphic_uniform_disk_iteratedDeriv_zero_limit
    (r : ℝ) (hr : 0 < r) (F : ℝ → ℂ → ℂ) (H : ℂ → ℂ)
    (hF : ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ (F T) (closedBall (0:ℂ) (2*r)))
    (hlimit : TendstoUniformlyOn F H atTop (closedBall (0:ℂ) r)) (n : ℕ) :
    Tendsto (fun T => iteratedDeriv n (F T) 0) atTop (𝓝 (iteratedDeriv n H 0)) := by
  have hsub : ball (0:ℂ) r ⊆ closedBall (0:ℂ) (2*r) := by
    intro z hz
    have hh : ‖z‖ < r := by simpa only [mem_ball, dist_zero_right] using hz
    simp only [mem_closedBall, dist_zero_right]
    linarith
  have hlocal : TendstoLocallyUniformlyOn F H atTop (ball (0:ℂ) r) :=
    hlimit.tendstoLocallyUniformlyOn.mono ball_subset_closedBall
  have hhol : ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ (F T) (ball (0:ℂ) r) := by
    filter_upwards [hF] with T hT
    exact hT.mono hsub
  have aux : ∀ k : ℕ,
      TendstoLocallyUniformlyOn (fun T => iteratedDeriv k (F T)) (iteratedDeriv k H)
        atTop (ball (0:ℂ) r) ∧
      ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ (iteratedDeriv k (F T)) (ball (0:ℂ) r) := by
    intro k
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using And.intro hlocal hhol
    | succ k ih =>
      constructor
      · simpa only [iteratedDeriv_succ, Function.comp_def] using ih.1.deriv ih.2 isOpen_ball
      · filter_upwards [ih.2] with T hT
        simpa only [iteratedDeriv_succ] using hT.deriv isOpen_ball
  exact (aux n).1.tendsto_at (mem_ball_self hr)

/-- Every finite ordinary differential operator has the corresponding
limit under the same fixed disk hypotheses. -/
theorem holomorphic_uniform_disk_finiteDifferentialOperator_limit
    (r : ℝ) (hr : 0 < r) (F : ℝ → ℂ → ℂ) (H : ℂ → ℂ)
    (hF : ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ (F T) (closedBall (0:ℂ) (2*r)))
    (hlimit : TendstoUniformlyOn F H atTop (closedBall (0:ℂ) r))
    (N : ℕ) (q : Fin (N+1) → ℂ) :
    Tendsto (fun T => finiteDifferentialOperator N q (F T) 0)
      atTop (𝓝 (finiteDifferentialOperator N q H 0)) := by
  unfold finiteDifferentialOperator
  exact tendsto_finsetSum Finset.univ (fun j _ => tendsto_const_nhds.mul
    (holomorphic_uniform_disk_iteratedDeriv_zero_limit r hr F H hF hlimit j.val))

/-- Constant division commutes exactly with the finite differential operator,
including at zero normalization in Lean's total field convention. -/
theorem finiteDifferentialOperator_div_const (N : ℕ) (q : Fin (N+1) → ℂ)
    (F : ℂ → ℂ) (d z : ℂ) :
    finiteDifferentialOperator N q (fun w => F w/d) z =
      finiteDifferentialOperator N q F z/d := by
  unfold finiteDifferentialOperator
  simp only [div_eq_mul_inv, iteratedDeriv_mul_const_field, Finset.sum_mul, mul_assoc]

/-- The actual mixed U generator with the literal moment normalization. -/
def uPolynomialNormalizedMixedGenerator (T : ℝ) (f g Φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  uPolynomialMixedGenerator T f g Φ z / ((T:ℂ)*(Real.log T:ℂ)^9)

/-- The actual normalization preserves the exact centering and amplifier
orientation: the source moment uses the swapped profiles `g,f`. -/
theorem uPolynomialNormalizedMixedGenerator_eq_centered_twistedFourthMoment
    (T : ℝ) (f g Φ : ℝ → ℝ) (z : ℂ) :
    uPolynomialNormalizedMixedGenerator T f g Φ z =
      Complex.exp (z/2) *
        (twistedFourthMoment T (rawMomentShifts T (uBBLRShifts z)) g f Φ /
          ((T:ℂ)*(Real.log T:ℂ)^9)) := by
  unfold uPolynomialNormalizedMixedGenerator
  rw [uPolynomialMixedGenerator_eq_twistedFourthMoment]
  ring

/-- The needed holomorphy of the normalized actual generator follows from
the already proved compact-integral holomorphy, for every fixed `r<2`. -/
theorem uPolynomialNormalizedMixedGenerator_eventually_differentiableOn_disk
    (r : ℝ) (hr : r<2) (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a<x → f x=0) (hg : ∀ x, b<x → g x=0) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ
      (uPolynomialNormalizedMixedGenerator T f g Φ) (closedBall (0:ℂ) (2*r)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  have hsub : closedBall (0:ℂ) (2*r) ⊆ ball (0:ℂ) 4 := by
    intro z hz
    have hh : ‖z‖ ≤ 2*r := by simpa only [mem_closedBall, dist_zero_right] using hz
    simp only [mem_ball, dist_zero_right]
    linarith
  exact ((uPolynomialMixedGenerator_differentiableOn hT hL a b f g Φ hf hg hΦ).mono hsub).div_const _

/-- The normalized raw U moment is exactly the same finite differential
operator on the normalized genuine generator. -/
theorem uPolynomialRawMixedMoment_normalized_eq_finiteDifferentialOperator
    (N : ℕ) {T : ℝ} (hT : 1<T) (hL : 16<Real.log T)
    (a b : ℝ) (p : ℝ[X]) (hp : p.natDegree≤N) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a<x → f x=0) (hg : ∀ x, b<x → g x=0) (hΦ : SmoothDyadicWeight Φ) :
    uPolynomialRawMixedMoment T p f g Φ / ((T:ℂ)*(Real.log T:ℂ)^9) =
      finiteDifferentialOperator N (fun j => (p.coeff j.val:ℂ))
        (uPolynomialNormalizedMixedGenerator T f g Φ) 0 := by
  rw [uPolynomialRawMixedMoment_eq_finiteDifferentialOperator N hT hL a b p hp f g Φ hf hg hΦ]
  exact (finiteDifferentialOperator_div_const N (fun j => (p.coeff j.val:ℂ))
    (uPolynomialMixedGenerator T f g Φ) ((T:ℂ)*(Real.log T:ℂ)^9) 0).symm

/-- Once a uniform limit of the normalized actual U generator is supplied,
all its ordinary derivatives through degree four have the expected limit. -/
theorem uPolynomialNormalizedMixedGenerator_derivatives_zero_through_four
    (r : ℝ) (hr : 0<r) (f g Φ : ℝ → ℝ) (H : ℂ → ℂ)
    (hhol : ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ
      (uPolynomialNormalizedMixedGenerator T f g Φ) (closedBall (0:ℂ) (2*r)))
    (hlimit : TendstoUniformlyOn (fun T => uPolynomialNormalizedMixedGenerator T f g Φ)
      H atTop (closedBall (0:ℂ) r)) :
    ∀ n ≤ 4, Tendsto (fun T => iteratedDeriv n (uPolynomialNormalizedMixedGenerator T f g Φ) 0)
      atTop (𝓝 (iteratedDeriv n H 0)) := by
  intro n _
  exact holomorphic_uniform_disk_iteratedDeriv_zero_limit r hr
    (fun T => uPolynomialNormalizedMixedGenerator T f g Φ) H hhol hlimit n

/-- A supplied generator disk limit gives the normalized literal U numerator
limit for any polynomial of degree at most four. -/
theorem uPolynomialRawMixedMoment_normalized_limit_of_uniform_generator_limit
    (r : ℝ) (hr : 0<r) (a b : ℝ) (p : ℝ[X]) (hp : p.natDegree≤4)
    (f g Φ : ℝ → ℝ) (hf : ∀ x, a<x → f x=0) (hg : ∀ x, b<x → g x=0)
    (hΦ : SmoothDyadicWeight Φ) (H : ℂ → ℂ)
    (hhol : ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ
      (uPolynomialNormalizedMixedGenerator T f g Φ) (closedBall (0:ℂ) (2*r)))
    (hlimit : TendstoUniformlyOn (fun T => uPolynomialNormalizedMixedGenerator T f g Φ)
      H atTop (closedBall (0:ℂ) r)) :
    Tendsto (fun T => uPolynomialRawMixedMoment T p f g Φ / ((T:ℂ)*(Real.log T:ℂ)^9))
      atTop (𝓝 (finiteDifferentialOperator 4 (fun j => (p.coeff j.val:ℂ)) H 0)) := by
  have hoperator := holomorphic_uniform_disk_finiteDifferentialOperator_limit r hr
    (fun T => uPolynomialNormalizedMixedGenerator T f g Φ) H hhol hlimit 4
    (fun j => (p.coeff j.val:ℂ))
  apply hoperator.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  exact (uPolynomialRawMixedMoment_normalized_eq_finiteDifferentialOperator 4 hT hL
    a b p hp f g Φ hf hg hΦ).symm

/-- For the actual compact U generator, a supplied uniform disk limit is
the only remaining analytic input: its holomorphy and literal polynomial
moment identification have already been proved independently. -/
theorem uPolynomialRawMixedMoment_normalized_limit_of_uniform_disk_limit
    (r : ℝ) (hr : 0<r) (hrsmall : r<2) (a b : ℝ) (p : ℝ[X]) (hp : p.natDegree≤4)
    (f g Φ : ℝ → ℝ) (hf : ∀ x, a<x → f x=0) (hg : ∀ x, b<x → g x=0)
    (hΦ : SmoothDyadicWeight Φ) (H : ℂ → ℂ)
    (hlimit : TendstoUniformlyOn (fun T => uPolynomialNormalizedMixedGenerator T f g Φ)
      H atTop (closedBall (0:ℂ) r)) :
    Tendsto (fun T => uPolynomialRawMixedMoment T p f g Φ / ((T:ℂ)*(Real.log T:ℂ)^9))
      atTop (𝓝 (finiteDifferentialOperator 4 (fun j => (p.coeff j.val:ℂ)) H 0)) :=
  uPolynomialRawMixedMoment_normalized_limit_of_uniform_generator_limit r hr a b p hp f g Φ
    hf hg hΦ H (uPolynomialNormalizedMixedGenerator_eventually_differentiableOn_disk
      r hrsmall a b f g Φ hf hg hΦ) hlimit

end
end Sechstmoment
