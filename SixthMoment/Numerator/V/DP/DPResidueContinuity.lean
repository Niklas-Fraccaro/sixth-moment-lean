import Mathlib.MeasureTheory.Integral.DominatedConvergence
import SixthMoment.Numerator.V.DP.DPNormalization

namespace SixthMoment.Source
open Complex Set
open scoped Topology

set_option maxHeartbeats 1000000

theorem dpNormalizedTriple_continuous_joint (P : Polynomial ℝ) :
    Continuous (fun p : ℝ × (Fin 3 → ℂ) =>
      dpNormalizedTriple p.1 P (p.2 0) (p.2 1) (p.2 2)) := by
  unfold dpNormalizedTriple
  fun_prop

theorem dpNormalizedTriple_continuous_shifts (η : ℝ) (P : Polynomial ℝ)
    {X : Type*} [TopologicalSpace X] (β γ δ : X → ℂ)
    (hβ : Continuous β) (hγ : Continuous γ) (hδ : Continuous δ) :
    Continuous (fun p => dpNormalizedTriple η P (β p) (γ p) (δ p)) := by
  unfold dpNormalizedTriple
  fun_prop

theorem dpSeparated_denominators {σ : MomentShifts} (hσ : DPSeparated σ) :
    (σ 1-σ 0)*(σ 0+σ 2)*(σ 0+σ 3) ≠ 0 ∧
    (σ 0-σ 1)*(σ 1+σ 2)*(σ 1+σ 3) ≠ 0 ∧
    (σ 1+σ 2)*(σ 0+σ 2)*(σ 2-σ 3) ≠ 0 ∧
    (σ 1+σ 3)*(σ 3-σ 2)*(σ 0+σ 3) ≠ 0 := by
  have h01 := hσ.ne (show (0 : Fin 4) ≠ 1 by decide)
  have h02 := hσ.ne (show (0 : Fin 4) ≠ 2 by decide)
  have h03 := hσ.ne (show (0 : Fin 4) ≠ 3 by decide)
  have h12 := hσ.ne (show (1 : Fin 4) ≠ 2 by decide)
  have h13 := hσ.ne (show (1 : Fin 4) ≠ 3 by decide)
  have h23 := hσ.ne (show (2 : Fin 4) ≠ 3 by decide)
  change -σ 0 ≠ -σ 1 at h01
  change -σ 0 ≠ σ 2 at h02
  change -σ 0 ≠ σ 3 at h03
  change -σ 1 ≠ σ 2 at h12
  change -σ 1 ≠ σ 3 at h13
  change σ 2 ≠ σ 3 at h23
  have hσ01 : σ 0 ≠ σ 1 := fun h => h01 (congrArg Neg.neg h)
  have hσ02 : σ 0+σ 2 ≠ 0 := by
    intro h
    apply h02
    linear_combination -h
  have hσ03 : σ 0+σ 3 ≠ 0 := by
    intro h
    apply h03
    linear_combination -h
  have hσ12 : σ 1+σ 2 ≠ 0 := by
    intro h
    apply h12
    linear_combination -h
  have hσ13 : σ 1+σ 3 ≠ 0 := by
    intro h
    apply h13
    linear_combination -h
  exact ⟨mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hσ01.symm) hσ02) hσ03,
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hσ01) hσ12) hσ13,
    mul_ne_zero (mul_ne_zero hσ12 hσ02) (sub_ne_zero.mpr h23),
    mul_ne_zero (mul_ne_zero hσ13 (sub_ne_zero.mpr h23.symm)) hσ03⟩

theorem dpNormalizedFourResidues_continuousOn_joint (η : ℝ) (P : Polynomial ℝ) :
    ContinuousOn (fun p : ℝ × MomentShifts => dpNormalizedFourResidues p.1 η P p.2)
      {p | DPSeparated p.2} := by
  have ht1 : Continuous (fun p : ℝ × MomentShifts =>
      dpNormalizedTriple η P (p.2 1) (p.2 2) (p.2 3)) :=
    dpNormalizedTriple_continuous_shifts η P _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  have ht0 : Continuous (fun p : ℝ × MomentShifts =>
      dpNormalizedTriple η P (p.2 0) (p.2 2) (p.2 3)) :=
    dpNormalizedTriple_continuous_shifts η P _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  have ht2 : Continuous (fun p : ℝ × MomentShifts =>
      dpNormalizedTriple η P (p.2 1) (-p.2 0) (p.2 3)) :=
    dpNormalizedTriple_continuous_shifts η P _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  have ht3 : Continuous (fun p : ℝ × MomentShifts =>
      dpNormalizedTriple η P (p.2 1) (p.2 2) (-p.2 0)) :=
    dpNormalizedTriple_continuous_shifts η P _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  have hn1 : Continuous (fun p : ℝ × MomentShifts =>
      Complex.exp ((p.1:ℂ)*(-p.2 0-p.2 2-p.2 3)) *
        (dpNormalizedTriple η P (p.2 1) (p.2 2) (p.2 3))^2) := by fun_prop
  have hn0 : Continuous (fun p : ℝ × MomentShifts =>
      Complex.exp ((p.1:ℂ)*(-p.2 1-p.2 2-p.2 3)) *
        (dpNormalizedTriple η P (p.2 0) (p.2 2) (p.2 3))^2) := by fun_prop
  have hn2 : Continuous (fun p : ℝ × MomentShifts =>
      Complex.exp ((p.1:ℂ)*(-p.2 3)) *
        (dpNormalizedTriple η P (p.2 1) (-p.2 0) (p.2 3))^2) := by fun_prop
  have hn3 : Continuous (fun p : ℝ × MomentShifts =>
      Complex.exp ((p.1:ℂ)*(-p.2 2)) *
        (dpNormalizedTriple η P (p.2 1) (p.2 2) (-p.2 0))^2) := by fun_prop
  unfold dpNormalizedFourResidues
  exact (((hn1.continuousOn.div (by fun_prop) (fun p hp => (dpSeparated_denominators hp).1)).add
    (hn0.continuousOn.div (by fun_prop) (fun p hp => (dpSeparated_denominators hp).2.1))).add
    (hn2.continuousOn.div (by fun_prop) (fun p hp => (dpSeparated_denominators hp).2.2.1))).add
    (hn3.continuousOn.div (by fun_prop) (fun p hp => (dpSeparated_denominators hp).2.2.2))

end SixthMoment.Source
