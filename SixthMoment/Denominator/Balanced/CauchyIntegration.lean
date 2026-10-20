import SixthMoment.Denominator.Balanced.CircleIntegral
import SixthMoment.Denominator.Balanced.DiagonalKernelLimit


namespace SixthMoment
open MeasureTheory Set Complex Polynomial
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

theorem d02PolynomialCircle_continuous_parameter {A : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] [LocallyCompactSpace A]
    (p : ℝ[X]) (F : A → ℂ → ℂ) (hF : Continuous (Function.uncurry F)) :
    Continuous (fun a => d02PolynomialCircle p (F a)) := by
  unfold d02PolynomialCircle Polynomial.sum
  apply continuous_finsetSum
  intro m hm
  exact continuous_const.mul (d02CircleExtract_continuous_parameter m F hF)

theorem d02PolynomialCircle_two_setIntegral (p q : ℝ[X]) (E : Set D01EdgeSpace)
    (hE : IsCompact E) (F : ℂ → ℂ → D01EdgeSpace → ℂ)
    (hF : Continuous (fun y : ℂ × (ℂ × D01EdgeSpace) => F y.1 y.2.1 y.2.2)) :
    d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => ∫ x in E, F z w x)) =
      ∫ x in E, d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w => F z w x)) := by
  have hinner (z : ℂ) : Continuous (Function.uncurry (F z)) :=
    hF.comp (by fun_prop : Continuous (fun y : ℂ × D01EdgeSpace => (z,y)))
  simp_rw [d02PolynomialCircle_setIntegral q E hE _ (hinner _)]
  apply d02PolynomialCircle_setIntegral p E hE
  apply d02PolynomialCircle_continuous_parameter q
  exact hF.comp (by fun_prop : Continuous
    (fun y : (ℂ × D01EdgeSpace) × ℂ => (y.1.1,(y.2,y.1.2))))

def d02BalancedShiftedEdgeIntegral (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) : ℂ :=
  ∫ x : D01EdgeSpace,
    d02BalancedWeightedEdgeIntegrand ρ (d02BalancedLogExponentialWeight σ) x

theorem d02BalancedCauchyPolynomialWeight (p q : ℝ[X])
    (hp : p.natDegree≤4) (hq : q.natDegree≤4) (y : D01LogSpace) :
    d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
      d02BalancedLogExponentialWeight ![z,w] y)) =
      d02BalancedLogPolynomialWeight (fun i => p.coeff i.val) (fun i => q.coeff i.val) y := by
  rw [d02BalancedCircleWeight_extract]
  unfold d02BalancedLogPolynomialWeight
  simp_rw [d02_evalDegreeFour_coeff p hp, d02_evalDegreeFour_coeff q hq]

theorem d02BalancedWeightedPolynomialEdgeIntegrand (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (x : D01EdgeSpace) :
    d02BalancedWeightedEdgeIntegrand ρ (d02BalancedLogPolynomialWeight p q) x =
      (d02BalancedEdgeIntegrand p q ρ x : ℂ) := by
  by_cases hx : x∈d02BalancedEdgeCut
  · simp only [d02BalancedWeightedEdgeIntegrand, d02BalancedEdgeIntegrand,
      indicator_of_mem hx, d02BalancedLogPolynomialWeight, d02BalancedEdgePolynomial]
    push_cast
    rfl
  · simp [d02BalancedWeightedEdgeIntegrand, d02BalancedEdgeIntegrand, hx]

theorem d02BalancedCauchy_edgeIntegral (p q : ℝ[X])
    (hp : p.natDegree≤4) (hq : q.natDegree≤4)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
      d02BalancedShiftedEdgeIntegral ρ ![z,w])) =
      ((∫ x : D01EdgeSpace, d02BalancedEdgeIntegrand
        (fun i => p.coeff i.val) (fun i => q.coeff i.val) ρ x : ℝ) : ℂ) := by
  let E := d02BalancedCompactEdgeSet A
  let F : ℂ → ℂ → D01EdgeSpace → ℂ := fun z w x =>
    (d02BalancedEdgeProfile ρ x : ℂ)*
      d02BalancedLogExponentialWeight ![z,w] (d01RowColumnSums x)
  have hF : Continuous (fun y : ℂ × (ℂ × D01EdgeSpace) => F y.1 y.2.1 y.2.2) := by
    have hprofile := d02BalancedEdgeProfile_continuous ρ hρc
    have hsum := d01RowColumnSums_continuous
    dsimp [F]
    unfold d02BalancedLogExponentialWeight
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    fun_prop
  unfold d02BalancedShiftedEdgeIntegral
  simp_rw [d02BalancedWeightedEdgeIntegral_eq_compactIntegral ρ A _ hρcap]
  change d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
    ∫ x in E, F z w x)) = _
  rw [d02PolynomialCircle_two_setIntegral p q E
    (d02BalancedCompactEdgeSet_compact A) F hF]
  dsimp only [F]
  simp_rw [d02PolynomialCircle_const_mul, d02BalancedCauchyPolynomialWeight p q hp hq]
  rw [← d02BalancedWeightedEdgeIntegral_eq_compactIntegral ρ A _ hρcap]
  simp_rw [d02BalancedWeightedPolynomialEdgeIntegrand]
  exact integral_ofReal

theorem d02BalancedCauchy_profileKernel (p q : ℝ[X])
    (hp : p.natDegree≤4) (hq : q.natDegree≤4)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hA : (∑ i, A i)<1) (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
      d02BalancedShiftedEdgeIntegral ρ ![z,w])) =
      (d02BalancedProfileKernel (fun i => p.coeff i.val) (fun i => q.coeff i.val) ρ : ℂ) := by
  rw [d02BalancedCauchy_edgeIntegral p q hp hq ρ A hρc hρcap,
    d02BalancedEdgeIntegral_eq_profileKernel _ _ ρ A hA hρc hρcap]

theorem d02BalancedCauchy_originalDenominator (p q : ℝ[X])
    (hp : p.natDegree≤4) (hq : q.natDegree≤4)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hA : (∑ i, A i)<1) (hρc : ∀ i, Continuous (ρ i))
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i)) :
    d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
      d02BalancedShiftedEdgeIntegral ρ ![z,w])) =
      ((∫ a : Fin 4 → ℝ, (∏ i, ρ i (a i)) *
        denominatorZeroKernel (fun i => p.coeff i.val) (fun i => q.coeff i.val)
          (a 0) (a 1) (a 2) (a 3) : ℝ) : ℂ) := by
  apply d02BalancedCauchy_profileKernel p q hp hq ρ A hA hρc
  intro i t ht
  exact hρsupport i (subset_tsupport (ρ i) ht)

end
end SixthMoment
