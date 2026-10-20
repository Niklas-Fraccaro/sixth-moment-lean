import Sechstmoment.Denominator.Balanced.CauchyIntegration
import Sechstmoment.Denominator.Unbalanced.ShiftedDiagonalIntegrability

namespace Sechstmoment
open MeasureTheory Set Complex Polynomial
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def d04UnbalancedLogPolynomialWeight (p q : Fin 5 → ℝ) (y : D01LogSpace) : ℂ :=
  ((evalDegreeFour p (y.2 0-1/2)*evalDegreeFour q (1/2-y.2 1) : ℝ) : ℂ)

theorem d04UnbalancedCircleWeight_extract (p q : ℝ[X]) (y : D01LogSpace) :
    d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
      d04UnbalancedLogExponentialWeight ![z,w] y)) =
      ((p.eval (y.2 0-1/2)*q.eval (1/2-y.2 1) : ℝ) : ℂ) := by
  have heval (r : ℝ[X]) (t : ℝ) :
      r.eval₂ Complex.ofRealHom (t:ℂ) = ((r.eval t : ℝ):ℂ) := by
    simpa using (Polynomial.eval₂_at_apply (p := r) Complex.ofRealHom t)
  have hcast (t : ℝ) : (t:ℂ)-1/2=((t-1/2:ℝ):ℂ) := by push_cast; rfl
  have hcast' (t : ℝ) : 1/2-(t:ℂ)=((1/2-t:ℝ):ℂ) := by push_cast; rfl
  have hin (z : ℂ) :
      d02PolynomialCircle q (fun w => d04UnbalancedLogExponentialWeight ![z,w] y) =
        Complex.exp (((y.2 0-1/2:ℝ):ℂ)*z)*((q.eval (1/2-y.2 1):ℝ):ℂ) := by
    unfold d04UnbalancedLogExponentialWeight
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    simp_rw [hcast,hcast',Complex.exp_add]
    simp_rw [mul_comm z,mul_comm _ (((1/2-y.2 1:ℝ):ℂ))]
    rw [d02PolynomialCircle_const_mul,d02PolynomialCircle_exp,heval]
  simp_rw [hin,mul_comm (Complex.exp _)]
  rw [d02PolynomialCircle_const_mul,d02PolynomialCircle_exp,heval]
  push_cast
  ring

theorem d04UnbalancedCauchyPolynomialWeight (p q : ℝ[X])
    (hp : p.natDegree≤4) (hq : q.natDegree≤4) (y : D01LogSpace) :
    d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
      d04UnbalancedLogExponentialWeight ![z,w] y)) =
      d04UnbalancedLogPolynomialWeight (fun i => p.coeff i.val) (fun i => q.coeff i.val) y := by
  rw [d04UnbalancedCircleWeight_extract]
  unfold d04UnbalancedLogPolynomialWeight
  simp_rw [d02_evalDegreeFour_coeff p hp,d02_evalDegreeFour_coeff q hq]

theorem d04UnbalancedWeightedPolynomialEdgeIntegrand (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (x : D01EdgeSpace) :
    d04UnbalancedWeightedEdgeIntegrand ρ (d04UnbalancedLogPolynomialWeight p q) x =
      (d04UnbalancedEdgeIntegrand p q ρ x : ℂ) := by
  by_cases hx : x∈d01NonnegativeOrthant
  · simp only [d04UnbalancedWeightedEdgeIntegrand,d04UnbalancedEdgeIntegrand,
      indicator_of_mem hx,d04UnbalancedLogPolynomialWeight,d04UnbalancedEdgePolynomial]
    push_cast
    rfl
  · simp [d04UnbalancedWeightedEdgeIntegrand,d04UnbalancedEdgeIntegrand,hx]

theorem d04UnbalancedCauchy_edgeIntegral (p q : ℝ[X])
    (hp : p.natDegree≤4) (hq : q.natDegree≤4)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
      d04UnbalancedShiftedEdgeIntegral ρ ![z,w])) =
      ((∫ x : D01EdgeSpace, d04UnbalancedEdgeIntegrand
        (fun i => p.coeff i.val) (fun i => q.coeff i.val) ρ x : ℝ) : ℂ) := by
  let E := d04UnbalancedCompactEdgeSet A
  let F : ℂ → ℂ → D01EdgeSpace → ℂ := fun z w x =>
    (d04UnbalancedEdgeProfile ρ x : ℂ)*
      d04UnbalancedLogExponentialWeight ![z,w] (d01RowColumnSums x)
  have hF : Continuous (fun y : ℂ × (ℂ × D01EdgeSpace) => F y.1 y.2.1 y.2.2) := by
    have hprofile := d04UnbalancedEdgeProfile_continuous ρ hρc
    have hsum := d01RowColumnSums_continuous
    dsimp [F]
    unfold d04UnbalancedLogExponentialWeight
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    fun_prop
  simp_rw [d04UnbalancedShiftedEdgeIntegral_eq_weighted,
    d04UnbalancedWeightedEdgeIntegral_eq_compactIntegral ρ A _ hρcap]
  change d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
    ∫ x in E, F z w x)) = _
  rw [d02PolynomialCircle_two_setIntegral p q E
    (d04UnbalancedCompactEdgeSet_compact A) F hF]
  dsimp only [F]
  simp_rw [d02PolynomialCircle_const_mul,d04UnbalancedCauchyPolynomialWeight p q hp hq]
  rw [← d04UnbalancedWeightedEdgeIntegral_eq_compactIntegral ρ A _ hρcap]
  simp_rw [d04UnbalancedWeightedPolynomialEdgeIntegrand]
  exact integral_ofReal

theorem d04UnbalancedCauchy_profileKernel (p q : ℝ[X])
    (hp : p.natDegree≤4) (hq : q.natDegree≤4)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
      d04UnbalancedShiftedEdgeIntegral ρ ![z,w])) =
      (d04UnbalancedProfileKernel (fun i => p.coeff i.val) (fun i => q.coeff i.val) ρ : ℂ) := by
  rw [d04UnbalancedCauchy_edgeIntegral p q hp hq ρ A hρc hρcap,
    d04UnbalancedEdgeIntegral_eq_profileKernel _ _ ρ A hρc hρcap]

theorem d04UnbalancedCauchy_originalDenominator (p q : ℝ[X])
    (hp : p.natDegree≤4) (hq : q.natDegree≤4)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρsupport : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i)) :
    d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
      d04UnbalancedShiftedEdgeIntegral ρ ![z,w])) =
      ((∫ a : Fin 4 → ℝ, (∏ i, ρ i (a i)) *
        denominatorMinusKernel (fun i => p.coeff i.val) (fun i => q.coeff i.val)
          (a 0) (a 1) (a 2) (a 3) : ℝ) : ℂ) := by
  apply d04UnbalancedCauchy_profileKernel p q hp hq ρ A hρc
  intro i t ht
  exact hρsupport i (subset_tsupport (ρ i) ht)

end
end Sechstmoment
