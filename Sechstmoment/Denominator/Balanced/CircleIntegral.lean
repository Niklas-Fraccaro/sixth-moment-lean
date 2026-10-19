import Mathlib.Algebra.Polynomial.Eval.Degree
import Sechstmoment.Denominator.Balanced.ShiftedDiagonalIntegrability
import Sechstmoment.Zeta.PolynomialCircle

/-! Cauchy extraction commutes with the actual compactly localized
nine-edge integral.  The compact set and all integrability facts are
derived from the four profile caps. -/
namespace Sechstmoment
open MeasureTheory Set Complex Polynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem d02CircleExtract_setIntegral (m : ℕ) (E : Set D01EdgeSpace)
    (hE : IsCompact E) (F : ℂ → D01EdgeSpace → ℂ)
    (hF : Continuous (Function.uncurry F)) :
    d02CircleExtract m (fun z => ∫ x in E, F z x) =
      ∫ x in E, d02CircleExtract m (fun z => F z x) := by
  let B : Set ℝ := Icc 0 (2*Real.pi)
  let g : ℝ × D01EdgeSpace → ℂ := fun y =>
    deriv (circleMap 0 1) y.1 * (1/(circleMap 0 1 y.1)^(m+1)) * F (circleMap 0 1 y.1) y.2
  have hne (y : ℝ × D01EdgeSpace) : circleMap 0 1 y.1 ≠ 0 :=
    circleMap_ne_center (by norm_num : (1:ℝ)≠0)
  have hpow (y : ℝ × D01EdgeSpace) : (circleMap 0 1 y.1)^(m+1) ≠ 0 :=
    pow_ne_zero _ (hne y)
  have hg : Continuous g := by
    dsimp [g]
    simp_rw [deriv_circleMap]
    fun_prop
  have hgint : Integrable g ((volume.restrict B).prod (volume.restrict E)) := by
    rw [Measure.prod_restrict]
    exact hg.continuousOn.integrableOn_compact ((isCompact_Icc : IsCompact B).prod hE)
  unfold d02CircleExtract
  simp_rw [circleIntegral_def_Icc, smul_eq_mul]
  calc
    _ = (m.factorial:ℂ)/(2*Real.pi*I) * (∫ θ in B, ∫ x in E, g (θ,x)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with θ
      dsimp [g]
      rw [integral_const_mul]
      ring
    _ = (m.factorial:ℂ)/(2*Real.pi*I) * (∫ x in E, ∫ θ in B, g (θ,x)) := by
      rw [integral_integral_swap hgint]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1
      apply integral_congr_ae
      filter_upwards [] with θ
      dsimp [g]
      ring

theorem d02CircleExtract_continuous_parameter {A : Type*} [TopologicalSpace A]
    [FirstCountableTopology A] [LocallyCompactSpace A]
    (m : ℕ) (F : A → ℂ → ℂ) (hF : Continuous (Function.uncurry F)) :
    Continuous (fun a => d02CircleExtract m (F a)) := by
  have hjoint : Continuous (fun y : A × ℝ =>
      deriv (circleMap 0 1) y.2 * (1/(circleMap 0 1 y.2)^(m+1)) *
        F y.1 (circleMap 0 1 y.2)) := by
    simp_rw [deriv_circleMap]
    have hne (y : A × ℝ) : circleMap 0 1 y.2 ≠ 0 :=
      circleMap_ne_center (by norm_num : (1:ℝ)≠0)
    have hpow (y : A × ℝ) : (circleMap 0 1 y.2)^(m+1) ≠ 0 :=
      pow_ne_zero _ (hne y)
    fun_prop
  unfold d02CircleExtract
  apply continuous_const.mul
  simp_rw [circleIntegral_def_Icc, smul_eq_mul]
  exact continuous_parametric_integral_of_continuous
    (by simpa only [Function.uncurry_def,mul_assoc] using hjoint) isCompact_Icc

theorem d02PolynomialCircle_setIntegral (p : ℝ[X]) (E : Set D01EdgeSpace)
    (hE : IsCompact E) (F : ℂ → D01EdgeSpace → ℂ)
    (hF : Continuous (Function.uncurry F)) :
    d02PolynomialCircle p (fun z => ∫ x in E, F z x) =
      ∫ x in E, d02PolynomialCircle p (fun z => F z x) := by
  unfold d02PolynomialCircle Polynomial.sum
  simp_rw [d02CircleExtract_setIntegral _ E hE F hF, ← integral_const_mul]
  rw [integral_finsetSum]
  intro m hm
  -- Every extracted coefficient is a continuous function on the compact edge set.
  apply ContinuousOn.integrableOn_compact hE
  exact (continuous_const.mul (d02CircleExtract_continuous_parameter m
    (fun x z => F z x) (hF.comp (by fun_prop : Continuous
      (fun y : D01EdgeSpace × ℂ => (y.2,y.1)))))).continuousOn

theorem d02_evalDegreeFour_coeff (p : ℝ[X]) (hp : p.natDegree≤4) (x : ℝ) :
    evalDegreeFour (fun i : Fin 5 => p.coeff i.val) x = p.eval x := by
  unfold evalDegreeFour
  rw [p.eval_eq_sum_range' (by omega : p.natDegree<5)]
  exact Fin.sum_univ_eq_sum_range (fun i => p.coeff i*x^i) 5

theorem d02PolynomialCircle_two_exponentials (p : ℝ[X]) (c₀ c₁ u₀ u₁ : ℂ) :
    d02PolynomialCircle p (fun z => c₀*Complex.exp (u₀*z)+c₁*Complex.exp (u₁*z)) =
      c₀*p.eval₂ Complex.ofRealHom u₀+c₁*p.eval₂ Complex.ofRealHom u₁ := by
  rw [d02PolynomialCircle_add p _ _ (by fun_prop) (by fun_prop)]
  rw [d02PolynomialCircle_const_mul, d02PolynomialCircle_const_mul,
    d02PolynomialCircle_exp, d02PolynomialCircle_exp]

def d02BalancedCompactEdgeSet (A : Fin 4 → ℝ) : Set D01EdgeSpace :=
  d02BalancedEdgeCut∩Icc (fun _ => (0:ℝ)) (fun _ => d02BalancedEdgeBound A)

theorem d02BalancedCompactEdgeSet_compact (A : Fin 4 → ℝ) :
    IsCompact (d02BalancedCompactEdgeSet A) :=
  isCompact_Icc.inter_left d02BalancedEdgeCut_closed

theorem d02BalancedWeightedEdgeIntegral_eq_compactIntegral
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (w : D01LogSpace → ℂ)
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    (∫ x : D01EdgeSpace, d02BalancedWeightedEdgeIntegrand ρ w x) =
      ∫ x in d02BalancedCompactEdgeSet A,
        (d02BalancedEdgeProfile ρ x : ℂ)*w (d01RowColumnSums x) := by
  classical
  rw [← integral_indicator (d02BalancedCompactEdgeSet_compact A).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x∈d02BalancedEdgeCut
  · by_cases hp : d02BalancedEdgeProfile ρ x=0
    · simp [d02BalancedWeightedEdgeIntegrand,d02BalancedCompactEdgeSet,
        Set.indicator_apply,hx,hp]
    · have hK := d02BalancedEdge_profile_nonzero_bounded ρ A hρcap hx hp
      simp [d02BalancedWeightedEdgeIntegrand,d02BalancedCompactEdgeSet,hx,hK]
  · simp [d02BalancedWeightedEdgeIntegrand,d02BalancedCompactEdgeSet,hx]

theorem d02BalancedCircleWeight_extract (p q : ℝ[X]) (y : D01LogSpace) :
    d02PolynomialCircle p (fun z => d02PolynomialCircle q (fun w =>
      d02BalancedLogExponentialWeight ![z,w] y)) =
      ((p.eval (1/2-y.1 0)*q.eval (1/2-y.2 0)+
        p.eval (y.2 0-1/2)*q.eval (y.1 0-1/2) : ℝ) : ℂ) := by
  have heval (r : ℝ[X]) (t : ℝ) :
      r.eval₂ Complex.ofRealHom (t:ℂ) = ((r.eval t : ℝ):ℂ) := by
    simpa using (Polynomial.eval₂_at_apply (p := r) Complex.ofRealHom t)
  have hin (z : ℂ) :
      d02PolynomialCircle q (fun w => d02BalancedLogExponentialWeight ![z,w] y) =
        Complex.exp (((1/2-y.1 0 : ℝ):ℂ)*z)*((q.eval (1/2-y.2 0) : ℝ):ℂ)+
          Complex.exp (((y.2 0-1/2 : ℝ):ℂ)*z)*((q.eval (y.1 0-1/2) : ℝ):ℂ) := by
    unfold d02BalancedLogExponentialWeight
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    simp_rw [Complex.exp_add]
    have hcast (t : ℝ) : 1/2-(t:ℂ)=((1/2-t:ℝ):ℂ) := by push_cast; rfl
    have hcast' (t : ℝ) : (t:ℂ)-1/2=((t-1/2:ℝ):ℂ) := by push_cast; rfl
    simp_rw [hcast,hcast']
    simp_rw [mul_comm z,
      mul_comm _ (((1/2-y.2 0 : ℝ):ℂ)),
      mul_comm _ (((y.1 0-1/2 : ℝ):ℂ))]
    rw [d02PolynomialCircle_two_exponentials]
    simp only [heval]
  simp_rw [hin]
  have hout := d02PolynomialCircle_two_exponentials p
    ((q.eval (1/2-y.2 0) : ℝ):ℂ) ((q.eval (y.1 0-1/2) : ℝ):ℂ)
    (((1/2-y.1 0 : ℝ):ℂ)) (((y.2 0-1/2 : ℝ):ℂ))
  simp_rw [mul_comm (Complex.exp _)]
  rw [hout]
  simp only [heval]
  push_cast
  ring

end
end Sechstmoment
