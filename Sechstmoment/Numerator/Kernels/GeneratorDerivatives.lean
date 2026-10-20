import Sechstmoment.Analysis.Complex.CauchyBounds
import Sechstmoment.Analysis.Integration.ComplexParameter
import Sechstmoment.Numerator.Kernels.Integral
import Sechstmoment.Numerator.Kernels.ReflectionGenerator


namespace Sechstmoment
open Complex MeasureTheory Set Metric
open scoped Topology BigOperators

set_option maxHeartbeats 1000000
noncomputable section

private theorem complexInterval_hasDerivAt_ordered
    (F F' : ℂ → ℝ → ℂ) (z : ℂ) (a b : ℝ) (hab : a ≤ b)
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ z t, HasDerivAt (fun w => F w t) (F' z t) z) :
    HasDerivAt (fun w => ∫ t in a..b, F w t) (∫ t in a..b, F' z t) z := by
  have hc : Continuous (fun p : ℂ × ℝ =>
      ContinuousLinearMap.toSpanSingleton ℂ (F' p.1 p.2)) := by
    convert hF'.smul (continuous_const (y := ContinuousLinearMap.id ℂ ℂ)) using 1
    funext p
    apply ContinuousLinearMap.ext
    intro v
    change v*F' p.1 p.2 = F' p.1 p.2*v
    ring
  have h := complexIntervalIntegral_hasFDerivAt F
    (fun z t => ContinuousLinearMap.toSpanSingleton ℂ (F' z t)) z 1 a b
    (by norm_num) hab hF.continuousOn hc.continuousOn
    (fun w _ t _ => (hd w t).hasFDerivAt)
  have hi : IntervalIntegrable
      (fun t => ContinuousLinearMap.toSpanSingleton ℂ (F' z t)) volume a b :=
    (hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  simpa only [ContinuousLinearMap.intervalIntegral_apply hi,
    ContinuousLinearMap.toSpanSingleton_apply,one_smul] using h.hasDerivAt

theorem complexInterval_hasDerivAt_of_joint_continuity
    (F F' : ℂ → ℝ → ℂ) (z : ℂ) (a b : ℝ)
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ z t, HasDerivAt (fun w => F w t) (F' z t) z) :
    HasDerivAt (fun w => ∫ t in a..b, F w t) (∫ t in a..b, F' z t) z := by
  by_cases hab : a ≤ b
  · exact complexInterval_hasDerivAt_ordered F F' z a b hab hF hF' hd
  · have h := (complexInterval_hasDerivAt_ordered F F' z b a
      (le_of_not_ge hab) hF hF' hd).neg
    convert h using 1
    · funext w
      change (∫ t in a..b, F w t) = -(∫ t in b..a, F w t)
      exact intervalIntegral.integral_symm b a
    · exact intervalIntegral.integral_symm b a

def simplexExpPowerKernel (n : ℕ) (q : Fin 4 → ℂ) (z : ℂ) (x y w : ℝ) : ℂ :=
  (complexSimplexDot q x y w)^n*Complex.exp (z*complexSimplexDot q x y w)

def simplexExpMomentDerivative (n : ℕ) (q : Fin 4 → ℂ) (z : ℂ) : ℂ :=
  complexSimplexExpectation (simplexExpPowerKernel n q z)

theorem simplexExpPowerKernel_hasDerivAt (n : ℕ) (q : Fin 4 → ℂ)
    (z : ℂ) (x y w : ℝ) :
    HasDerivAt (fun z => simplexExpPowerKernel n q z x y w)
      (simplexExpPowerKernel (n+1) q z x y w) z := by
  have hd := ((Complex.hasDerivAt_exp (z*complexSimplexDot q x y w)).comp z
    ((hasDerivAt_id z).mul_const (complexSimplexDot q x y w))).const_mul
      ((complexSimplexDot q x y w)^n)
  convert hd using 1
  · rfl
  · unfold simplexExpPowerKernel
    rw [pow_succ]
    ring

theorem simplexExpMomentDerivative_hasDerivAt (n : ℕ) (q : Fin 4 → ℂ) (z : ℂ) :
    HasDerivAt (simplexExpMomentDerivative n q)
      (simplexExpMomentDerivative (n+1) q z) z := by
  have hw (x y : ℝ) (z : ℂ) := complexInterval_hasDerivAt_of_joint_continuity
    (fun z w => simplexExpPowerKernel n q z x y w)
    (fun z w => simplexExpPowerKernel (n+1) q z x y w) z 0 (1-x-y)
    (by unfold simplexExpPowerKernel complexSimplexDot; fun_prop)
    (by unfold simplexExpPowerKernel complexSimplexDot; fun_prop)
    (fun z w => simplexExpPowerKernel_hasDerivAt n q z x y w)
  have hy (x : ℝ) (z : ℂ) := complexInterval_hasDerivAt_of_joint_continuity
    (fun z y => ∫ w in (0:ℝ)..1-x-y, simplexExpPowerKernel n q z x y w)
    (fun z y => ∫ w in (0:ℝ)..1-x-y, simplexExpPowerKernel (n+1) q z x y w)
    z 0 (1-x)
    (by unfold simplexExpPowerKernel complexSimplexDot; fun_prop)
    (by unfold simplexExpPowerKernel complexSimplexDot; fun_prop)
    (fun z y => hw x y z)
  have hx := complexInterval_hasDerivAt_of_joint_continuity
    (fun z x => ∫ y in (0:ℝ)..1-x, ∫ w in (0:ℝ)..1-x-y,
      simplexExpPowerKernel n q z x y w)
    (fun z x => ∫ y in (0:ℝ)..1-x, ∫ w in (0:ℝ)..1-x-y,
      simplexExpPowerKernel (n+1) q z x y w) z 0 1
    (by unfold simplexExpPowerKernel complexSimplexDot; fun_prop)
    (by unfold simplexExpPowerKernel complexSimplexDot; fun_prop)
    (fun z x => hy x z)
  exact hx.const_mul 6

theorem simplexExpGenerator_iteratedDeriv (n : ℕ) (q : Fin 4 → ℂ) (z : ℂ) :
    iteratedDeriv n (simplexExpGenerator q) z = simplexExpMomentDerivative n q z := by
  induction n generalizing z with
  | zero =>
    rw [iteratedDeriv_zero]
    unfold simplexExpMomentDerivative simplexExpGenerator
    congr 1
    funext x y w
    simp [simplexExpPowerKernel]
  | succ n hn =>
    have he : iteratedDeriv n (simplexExpGenerator q) = simplexExpMomentDerivative n q :=
      funext hn
    rw [iteratedDeriv_succ,he]
    exact (simplexExpMomentDerivative_hasDerivAt n q z).deriv

def numeratorExpMomentDerivative (n : ℕ) (a b : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..min a b,
    (numeratorP (b-t) (a-t):ℂ)*simplexExpMomentDerivative n (numeratorExpNodes a b t) z

theorem numeratorExpMomentDerivative_hasDerivAt (n : ℕ) (a b : ℝ) (z : ℂ) :
    HasDerivAt (numeratorExpMomentDerivative n a b)
      (numeratorExpMomentDerivative (n+1) a b z) z := by
  unfold numeratorExpMomentDerivative
  apply complexInterval_hasDerivAt_of_joint_continuity
    (fun z t => (numeratorP (b-t) (a-t):ℂ)*
      simplexExpMomentDerivative n (numeratorExpNodes a b t) z)
    (fun z t => (numeratorP (b-t) (a-t):ℂ)*
      simplexExpMomentDerivative (n+1) (numeratorExpNodes a b t) z) z 0 (min a b)
  · unfold numeratorP simplexExpMomentDerivative numeratorExpNodes
      complexSimplexExpectation simplexExpPowerKernel complexSimplexDot
    fun_prop
  · unfold numeratorP simplexExpMomentDerivative numeratorExpNodes
      complexSimplexExpectation simplexExpPowerKernel complexSimplexDot
    fun_prop
  · intro z t
    exact (simplexExpMomentDerivative_hasDerivAt n (numeratorExpNodes a b t) z).const_mul
      (numeratorP (b-t) (a-t):ℂ)

theorem numeratorExpGenerator_iteratedDeriv (n : ℕ) (a b : ℝ) (z : ℂ) :
    iteratedDeriv n (numeratorExpGenerator a b) z = numeratorExpMomentDerivative n a b z := by
  induction n generalizing z with
  | zero =>
    rw [iteratedDeriv_zero]
    unfold numeratorExpGenerator numeratorExpMomentDerivative
    apply intervalIntegral.integral_congr
    intro t _
    change (numeratorP (b-t) (a-t):ℂ)*simplexExpGenerator (numeratorExpNodes a b t) z =
      (numeratorP (b-t) (a-t):ℂ)*simplexExpMomentDerivative 0 (numeratorExpNodes a b t) z
    rw [← simplexExpGenerator_iteratedDeriv 0,iteratedDeriv_zero]
  | succ n hn =>
    have he : iteratedDeriv n (numeratorExpGenerator a b) = numeratorExpMomentDerivative n a b :=
      funext hn
    rw [iteratedDeriv_succ,he]
    exact (numeratorExpMomentDerivative_hasDerivAt n a b z).deriv

theorem complexSimplexExpectation_ofReal (f : ℝ → ℝ → ℝ → ℝ) :
    complexSimplexExpectation (fun x y w => (f x y w:ℂ)) = (simplexExpectation f:ℂ) := by
  unfold complexSimplexExpectation simplexExpectation
  simp only [intervalIntegral.integral_ofReal]
  push_cast
  rfl

theorem numeratorExpNodes_dot (a b t x y w : ℝ) :
    complexSimplexDot (numeratorExpNodes a b t) x y w =
      (simplexDot (-1/2) (a-t-1/2) (1/2-b+t) (1/2) x y w:ℂ) := by
  unfold complexSimplexDot numeratorExpNodes simplexDot
  simp only [Matrix.cons_val_zero]
  push_cast
  ring

theorem numeratorExpGenerator_iteratedDeriv_zero (n : ℕ) (a b : ℝ) :
    iteratedDeriv n (numeratorExpGenerator a b) 0 =
      Complex.ofReal (∫ t in (0:ℝ)..min a b, numeratorP (b-t) (a-t)*
        simplexExpectation (fun x y w =>
          (simplexDot (-1/2) (a-t-1/2) (1/2-b+t) (1/2) x y w)^n)) := by
  rw [numeratorExpGenerator_iteratedDeriv]
  have he (t : ℝ) : simplexExpMomentDerivative n (numeratorExpNodes a b t) 0 =
      (simplexExpectation (fun x y w =>
        (simplexDot (-1/2) (a-t-1/2) (1/2-b+t) (1/2) x y w)^n):ℂ) := by
    unfold simplexExpMomentDerivative
    have hf : simplexExpPowerKernel n (numeratorExpNodes a b t) 0 =
        (fun x y w => Complex.ofReal
          ((simplexDot (-1/2) (a-t-1/2) (1/2-b+t) (1/2) x y w)^n)) := by
      funext x y w
      unfold simplexExpPowerKernel
      rw [numeratorExpNodes_dot]
      simp
    rw [hf,complexSimplexExpectation_ofReal]
  unfold numeratorExpMomentDerivative
  simp_rw [he,← Complex.ofReal_mul]
  rw [intervalIntegral.integral_ofReal]

theorem numeratorExpGenerator_iteratedDeriv_le_four (r : Fin 5) (a b : ℝ) :
    iteratedDeriv r.val (numeratorExpGenerator a b) 0 =
      Complex.ofReal (∫ t in (0:ℝ)..min a b, numeratorIntegrand r.val a b t) := by
  rw [numeratorExpGenerator_iteratedDeriv_zero]
  simp_rw [dirichlet_moment_le_four]
  rfl

theorem numeratorPointKernel_polynomial_min (p : Fin 5 → ℝ) (a b : ℝ) :
    numeratorPointKernel p a b =
      ∑ r : Fin 5, p r*(∫ t in (0:ℝ)..min a b, numeratorIntegrand r.val a b t) := by
  unfold numeratorPointKernel
  simp_rw [simplexExpectation_polynomial]
  have he (t : ℝ) : numeratorP (b-t) (a-t)*
      (∑ r : Fin 5, p r*simplexMonomialAverage r.val (-1/2) (a-t-1/2) (1/2-b+t) (1/2)) =
      ∑ r : Fin 5, p r*numeratorIntegrand r.val a b t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    unfold numeratorIntegrand
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul]
  · intro r _
    apply Continuous.intervalIntegrable
    unfold numeratorIntegrand numeratorP simplexMonomialAverage homogeneousFour
    fun_prop

theorem numeratorExpGenerator_operator_eq_pointKernel (p : Fin 5 → ℝ) (a b : ℝ) :
    finiteDifferentialOperator 4 (fun r => (p r:ℂ)) (numeratorExpGenerator a b) 0 =
      (numeratorPointKernel p a b:ℂ) := by
  unfold finiteDifferentialOperator
  simp_rw [numeratorExpGenerator_iteratedDeriv_le_four]
  rw [numeratorPointKernel_polynomial_min]
  push_cast
  rfl

theorem reflectedPolarGenerator_operator_eq_pointKernel (p : Fin 5 → ℝ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b < 1) :
    finiteDifferentialOperator 4 (fun r => (p r:ℂ)) (reflectedPolarGenerator a b) 0 =
      (numeratorPointKernel p a (1-b):ℂ) := by
  rw [← numeratorExpGenerator_reflection a b ha hb hab]
  exact numeratorExpGenerator_operator_eq_pointKernel p a (1-b)

theorem reflectedPolarContour_operator_eq_pointKernel (p : Fin 5 → ℝ) (a b R : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b < 1) (hR : 0 < R) :
    finiteDifferentialOperator 4 (fun r => (p r:ℂ))
      (fun z => Complex.exp (-z/2)*polarContourJ a b (-z) R) 0 =
      (numeratorPointKernel p a (1-b):ℂ) := by
  have he : numeratorExpGenerator a (1-b) =ᶠ[𝓝 (0:ℂ)]
      (fun z => Complex.exp (-z/2)*polarContourJ a b (-z) R) := by
    filter_upwards [ball_mem_nhds (0:ℂ) hR] with z hz
    exact numeratorExpGenerator_reflection_contour a b z R ha hb hab
      (by simpa only [mem_ball,dist_zero_right] using hz)
  rw [← numeratorExpGenerator_operator_eq_pointKernel p a (1-b)]
  unfold finiteDifferentialOperator
  apply Finset.sum_congr rfl
  intro r _
  rw [he.iteratedDeriv_eq r.val]

end
end Sechstmoment
