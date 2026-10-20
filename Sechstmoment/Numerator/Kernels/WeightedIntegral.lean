import Sechstmoment.Numerator.Kernels.GeneratorDerivatives
import Sechstmoment.Numerator.V.ReflectedKernel

namespace Sechstmoment
open Complex MeasureTheory Set Metric Filter Polynomial
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1600000

def polynomialIntervalProfile (η : ℝ) (P : ℝ[X]) (a : ℝ) : ℝ := P.eval (1-a/η)

def weightedPolarJ (η : ℝ) (P Q : ℝ[X]) (z : ℂ) : ℂ :=
  ∫ a in (0:ℝ)..η, ∫ b in (0:ℝ)..η,
    (polynomialIntervalProfile η P a:ℂ)*(polynomialIntervalProfile η Q b:ℂ)*polarJ a b z

private def weightedPolarTerm (η : ℝ) (P Q : ℝ[X]) (z : ℂ)
    (j : Fin 4) (a b : ℝ) : ℂ :=
  match j.val with
  | 0 => (polynomialIntervalProfile η P a:ℂ)*polarB a z*
      ((polynomialIntervalProfile η Q b:ℂ)*polarB b z)*polarH 2 z
  | 1 => (polynomialIntervalProfile η P a:ℂ)*polarB a z*
      ((polynomialIntervalProfile η Q b:ℂ)*polarC b z)*polarH 1 z
  | 2 => (polynomialIntervalProfile η P a:ℂ)*polarC a z*
      ((polynomialIntervalProfile η Q b:ℂ)*polarB b z)*polarH 1 z
  | _ => (polynomialIntervalProfile η P a:ℂ)*polarC a z*
      ((polynomialIntervalProfile η Q b:ℂ)*polarC b z)*polarH 0 z

private theorem weightedPolarTerm_continuous (η : ℝ) (P Q : ℝ[X]) (z : ℂ) (j : Fin 4) :
    Continuous (fun p : ℝ×ℝ => weightedPolarTerm η P Q z j p.1 p.2) := by
  fin_cases j <;> unfold weightedPolarTerm polynomialIntervalProfile polarB polarC polarH <;> fun_prop

theorem polarPolynomialBilinearJ_eq_weightedPolarJ (η : ℝ) (P Q : ℝ[X]) (z : ℂ) :
    polarPolynomialBilinearJ η P Q z = weightedPolarJ η P Q z := by
  have he (a b : ℝ) : (polynomialIntervalProfile η P a:ℂ)*
      (polynomialIntervalProfile η Q b:ℂ)*polarJ a b z =
      ∑ j : Fin 4, weightedPolarTerm η P Q z j a b := by
    simp [Fin.sum_univ_succ,weightedPolarTerm,polarJ]
    ring
  unfold weightedPolarJ
  simp_rw [he]
  have hi (a : ℝ) (j : Fin 4) : IntervalIntegrable (weightedPolarTerm η P Q z j a) volume 0 η :=
    ((weightedPolarTerm_continuous η P Q z j).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 η
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => hi _ j)]
  have ho (j : Fin 4) : IntervalIntegrable (fun a : ℝ => ∫ b in (0:ℝ)..η,
      weightedPolarTerm η P Q z j a b) volume 0 η := by
    apply Continuous.intervalIntegrable
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := weightedPolarTerm η P Q z j)
      (weightedPolarTerm_continuous η P Q z j) 0 η
  rw [intervalIntegral.integral_finsetSum (fun j _ => ho j)]
  simp [Fin.sum_univ_succ,weightedPolarTerm,intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul]
  unfold polarPolynomialBilinearJ polarPolynomialB polarPolynomialC polynomialIntervalProfile
  ring

theorem numeratorExpMomentDerivative_joint_continuous (n : ℕ) :
    Continuous (fun p : ℂ×(ℝ×ℝ) => numeratorExpMomentDerivative n p.2.1 p.2.2 p.1) := by
  unfold numeratorExpMomentDerivative simplexExpMomentDerivative simplexExpPowerKernel
    complexSimplexExpectation complexSimplexDot numeratorExpNodes numeratorP
  fun_prop

attribute [local irreducible] numeratorExpMomentDerivative

theorem numeratorPointKernel_joint_continuous (p : Fin 5→ℝ) :
    Continuous (fun q : ℝ×ℝ => numeratorPointKernel p q.1 q.2) := by
  simp_rw [numeratorPointKernel_polynomial_min]
  unfold numeratorIntegrand numeratorP simplexMonomialAverage homogeneousFour
  fun_prop

attribute [local irreducible] numeratorPointKernel

def weightedNumeratorExpMomentDerivative (n : ℕ) (η : ℝ) (P Q : ℝ[X]) (z : ℂ) : ℂ :=
  ∫ a in (0:ℝ)..η, ∫ b in (0:ℝ)..η,
    (polynomialIntervalProfile η P a:ℂ)*(polynomialIntervalProfile η Q b:ℂ)*
      numeratorExpMomentDerivative n a (1-b) z

def weightedNumeratorExpGenerator (η : ℝ) (P Q : ℝ[X]) (z : ℂ) : ℂ :=
  ∫ a in (0:ℝ)..η, ∫ b in (0:ℝ)..η,
    (polynomialIntervalProfile η P a:ℂ)*(polynomialIntervalProfile η Q b:ℂ)*
      numeratorExpGenerator a (1-b) z

theorem weightedNumeratorExpMomentDerivative_hasDerivAt (n : ℕ) (η : ℝ) (P Q : ℝ[X]) (z : ℂ) :
    HasDerivAt (weightedNumeratorExpMomentDerivative n η P Q)
      (weightedNumeratorExpMomentDerivative (n+1) η P Q z) z := by
  have hc (m : ℕ) : Continuous (fun p : ℂ×(ℝ×ℝ) =>
      (polynomialIntervalProfile η P p.2.1:ℂ)*(polynomialIntervalProfile η Q p.2.2:ℂ)*
        numeratorExpMomentDerivative m p.2.1 (1-p.2.2) p.1) := by
    exact (by unfold polynomialIntervalProfile; fun_prop : Continuous
      (fun p : ℂ×(ℝ×ℝ) => (polynomialIntervalProfile η P p.2.1:ℂ)*
        (polynomialIntervalProfile η Q p.2.2:ℂ))).mul
      ((numeratorExpMomentDerivative_joint_continuous m).comp (by fun_prop : Continuous
        (fun p : ℂ×(ℝ×ℝ) => (p.1,(p.2.1,1-p.2.2)))))
  have hb (a : ℝ) (w : ℂ) := complexInterval_hasDerivAt_of_joint_continuity
    (fun z b => (polynomialIntervalProfile η P a:ℂ)*(polynomialIntervalProfile η Q b:ℂ)*
      numeratorExpMomentDerivative n a (1-b) z)
    (fun z b => (polynomialIntervalProfile η P a:ℂ)*(polynomialIntervalProfile η Q b:ℂ)*
      numeratorExpMomentDerivative (n+1) a (1-b) z) w 0 η
    ((hc n).comp (by fun_prop : Continuous (fun p : ℂ×ℝ => (p.1,(a,p.2)))))
    ((hc (n+1)).comp (by fun_prop : Continuous (fun p : ℂ×ℝ => (p.1,(a,p.2)))))
    (fun z b => (numeratorExpMomentDerivative_hasDerivAt n a (1-b) z).const_mul _)
  have ho (m : ℕ) : Continuous (Function.uncurry (fun z a =>
      ∫ b in (0:ℝ)..η, (polynomialIntervalProfile η P a:ℂ)*
        (polynomialIntervalProfile η Q b:ℂ)*numeratorExpMomentDerivative m a (1-b) z)) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun p:ℂ×ℝ => fun b:ℝ =>
        (polynomialIntervalProfile η P p.2:ℂ)*(polynomialIntervalProfile η Q b:ℂ)*
          numeratorExpMomentDerivative m p.2 (1-b) p.1)
      ((hc m).comp (by fun_prop : Continuous (fun p : (ℂ×ℝ)×ℝ => (p.1.1,(p.1.2,p.2))))) 0 η
  unfold weightedNumeratorExpMomentDerivative
  exact complexInterval_hasDerivAt_of_joint_continuity
    (fun w a => ∫ b in (0:ℝ)..η, (polynomialIntervalProfile η P a:ℂ)*
      (polynomialIntervalProfile η Q b:ℂ)*numeratorExpMomentDerivative n a (1-b) w)
    (fun w a => ∫ b in (0:ℝ)..η, (polynomialIntervalProfile η P a:ℂ)*
      (polynomialIntervalProfile η Q b:ℂ)*numeratorExpMomentDerivative (n+1) a (1-b) w)
    z 0 η (ho n) (ho (n+1)) (fun w a => hb a w)
theorem weightedNumeratorExpGenerator_iteratedDeriv (n : ℕ) (η : ℝ) (P Q : ℝ[X]) (z : ℂ) :
    iteratedDeriv n (weightedNumeratorExpGenerator η P Q) z =
      weightedNumeratorExpMomentDerivative n η P Q z := by
  induction n generalizing z with
  | zero =>
    rw [iteratedDeriv_zero]
    unfold weightedNumeratorExpGenerator weightedNumeratorExpMomentDerivative
    simp_rw [← numeratorExpGenerator_iteratedDeriv 0,iteratedDeriv_zero]
  | succ n hn =>
    have he : iteratedDeriv n (weightedNumeratorExpGenerator η P Q) =
        weightedNumeratorExpMomentDerivative n η P Q := funext hn
    rw [iteratedDeriv_succ,he]
    exact (weightedNumeratorExpMomentDerivative_hasDerivAt n η P Q z).deriv

theorem vReflectedPolynomialJ_eq_weighted_reflection (η : ℝ) (P Q : ℝ[X]) (z : ℂ) :
    vReflectedPolynomialJ η P Q z =
      ∫ a in (0:ℝ)..η, ∫ b in (0:ℝ)..η,
        (polynomialIntervalProfile η P a:ℂ)*(polynomialIntervalProfile η Q b:ℂ)*
          reflectedPolarGenerator a b z := by
  unfold vReflectedPolynomialJ
  rw [polarPolynomialBilinearJ_eq_weightedPolarJ]
  unfold weightedPolarJ reflectedPolarGenerator
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro a _
  dsimp only
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro b _
  ring

theorem vReflectedPolynomialJ_eq_weightedNumeratorExpGenerator
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (P Q : ℝ[X]) :
    vReflectedPolynomialJ η P Q = weightedNumeratorExpGenerator η P Q := by
  funext z
  rw [vReflectedPolynomialJ_eq_weighted_reflection]
  unfold weightedNumeratorExpGenerator
  apply intervalIntegral.integral_congr_Ioo_of_le hη.le
  intro a ha
  apply intervalIntegral.integral_congr_Ioo_of_le hη.le
  intro b hb
  dsimp only
  rw [numeratorExpGenerator_reflection a b ha.1 hb.1 (by linarith [ha.2,hb.2])]

theorem vReflectedPolynomialJ_iteratedDeriv_eq_weightedNumerator
    (n : ℕ) (η : ℝ) (hη : 0<η) (hηu : η<1/4) (P Q : ℝ[X]) (z : ℂ) :
    iteratedDeriv n (vReflectedPolynomialJ η P Q) z =
      weightedNumeratorExpMomentDerivative n η P Q z := by
  rw [vReflectedPolynomialJ_eq_weightedNumeratorExpGenerator η hη hηu P Q,
    weightedNumeratorExpGenerator_iteratedDeriv]

def weightedNumeratorPointKernel (p : Fin 5→ℝ) (η : ℝ) (P Q : ℝ[X]) : ℝ :=
  ∫ a in (0:ℝ)..η, ∫ b in (0:ℝ)..η,
    polynomialIntervalProfile η P a*polynomialIntervalProfile η Q b*
      numeratorPointKernel p a (1-b)

theorem weightedNumeratorDerivativeIntegrand_continuous (n : ℕ) (η : ℝ) (P Q : ℝ[X]) (z : ℂ) :
    Continuous (fun q:ℝ×ℝ=>(polynomialIntervalProfile η P q.1:ℂ)*
      (polynomialIntervalProfile η Q q.2:ℂ)*numeratorExpMomentDerivative n q.1 (1-q.2) z) := by
  exact (by unfold polynomialIntervalProfile; fun_prop : Continuous
    (fun q:ℝ×ℝ=>(polynomialIntervalProfile η P q.1:ℂ)*
      (polynomialIntervalProfile η Q q.2:ℂ))).mul
    ((numeratorExpMomentDerivative_joint_continuous n).comp (by fun_prop : Continuous
      (fun q:ℝ×ℝ=>(z,(q.1,1-q.2)))))

theorem weightedNumeratorPointKernel_integrable (p : Fin 5→ℝ) (η : ℝ) (P Q : ℝ[X]) :
    (∀ a:ℝ, IntervalIntegrable (fun b:ℝ=>polynomialIntervalProfile η P a*
        polynomialIntervalProfile η Q b*numeratorPointKernel p a (1-b)) volume 0 η) ∧
    IntervalIntegrable (fun a:ℝ=>∫ b in (0:ℝ)..η,polynomialIntervalProfile η P a*
      polynomialIntervalProfile η Q b*numeratorPointKernel p a (1-b)) volume 0 η := by
  have hc : Continuous (fun q:ℝ×ℝ=>polynomialIntervalProfile η P q.1*
      polynomialIntervalProfile η Q q.2*numeratorPointKernel p q.1 (1-q.2)) :=
    (by unfold polynomialIntervalProfile; fun_prop : Continuous
      (fun q:ℝ×ℝ=>polynomialIntervalProfile η P q.1*polynomialIntervalProfile η Q q.2)).mul
      ((numeratorPointKernel_joint_continuous p).comp (by fun_prop : Continuous
        (fun q:ℝ×ℝ=>(q.1,1-q.2))))
  exact ⟨fun a=> (hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 η,
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun a b => polynomialIntervalProfile η P a*
        polynomialIntervalProfile η Q b*numeratorPointKernel p a (1-b)) hc 0 η).intervalIntegrable 0 η⟩

theorem weightedNumeratorPointKernel_ofReal (p : Fin 5→ℝ) (η : ℝ) (P Q : ℝ[X]) :
    Complex.ofReal (weightedNumeratorPointKernel p η P Q) =
      ∫ a in (0:ℝ)..η, ∫ b in (0:ℝ)..η,
        (polynomialIntervalProfile η P a:ℂ)*(polynomialIntervalProfile η Q b:ℂ)*
          (numeratorPointKernel p a (1-b):ℂ) := by
  unfold weightedNumeratorPointKernel
  simp only [←intervalIntegral.integral_ofReal,Complex.ofReal_mul]

theorem weightedNumeratorExpGenerator_operator_eq_weightedPointKernel
    (p : Fin 5→ℝ) (η : ℝ) (P Q : ℝ[X]) :
    finiteDifferentialOperator 4 (fun r=>(p r:ℂ)) (weightedNumeratorExpGenerator η P Q) 0 =
      Complex.ofReal (weightedNumeratorPointKernel p η P Q) := by
  rw [weightedNumeratorPointKernel_ofReal]
  unfold finiteDifferentialOperator
  simp_rw [weightedNumeratorExpGenerator_iteratedDeriv]
  unfold weightedNumeratorExpMomentDerivative
  simp_rw [←intervalIntegral.integral_const_mul]
  have hc (r : Fin 5) : Continuous (fun q:ℝ×ℝ=> (p r:ℂ)*
      ((polynomialIntervalProfile η P q.1:ℂ)*(polynomialIntervalProfile η Q q.2:ℂ)*
        numeratorExpMomentDerivative r.val q.1 (1-q.2) 0)) :=
    continuous_const.mul (weightedNumeratorDerivativeIntegrand_continuous r.val η P Q 0)
  rw [←intervalIntegral.integral_finsetSum (fun r _ =>
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun a b => (p r:ℂ)*((polynomialIntervalProfile η P a:ℂ)*
        (polynomialIntervalProfile η Q b:ℂ)*numeratorExpMomentDerivative r.val a (1-b) 0))
      (hc r) 0 η).intervalIntegrable 0 η)]
  have he (a b : ℝ) :
      ∑ r : Fin 5, (p r:ℂ)*((polynomialIntervalProfile η P a:ℂ)*
        (polynomialIntervalProfile η Q b:ℂ)*numeratorExpMomentDerivative r.val a (1-b) 0) =
      (polynomialIntervalProfile η P a:ℂ)*(polynomialIntervalProfile η Q b:ℂ)*
        (numeratorPointKernel p a (1-b):ℂ) := by
    rw [←numeratorExpGenerator_operator_eq_pointKernel]
    unfold finiteDifferentialOperator
    simp_rw [numeratorExpGenerator_iteratedDeriv]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  apply intervalIntegral.integral_congr
  intro a _
  dsimp only
  have hib (r : Fin 5) : IntervalIntegrable (fun b:ℝ => (p r:ℂ)*
      ((polynomialIntervalProfile η P a:ℂ)*(polynomialIntervalProfile η Q b:ℂ)*
        numeratorExpMomentDerivative r.val a (1-b) 0)) volume 0 η := by
    exact ((hc r).comp (continuous_const.prodMk continuous_id :
      Continuous (fun b:ℝ=>(a,b)))).intervalIntegrable 0 η
  rw [←intervalIntegral.integral_finsetSum (fun r _ => hib r)]
  simp_rw [he]

theorem vReflectedPolynomialJ_operator_eq_weightedNumerator (p : Fin 5→ℝ)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (P Q : ℝ[X]) :
    finiteDifferentialOperator 4 (fun r=>(p r:ℂ)) (vReflectedPolynomialJ η P Q) 0 =
      Complex.ofReal (weightedNumeratorPointKernel p η P Q) := by
  rw [vReflectedPolynomialJ_eq_weightedNumeratorExpGenerator η hη hηu P Q]
  exact weightedNumeratorExpGenerator_operator_eq_weightedPointKernel p η P Q

theorem polynomialIntervalProfile_eq_zeroExtended {η a : ℝ} (P : ℝ[X])
    (ha : a∈Ioo 0 η) :
    polynomialIntervalProfile η P a = zeroExtendedPolynomialProfile η P a := by
  have hm : a∈Ico 0 η := ⟨ha.1.le,ha.2⟩
  simp only [zeroExtendedPolynomialProfile,Set.indicator_of_mem hm,polynomialIntervalProfile]

theorem polarPolynomialBilinearJ_eq_double_profileIntegral
    (η : ℝ) (hη : 0<η) (P Q : ℝ[X]) (z : ℂ) :
    polarPolynomialBilinearJ η P Q z =
      ∫ a in (0:ℝ)..η, ∫ b in (0:ℝ)..η,
        (zeroExtendedPolynomialProfile η P a:ℂ)*(zeroExtendedPolynomialProfile η Q b:ℂ)*
          polarJ a b z := by
  rw [polarPolynomialBilinearJ_eq_weightedPolarJ]
  unfold weightedPolarJ
  apply intervalIntegral.integral_congr_Ioo_of_le hη.le
  intro a ha
  apply intervalIntegral.integral_congr_Ioo_of_le hη.le
  intro b hb
  dsimp only
  rw [polynomialIntervalProfile_eq_zeroExtended P ha,polynomialIntervalProfile_eq_zeroExtended Q hb]

theorem weightedNumeratorPointKernel_eq_double_profileIntegral
    (p : Fin 5→ℝ) (η : ℝ) (hη : 0<η) (P Q : ℝ[X]) :
    weightedNumeratorPointKernel p η P Q =
      ∫ a in (0:ℝ)..η, ∫ b in (0:ℝ)..η,
        zeroExtendedPolynomialProfile η P a*zeroExtendedPolynomialProfile η Q b*
          numeratorPointKernel p a (1-b) := by
  unfold weightedNumeratorPointKernel
  apply intervalIntegral.integral_congr_Ioo_of_le hη.le
  intro a ha
  apply intervalIntegral.integral_congr_Ioo_of_le hη.le
  intro b hb
  dsimp only
  rw [polynomialIntervalProfile_eq_zeroExtended P ha,polynomialIntervalProfile_eq_zeroExtended Q hb]

end
end Sechstmoment
