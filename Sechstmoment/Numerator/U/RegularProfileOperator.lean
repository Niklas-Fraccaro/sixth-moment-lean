import Sechstmoment.Numerator.Kernels.WeightedIntegral
import Sechstmoment.Numerator.U.MainTerm.RegularProfileGenerator

/-! Differentiation of the actual compact U profile generator.  Every derivative
is proved under both profile integrals, before its degree-four operator is
identified with the literal numerical numerator point kernel. -/

namespace Sechstmoment
open Complex MeasureTheory Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 2000000

attribute [local irreducible] numeratorExpMomentDerivative

/-- The actual derivative family, with both genuine profile integrations. -/
def actualCenteredNumeratorProfileDerivative (n : ℕ) (a b : ℝ)
    (f g : ℝ → ℂ) (Φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  (arithmeticFactor:ℂ)*(∫ x, (Φ x:ℂ))*
    ∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
      f A*g B*numeratorExpMomentDerivative n A B z

theorem actualCenteredNumeratorProfileDerivative_hasDerivAt
    (n : ℕ) (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (z : ℂ) :
    HasDerivAt (actualCenteredNumeratorProfileDerivative n a b f g Φ)
      (actualCenteredNumeratorProfileDerivative (n+1) a b f g Φ z) z := by
  have hc (m : ℕ) : Continuous (fun p : ℂ × (ℝ × ℝ) =>
      f p.2.1*g p.2.2*numeratorExpMomentDerivative m p.2.1 p.2.2 p.1) :=
    ((hf.comp (by fun_prop : Continuous (fun p : ℂ × (ℝ × ℝ) => p.2.1))).mul
      (hg.comp (by fun_prop : Continuous (fun p : ℂ × (ℝ × ℝ) => p.2.2)))).mul
      (numeratorExpMomentDerivative_joint_continuous m)
  have hinner (A : ℝ) (z : ℂ) := complexInterval_hasDerivAt_of_joint_continuity
    (fun z B => f A*g B*numeratorExpMomentDerivative n A B z)
    (fun z B => f A*g B*numeratorExpMomentDerivative (n+1) A B z) z 0 b
    ((hc n).comp (by fun_prop : Continuous (fun p : ℂ × ℝ => (p.1,(A,p.2)))))
    ((hc (n+1)).comp (by fun_prop : Continuous (fun p : ℂ × ℝ => (p.1,(A,p.2)))))
    (fun z B => (numeratorExpMomentDerivative_hasDerivAt n A B z).const_mul (f A*g B))
  have ho (m : ℕ) : Continuous (fun p : ℂ × ℝ =>
      ∫ B in (0:ℝ)..b, f p.2*g B*numeratorExpMomentDerivative m p.2 B p.1) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun p : ℂ × ℝ => fun B : ℝ =>
        f p.2*g B*numeratorExpMomentDerivative m p.2 B p.1)
      ((hc m).comp (by fun_prop : Continuous
        (fun p : (ℂ × ℝ) × ℝ => (p.1.1,(p.1.2,p.2))))) 0 b
  unfold actualCenteredNumeratorProfileDerivative
  exact (complexInterval_hasDerivAt_of_joint_continuity
    (fun z A => ∫ B in (0:ℝ)..b, f A*g B*numeratorExpMomentDerivative n A B z)
    (fun z A => ∫ B in (0:ℝ)..b, f A*g B*numeratorExpMomentDerivative (n+1) A B z)
    z 0 a (ho n) (ho (n+1)) (fun z A => hinner A z)).const_mul _

/-- Ordinary derivatives commute with both actual profile integrals at every
order, including all node and endpoint coincidences. -/
theorem actualCenteredNumeratorProfileGenerator_iteratedDeriv
    (n : ℕ) (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (z : ℂ) :
    iteratedDeriv n (actualCenteredNumeratorProfileGenerator a b f g Φ) z =
      actualCenteredNumeratorProfileDerivative n a b f g Φ z := by
  induction n generalizing z with
  | zero =>
    rw [iteratedDeriv_zero]
    unfold actualCenteredNumeratorProfileGenerator actualCenteredNumeratorProfileDerivative
    simp_rw [← numeratorExpGenerator_iteratedDeriv 0, iteratedDeriv_zero]
  | succ n ih =>
    have he : iteratedDeriv n (actualCenteredNumeratorProfileGenerator a b f g Φ) =
        actualCenteredNumeratorProfileDerivative n a b f g Φ := funext ih
    rw [iteratedDeriv_succ, he]
    exact (actualCenteredNumeratorProfileDerivative_hasDerivAt n a b f g Φ hf hg z).deriv

/-- The genuine degree-four operator is the compact double point-kernel
integral.  All finite-sum interchanges have proved continuous integrands. -/
theorem actualCenteredNumeratorProfileGenerator_operator_eq_compactPointKernel
    (p : Fin 5 → ℝ) (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    finiteDifferentialOperator 4 (fun r => (p r:ℂ))
      (actualCenteredNumeratorProfileGenerator a b f g Φ) 0 =
      (arithmeticFactor:ℂ)*(∫ x, (Φ x:ℂ))*
        ∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
          f A*g B*(numeratorPointKernel p A B:ℂ) := by
  unfold finiteDifferentialOperator
  simp_rw [actualCenteredNumeratorProfileGenerator_iteratedDeriv _ _ _ _ _ _ hf hg]
  unfold actualCenteredNumeratorProfileDerivative
  let M : ℂ := (arithmeticFactor:ℂ)*(∫ x, (Φ x:ℂ))
  change (∑ r : Fin 5, (p r:ℂ)*(M*
    (∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
      f A*g B*numeratorExpMomentDerivative r.val A B 0))) =
    M*(∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b, f A*g B*(numeratorPointKernel p A B:ℂ))
  calc
    _ = M*(∑ r : Fin 5, (p r:ℂ)*
        (∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
          f A*g B*numeratorExpMomentDerivative r.val A B 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      congr 1
      simp_rw [← intervalIntegral.integral_const_mul]
      have hc (r : Fin 5) : Continuous (fun q : ℝ × ℝ => (p r:ℂ)*
          (f q.1*g q.2*numeratorExpMomentDerivative r.val q.1 q.2 0)) :=
        continuous_const.mul (((hf.comp continuous_fst).mul
          (hg.comp continuous_snd)).mul
          ((numeratorExpMomentDerivative_joint_continuous r.val).comp
            (by fun_prop : Continuous (fun q : ℝ × ℝ => ((0:ℂ),q)))))
      rw [← intervalIntegral.integral_finsetSum (fun r _ =>
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (μ := volume) (f := fun A B => (p r:ℂ)*
            (f A*g B*numeratorExpMomentDerivative r.val A B 0))
          (hc r) 0 b).intervalIntegrable 0 a)]
      have he (A B : ℝ) :
          ∑ r : Fin 5, (p r:ℂ)*(f A*g B*numeratorExpMomentDerivative r.val A B 0) =
            f A*g B*(numeratorPointKernel p A B:ℂ) := by
        rw [← numeratorExpGenerator_operator_eq_pointKernel]
        unfold finiteDifferentialOperator
        simp_rw [numeratorExpGenerator_iteratedDeriv]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      apply intervalIntegral.integral_congr
      intro A _
      dsimp only
      have hib (r : Fin 5) : IntervalIntegrable (fun B : ℝ => (p r:ℂ)*
          (f A*g B*numeratorExpMomentDerivative r.val A B 0)) volume 0 b :=
        ((hc r).comp (continuous_const.prodMk continuous_id :
          Continuous (fun B : ℝ => (A,B)))).intervalIntegrable 0 b
      rw [← intervalIntegral.integral_finsetSum (fun r _ => hib r)]
      simp_rw [he]

/-- The actual interior supports justify replacing both oriented compact
profile integrals by their literal global real integrals. -/
theorem smoothInteriorProfile_two_integral_eq_global
    {a b : ℝ} {f g : ℝ → ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (K : ℝ → ℝ → ℝ) :
    (∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b, f A*g B*K A B) =
      ∫ A : ℝ, ∫ B : ℝ, f A*g B*K A B := by
  have hin (A : ℝ) : Function.support (fun B => f A*g B*K A B) ⊆ Ioc 0 b := by
    intro B hB
    have hgB : g B ≠ 0 := by
      intro hz
      exact hB (by simp [hz])
    have hBs := hg.2.2 (subset_tsupport g hgB)
    exact ⟨hBs.1,hBs.2.le⟩
  simp_rw [intervalIntegral.integral_eq_integral_of_support_subset (hin _)]
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro A hA
  have hfA : f A ≠ 0 := by
    intro hz
    exact hA (by simp [hz])
  have hAs := hf.2.2 (subset_tsupport f hfA)
  exact ⟨hAs.1,hAs.2.le⟩

/-- The actual smooth U profile operator recovers exactly the real scalar
profile kernel used in the original certificate. -/
theorem actualCenteredNumeratorProfileGenerator_operator_eq_globalPointKernel
    (p : Fin 5 → ℝ) (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    finiteDifferentialOperator 4 (fun r => (p r:ℂ))
      (actualCenteredNumeratorProfileGenerator a b (fun x => (f x:ℂ))
        (fun x => (g x:ℂ)) Φ) 0 =
      (arithmeticFactor:ℂ)*(∫ x, (Φ x:ℂ))*
        Complex.ofReal (∫ A : ℝ, ∫ B : ℝ, f A*g B*numeratorPointKernel p A B) := by
  rw [actualCenteredNumeratorProfileGenerator_operator_eq_compactPointKernel p a b
    (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ
    (Complex.continuous_ofReal.comp hf.1.continuous)
    (Complex.continuous_ofReal.comp hg.1.continuous)]
  simp_rw [← Complex.ofReal_mul, intervalIntegral.integral_ofReal]
  rw [smoothInteriorProfile_two_integral_eq_global hf hg]

end
end Sechstmoment
