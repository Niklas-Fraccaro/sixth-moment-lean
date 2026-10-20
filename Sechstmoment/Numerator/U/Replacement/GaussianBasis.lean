import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic
import Sechstmoment.Numerator.Polar.PoleKiller
import Sechstmoment.Zeta.AFE.Four.Specification


namespace Sechstmoment.Source
open Complex Polynomial
open scoped BigOperators
open Classical
noncomputable section

def polarPoleCoefficientPolynomial (T : ℝ) (σ : MomentShifts) : ℂ[X] :=
  ∏ k : PurePolarIndex, (1-C ((purePolarRoot T σ k)^2)⁻¹*X)

def fixedGaussianBasis (i : Fin 25) (z : ℂ) : ℂ :=
  if i=0 then exp (z^2) else exp (z^2)*(1+z^(2*i.val))

def polarPoleBasisWeights (T : ℝ) (σ : MomentShifts) (i : Fin 25) : ℂ :=
  if i=0 then 1-∑ j : Fin 24, (polarPoleCoefficientPolynomial T σ).coeff (j.val+1)
  else (polarPoleCoefficientPolynomial T σ).coeff i.val

private theorem linearProduct_natDegree_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ) :
    (∏ k ∈ s, (1-C (c k)*X)).natDegree ≤ s.card := by
  calc
    _ ≤ ∑ k ∈ s, (1-C (c k)*X).natDegree :=
      Polynomial.natDegree_prod_le s (fun k => 1-C (c k)*X)
    _ ≤ ∑ _k ∈ s, 1 := by
      apply Finset.sum_le_sum
      intro k hk
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    _ = s.card := by simp

theorem polarPoleCoefficientPolynomial_natDegree_le (T : ℝ) (σ : MomentShifts) :
    (polarPoleCoefficientPolynomial T σ).natDegree ≤ 24 := by
  have h := linearProduct_natDegree_le (Finset.univ : Finset PurePolarIndex)
    (fun k => ((purePolarRoot T σ k)^2)⁻¹)
  have hc : (Finset.univ : Finset PurePolarIndex).card = 24 := by simp [PurePolarIndex]
  rw [hc] at h
  exact h

@[simp] theorem polarPoleCoefficientPolynomial_coeff_zero (T : ℝ) (σ : MomentShifts) :
    (polarPoleCoefficientPolynomial T σ).coeff 0 = 1 := by
  simp [Polynomial.coeff_zero_eq_eval_zero, polarPoleCoefficientPolynomial,
    Polynomial.eval_prod]

theorem polarPoleKiller_polynomial_eval (T : ℝ) (σ : MomentShifts) (z : ℂ) :
    polarPoleKiller T σ z = exp (z^2)*(polarPoleCoefficientPolynomial T σ).eval (z^2) := by
  unfold polarPoleKiller polarPoleCoefficientPolynomial
  rw [Polynomial.eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  by_cases hr : purePolarRoot T σ k=0
  · simp [polarPoleKillingFactor, hr]
  · simp only [polarPoleKillingFactor, ite_eq_right hr, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      div_eq_mul_inv]
    ring

@[simp] theorem fixedGaussianBasis_zero (i : Fin 25) : fixedGaussianBasis i 0 = 1 := by
  by_cases hi : i=0
  · simp [fixedGaussianBasis, hi]
  · have hn : 2*i.val ≠ 0 := by
      have hval : i.val ≠ 0 := by intro h; exact hi (Fin.ext h)
      omega
    simp [fixedGaussianBasis, hi, hn]

theorem fixedGaussianBasis_even (i : Fin 25) (z : ℂ) :
    fixedGaussianBasis i (-z) = fixedGaussianBasis i z := by
  simp [fixedGaussianBasis, pow_mul]

theorem fixedGaussianBasis_differentiable (i : Fin 25) :
    Differentiable ℂ (fixedGaussianBasis i) := by
  unfold fixedGaussianBasis
  split_ifs <;> fun_prop

theorem polarPoleBasisWeights_sum (T : ℝ) (σ : MomentShifts) :
    ∑ i : Fin 25, polarPoleBasisWeights T σ i = 1 := by
  rw [Fin.sum_univ_succ]
  simp [polarPoleBasisWeights]

theorem linearProduct_coeff_norm_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℂ) (n : ℕ) :
    ‖(∏ k ∈ s, (1-C (c k)*X)).coeff n‖ ≤ ∏ k ∈ s, (1+‖c k‖) := by
  induction s using Finset.induction_on generalizing n with
  | empty =>
      by_cases hn : n=0
      · simp [Polynomial.coeff_one, hn]
      · simp [Polynomial.coeff_one, hn]
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      let p : ℂ[X] := ∏ k ∈ s, (1-C (c k)*X)
      have hB : 0 ≤ ∏ k ∈ s, (1+‖c k‖) :=
        Finset.prod_nonneg (fun k hk => by positivity)
      have he : (1-C (c a)*X)*p = p-(C (c a)*p)*X := by ring
      change ‖((1-C (c a)*X)*p).coeff n‖ ≤ _
      rw [he]
      cases n with
      | zero =>
          rw [Polynomial.coeff_sub, Polynomial.coeff_mul_X_zero, sub_zero]
          calc
            _ ≤ ∏ k ∈ s, (1+‖c k‖) := ih 0
            _ ≤ (1+‖c a‖)*∏ k ∈ s, (1+‖c k‖) := by
              have hc := norm_nonneg (c a)
              nlinarith
      | succ n =>
          rw [Polynomial.coeff_sub, Polynomial.coeff_mul_X, Polynomial.coeff_C_mul]
          calc
            _ ≤ ‖p.coeff (n+1)‖+‖c a*p.coeff n‖ := norm_sub_le _ _
            _ = ‖p.coeff (n+1)‖+‖c a‖*‖p.coeff n‖ := by rw [norm_mul]
            _ ≤ (∏ k ∈ s, (1+‖c k‖))+‖c a‖*∏ k ∈ s, (1+‖c k‖) :=
              add_le_add (ih (n+1)) (mul_le_mul_of_nonneg_left (ih n) (norm_nonneg _))
            _ = _ := by ring

theorem polarPoleCoefficientPolynomial_coeff_norm_le (T : ℝ) (σ : MomentShifts) (n : ℕ) :
    ‖(polarPoleCoefficientPolynomial T σ).coeff n‖ ≤
      ∏ k : PurePolarIndex, (1+‖((purePolarRoot T σ k)^2)⁻¹‖) :=
  linearProduct_coeff_norm_le Finset.univ (fun k => ((purePolarRoot T σ k)^2)⁻¹) n

theorem polarPoleBasisWeights_norm_sum_le (T : ℝ) (σ : MomentShifts) :
    ∑ i : Fin 25, ‖polarPoleBasisWeights T σ i‖ ≤
      1+48*∏ k : PurePolarIndex, (1+‖((purePolarRoot T σ k)^2)⁻¹‖) := by
  let B : ℝ := ∏ k : PurePolarIndex, (1+‖((purePolarRoot T σ k)^2)⁻¹‖)
  have hsum : (∑ j : Fin 24, ‖(polarPoleCoefficientPolynomial T σ).coeff (j.val+1)‖) ≤
      24*B := by
    calc
      _ ≤ ∑ _j : Fin 24, B := Finset.sum_le_sum
        (fun j hj => polarPoleCoefficientPolynomial_coeff_norm_le T σ (j.val+1))
      _ = 24*B := by simp
  have hzero : ‖1-∑ j : Fin 24, (polarPoleCoefficientPolynomial T σ).coeff (j.val+1)‖ ≤
      1+∑ j : Fin 24, ‖(polarPoleCoefficientPolynomial T σ).coeff (j.val+1)‖ := by
    calc
      _ ≤ ‖(1 : ℂ)‖+‖∑ j : Fin 24, (polarPoleCoefficientPolynomial T σ).coeff (j.val+1)‖ :=
        norm_sub_le _ _
      _ ≤ _ := by
        rw [norm_one]
        exact add_le_add le_rfl (norm_sum_le Finset.univ
          (fun j : Fin 24 => (polarPoleCoefficientPolynomial T σ).coeff (j.val+1)))
  have hw0 : polarPoleBasisWeights T σ 0 =
      1-∑ j : Fin 24, (polarPoleCoefficientPolynomial T σ).coeff (j.val+1) := by
    simp [polarPoleBasisWeights]
  have hws (j : Fin 24) : polarPoleBasisWeights T σ j.succ =
      (polarPoleCoefficientPolynomial T σ).coeff (j.val+1) := by
    simp [polarPoleBasisWeights]
  rw [Fin.sum_univ_succ]
  rw [hw0]
  simp_rw [hws]
  change ‖1-∑ j : Fin 24, (polarPoleCoefficientPolynomial T σ).coeff (j.val+1)‖+
    (∑ j : Fin 24, ‖(polarPoleCoefficientPolynomial T σ).coeff (j.val+1)‖) ≤ 1+48*B
  linarith

theorem polarPoleCoefficientPolynomial_eval_fin (T : ℝ) (σ : MomentShifts) (z : ℂ) :
    (polarPoleCoefficientPolynomial T σ).eval (z^2) =
      1+∑ j : Fin 24, (polarPoleCoefficientPolynomial T σ).coeff (j.val+1)*
        z^(2*(j.val+1)) := by
  rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt
    (polarPoleCoefficientPolynomial_natDegree_le T σ) (by norm_num : 24<25)),
    ← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
  simp [pow_mul]

theorem polarPoleKiller_fixed_basis (T : ℝ) (σ : MomentShifts) :
    polarPoleKiller T σ = finiteAuxiliaryCombination (polarPoleBasisWeights T σ)
      fixedGaussianBasis := by
  ext z
  have hs : finiteAuxiliaryCombination (polarPoleBasisWeights T σ) fixedGaussianBasis z =
      (1-∑ j : Fin 24, (polarPoleCoefficientPolynomial T σ).coeff (j.val+1))*exp (z^2)+
        ∑ j : Fin 24, (polarPoleCoefficientPolynomial T σ).coeff (j.val+1)*
          (exp (z^2)*(1+z^(2*(j.val+1)))) := by
    unfold finiteAuxiliaryCombination
    rw [Fin.sum_univ_succ]
    simp [polarPoleBasisWeights, fixedGaussianBasis]
  rw [polarPoleKiller_polynomial_eval T σ z,
    polarPoleCoefficientPolynomial_eval_fin T σ z, hs]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  have he : ∑ j : Fin 24, (polarPoleCoefficientPolynomial T σ).coeff (j.val+1)*
      (exp (z^2)*z^(2*(j.val+1))) =
    exp (z^2)*∑ j : Fin 24, (polarPoleCoefficientPolynomial T σ).coeff (j.val+1)*
      z^(2*(j.val+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [mul_add] at he
  rw [he]
  ring

end
end Sechstmoment.Source
