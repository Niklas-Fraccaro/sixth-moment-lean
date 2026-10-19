import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Sechstmoment.Analysis.Integration.BoxMoments
import Sechstmoment.Certificate.Kernels.Balanced.Inner

namespace Sechstmoment

open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Coefficients of the actual product `p(Z - shift) q(Z + shift)`. -/
noncomputable def minusBoxCoefficient (p q : Fin 5 → ℝ) (shift : ℝ) : Fin 9 → ℝ :=
  productCoefficient (shiftedCoefficient p (-shift) 1) (shiftedCoefficient q shift 1)

theorem minusBox_integrand_polynomial (p q : Fin 5 → ℝ) (shift Z : ℝ) :
    evalDegreeFour p (Z - shift) * evalDegreeFour q (Z + shift) =
      ∑ k : Fin 9, minusBoxCoefficient p q shift k * Z ^ k.val := by
  have hp := shiftedPolynomial_exact p (-shift) 1 Z
  have hq := shiftedPolynomial_exact q shift 1 Z
  have he₁ : -shift + 1 * Z = Z - shift := by ring
  have he₂ : shift + 1 * Z = Z + shift := by ring
  rw [he₁] at hp
  rw [he₂] at hq
  rw [hp, hq]
  exact polynomialProduct_exact _ _ Z

/-- Finite linearity of the three oriented integrals for polynomials in `x+y+z`. -/
theorem boxIntegral_finite_polynomial {n : ℕ} (c : Fin n → ℝ) (r s t : ℝ) :
    boxIntegral r s t (fun x y z => ∑ k : Fin n, c k * (x + y + z) ^ k.val) =
      ∑ k : Fin n, c k * boxIntegral r s t (fun x y z => (x + y + z) ^ k.val) := by
  have hcz (k : Fin n) : Continuous (fun p : ℝ × ℝ =>
      ∫ z in -(t / 2)..t / 2, (p.1 + p.2 + z) ^ k.val) := by
    fun_prop
  have hcy (k : Fin n) : Continuous (fun x : ℝ =>
      ∫ y in -(s / 2)..s / 2, ∫ z in -(t / 2)..t / 2, (x + y + z) ^ k.val) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hcz k
  have hz (x y : ℝ) :
      (∫ z in -(t / 2)..t / 2, ∑ k : Fin n, c k * (x + y + z) ^ k.val) =
        ∑ k : Fin n, c k * ∫ z in -(t / 2)..t / 2, (x + y + z) ^ k.val := by
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_const_mul]
    · intro k _
      apply Continuous.intervalIntegrable
      fun_prop
  have hy (x : ℝ) :
      (∫ y in -(s / 2)..s / 2,
        ∑ k : Fin n, c k * ∫ z in -(t / 2)..t / 2, (x + y + z) ^ k.val) =
      ∑ k : Fin n, c k * ∫ y in -(s / 2)..s / 2,
        ∫ z in -(t / 2)..t / 2, (x + y + z) ^ k.val := by
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_const_mul]
    · intro k _
      exact (continuous_const.mul ((hcz k).comp
        (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
  unfold boxIntegral
  simp_rw [hz, hy]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul]
  · intro k _
    exact (continuous_const.mul (hcy k)).intervalIntegrable _ _

/-- The unnormalized box integral that occurs in the minus kernel. -/
noncomputable def minusBoxIntegral (p q : Fin 5 → ℝ) (shift r s t : ℝ) : ℝ :=
  boxIntegral r s t (fun x y z =>
    evalDegreeFour p (x + y + z - shift) * evalDegreeFour q (x + y + z + shift))

theorem minusBoxIntegral_all_moments (p q : Fin 5 → ℝ) (shift r s t : ℝ) :
    minusBoxIntegral p q shift r s t =
      ∑ k : Fin 9, minusBoxCoefficient p q shift k *
        boxIntegral r s t (fun x y z => (x + y + z) ^ k.val) := by
  unfold minusBoxIntegral
  simp_rw [minusBox_integrand_polynomial]
  exact boxIntegral_finite_polynomial _ r s t

theorem shiftedCoefficient_continuous (p : Fin 5 → ℝ) (sign : ℝ) (k : Fin 5) :
    Continuous (fun delta : ℝ => shiftedCoefficient p delta sign k) := by
  unfold shiftedCoefficient
  apply continuous_finsetSum
  intro r _
  split_ifs
  · fun_prop
  · exact continuous_const

theorem minusBoxCoefficient_continuous (p q : Fin 5 → ℝ) (k : Fin 9) :
    Continuous (fun shift : ℝ => minusBoxCoefficient p q shift k) := by
  unfold minusBoxCoefficient productCoefficient
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  split_ifs
  · exact ((shiftedCoefficient_continuous p 1 i).comp continuous_neg).mul
      (shiftedCoefficient_continuous q 1 j)
  · exact continuous_const

/-- Exact even moments; `m` is half the degree, so each summand has degree `2m+3`. -/
noncomputable def minusBoxEvenMoment (m : ℕ) (r s t : ℝ) : ℝ :=
  (Nat.factorial (2 * m) : ℝ) / (2 : ℝ) ^ (2 * m) *
    ∑ l1 : Fin (m + 1), ∑ l2 : Fin (m + 1), ∑ l3 : Fin (m + 1),
      if l1.val + l2.val + l3.val = m then
        r ^ (2 * l1.val + 1) * s ^ (2 * l2.val + 1) * t ^ (2 * l3.val + 1) /
          ((Nat.factorial (2 * l1.val + 1) : ℝ) *
            Nat.factorial (2 * l2.val + 1) * Nat.factorial (2 * l3.val + 1))
      else 0

theorem minusBox_even_moment (m : Fin 5) (r s t : ℝ) :
    boxIntegral r s t (fun x y z => (x + y + z) ^ (2 * m.val)) =
      minusBoxEvenMoment m.val r s t := by
  fin_cases m
  · change boxIntegral r s t (fun x y z => (x + y + z) ^ 0) = minusBoxEvenMoment 0 r s t
    rw [box_power_0]
    norm_num [minusBoxEvenMoment, Fin.sum_univ_succ]
  · change boxIntegral r s t (fun x y z => (x + y + z) ^ 2) = minusBoxEvenMoment 1 r s t
    rw [box_power_2]
    norm_num [minusBoxEvenMoment, Fin.sum_univ_succ]
    ring
  · change boxIntegral r s t (fun x y z => (x + y + z) ^ 4) = minusBoxEvenMoment 2 r s t
    rw [box_power_4]
    norm_num [minusBoxEvenMoment, Fin.sum_univ_succ]
    ring
  · change boxIntegral r s t (fun x y z => (x + y + z) ^ 6) = minusBoxEvenMoment 3 r s t
    rw [box_power_6]
    norm_num [minusBoxEvenMoment, Fin.sum_univ_succ]
    ring
  · change boxIntegral r s t (fun x y z => (x + y + z) ^ 8) = minusBoxEvenMoment 4 r s t
    rw [box_power_8]
    norm_num [minusBoxEvenMoment, Fin.sum_univ_succ]
    ring

theorem continuous_minusBoxEvenMoment (m : ℕ) :
    Continuous (fun p : ℝ × ℝ × ℝ => minusBoxEvenMoment m p.1 p.2.1 p.2.2) := by
  unfold minusBoxEvenMoment
  apply continuous_const.mul
  apply continuous_finsetSum
  intro l1 _
  apply continuous_finsetSum
  intro l2 _
  apply continuous_finsetSum
  intro l3 _
  by_cases h : l1.val + l2.val + l3.val = m <;> simp only [h, ite_true, ite_false]
  all_goals fun_prop

theorem minusBoxEvenMoment_homogeneous (m : ℕ) (q r s t : ℝ) :
    minusBoxEvenMoment m (q * r) (q * s) (q * t) =
      q ^ (2 * m + 3) * minusBoxEvenMoment m r s t := by
  unfold minusBoxEvenMoment
  rw [mul_left_comm (q ^ (2 * m + 3))]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l1 _
  apply Finset.sum_congr rfl
  intro l2 _
  apply Finset.sum_congr rfl
  intro l3 _
  by_cases h : l1.val + l2.val + l3.val = m
  · simp only [h, ite_true, mul_pow]
    have hq : q ^ (2 * l1.val + 1) * q ^ (2 * l2.val + 1) *
        q ^ (2 * l3.val + 1) = q ^ (2 * m + 3) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    calc
      q ^ (2 * l1.val + 1) * r ^ (2 * l1.val + 1) *
          (q ^ (2 * l2.val + 1) * s ^ (2 * l2.val + 1)) *
          (q ^ (2 * l3.val + 1) * t ^ (2 * l3.val + 1)) /
          ((Nat.factorial (2 * l1.val + 1) : ℝ) *
            Nat.factorial (2 * l2.val + 1) * Nat.factorial (2 * l3.val + 1)) =
        (q ^ (2 * l1.val + 1) * q ^ (2 * l2.val + 1) * q ^ (2 * l3.val + 1)) *
          (r ^ (2 * l1.val + 1) * s ^ (2 * l2.val + 1) * t ^ (2 * l3.val + 1) /
            ((Nat.factorial (2 * l1.val + 1) : ℝ) *
              Nat.factorial (2 * l2.val + 1) * Nat.factorial (2 * l3.val + 1))) := by ring
      _ = _ := by rw [hq]
  · simp only [h, ite_false, mul_zero]

def minusEvenIndex (m : Fin 5) : Fin 9 := ⟨2 * m.val, by omega⟩

theorem minusBoxIntegral_polynomial (p q : Fin 5 → ℝ) (shift r s t : ℝ) :
    minusBoxIntegral p q shift r s t =
      ∑ m : Fin 5, minusBoxCoefficient p q shift (minusEvenIndex m) *
        minusBoxEvenMoment m.val r s t := by
  rw [minusBoxIntegral_all_moments]
  calc
    _ = ∑ m : Fin 5, minusBoxCoefficient p q shift (minusEvenIndex m) *
        boxIntegral r s t (fun x y z => (x + y + z) ^ (2 * m.val)) := by
      have hodd₁ : boxIntegral r s t (fun x y z => x + y + z) = 0 := by
        simpa only [pow_one] using box_power_1 r s t
      norm_num [Fin.sum_univ_succ, minusEvenIndex,
        hodd₁, box_power_3, box_power_5, box_power_7]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      rw [minusBox_even_moment]

theorem minusBoxIntegral_continuous (p q : Fin 5 → ℝ) :
    Continuous (fun v : ℝ × ℝ × ℝ × ℝ =>
      minusBoxIntegral p q v.1 v.2.1 v.2.2.1 v.2.2.2) := by
  simp_rw [minusBoxIntegral_polynomial]
  apply continuous_finsetSum
  intro m _
  apply Continuous.mul
  · exact (minusBoxCoefficient_continuous p q (minusEvenIndex m)).comp continuous_fst
  · exact (continuous_minusBoxEvenMoment m.val).comp continuous_snd

theorem minusBoxIntegral_continuous_comp {α : Type*} [TopologicalSpace α]
    (p q : Fin 5 → ℝ) {shift r s t : α → ℝ} (hshift : Continuous shift)
    (hr : Continuous r) (hs : Continuous s) (ht : Continuous t) :
    Continuous (fun x => minusBoxIntegral p q (shift x) (r x) (s x) (t x)) := by
  exact (minusBoxIntegral_continuous p q).comp
    (hshift.prodMk (hr.prodMk (hs.prodMk ht)))

end Sechstmoment
