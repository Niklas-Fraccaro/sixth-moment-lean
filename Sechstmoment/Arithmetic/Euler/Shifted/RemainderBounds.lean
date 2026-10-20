import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.PSeries
import Mathlib.Tactic
import Sechstmoment.Arithmetic.Euler.Shifted.Tail


namespace Sechstmoment

open Real Complex Filter
open scoped BigOperators

noncomputable section

theorem finitePolarProduct_norm_le {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    {y : ℝ} (_hy : 0 ≤ y) (hw : ∀ i ∈ s, ‖w i‖ ≤ y) :
    ‖∏ i ∈ s, (1-w i)‖ ≤ (1+y)^s.card := by
  calc
    _ ≤ ∏ i ∈ s, ‖1-w i‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _i ∈ s, (1+y) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact norm_nonneg _
      · intro i hi
        exact (norm_sub_le _ _).trans (by simpa using add_le_add_left (hw i hi) 1)
    _ = _ := by simp

theorem finitePolarProduct_sub_one_norm_le {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    {y : ℝ} (hy : 0 ≤ y) (hw : ∀ i ∈ s, ‖w i‖ ≤ y) :
    ‖(∏ i ∈ s, (1-w i))-1‖ ≤ s.card*y*(1+y)^s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hwi := hw i (Finset.mem_insert_self _ _)
    have hws : ∀ j ∈ s, ‖w j‖ ≤ y := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hident : (1-w i)*(∏ j ∈ s, (1-w j))-1 =
        ((∏ j ∈ s, (1-w j))-1)-w i*(∏ j ∈ s, (1-w j)) := by ring
    rw [Finset.prod_insert hi, hident, Finset.card_insert_of_notMem hi]
    calc
      _ ≤ ‖(∏ j ∈ s, (1-w j))-1‖ + ‖w i*(∏ j ∈ s, (1-w j))‖ := norm_sub_le _ _
      _ ≤ s.card*y*(1+y)^s.card + y*(1+y)^s.card := by
        rw [norm_mul]
        exact add_le_add (ih hws)
          (mul_le_mul hwi (finitePolarProduct_norm_le s w hy hws) (norm_nonneg _) hy)
      _ ≤ (↑(s.card+1):ℝ)*y*(1+y)^(s.card+1) := by
        rw [pow_succ (1+y) s.card, Nat.cast_add, Nat.cast_one]
        have hpow : 0 ≤ (1+y)^s.card := by positivity
        nlinarith [mul_nonneg hy hpow, mul_nonneg (Nat.cast_nonneg s.card) hy]

theorem finitePolarProduct_linear_error_norm_le {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    {y : ℝ} (hy : 0 ≤ y) (hw : ∀ i ∈ s, ‖w i‖ ≤ y) :
    ‖(∏ i ∈ s, (1-w i))-1+(∑ i ∈ s, w i)‖ ≤
      (s.card:ℝ)^2*y^2*(1+y)^s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hwi := hw i (Finset.mem_insert_self _ _)
    have hws : ∀ j ∈ s, ‖w j‖ ≤ y := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hident : (1-w i)*(∏ j ∈ s, (1-w j))-1+(w i+∑ j ∈ s, w j) =
        ((∏ j ∈ s, (1-w j))-1+∑ j ∈ s, w j)-
          w i*((∏ j ∈ s, (1-w j))-1) := by ring
    rw [Finset.prod_insert hi, Finset.sum_insert hi, hident, Finset.card_insert_of_notMem hi]
    calc
      _ ≤ ‖(∏ j ∈ s, (1-w j))-1+∑ j ∈ s, w j‖ +
          ‖w i*((∏ j ∈ s, (1-w j))-1)‖ := norm_sub_le _ _
      _ ≤ (s.card:ℝ)^2*y^2*(1+y)^s.card + y*(s.card*y*(1+y)^s.card) := by
        rw [norm_mul]
        exact add_le_add (ih hws)
          (mul_le_mul hwi (finitePolarProduct_sub_one_norm_le s w hy hws)
            (norm_nonneg _) hy)
      _ ≤ (↑(s.card+1):ℝ)^2*y^2*(1+y)^(s.card+1) := by
        rw [pow_succ (1+y) s.card, Nat.cast_add, Nat.cast_one]
        have hpow : 0 ≤ (1+y)^s.card := by positivity
        have hn : (0:ℝ) ≤ s.card := Nat.cast_nonneg _
        have h1 : (s.card:ℝ)^2+s.card ≤ ((s.card:ℝ)+1)^2 := by nlinarith
        have h2 := mul_le_mul_of_nonneg_right h1
          (mul_nonneg (sq_nonneg y) hpow)
        have h3 : 0 ≤ ((s.card:ℝ)+1)^2*y^2*(1+y)^s.card := by positivity
        nlinarith [mul_nonneg hy h3]

theorem diagonalPolarRemainder_norm_le {a b : Fin 3 → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : ∀ i : Fin 3, ‖a i‖ ≤ r) (hb : ∀ i : Fin 3, ‖b i‖ ≤ r)
    {x : ℂ} (hx : r^2*‖x‖ ≤ 1/2) :
    ‖(∏ ij : Fin 3 × Fin 3, (1-a ij.1*b ij.2*x)) *
      (∑' m : ℕ, triplePrimePowerCoefficient a m *
        triplePrimePowerCoefficient b m * x^m)-1‖ ≤ 2000000*(r^2*‖x‖)^2 := by
  let y : ℝ := r^2*‖x‖
  let w : Fin 3 × Fin 3 → ℂ := fun ij => a ij.1*b ij.2*x
  let P : ℂ := ∏ ij : Fin 3 × Fin 3, (1-w ij)
  let S : ℂ := ∑ ij : Fin 3 × Fin 3, w ij
  let D : ℂ := ∑' m : ℕ, triplePrimePowerCoefficient a m *
    triplePrimePowerCoefficient b m * x^m
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hwy : ∀ ij : Fin 3 × Fin 3, ‖w ij‖ ≤ y := by
    intro ij
    dsimp [w, y]
    rw [norm_mul, norm_mul]
    calc
      _ ≤ r*r*‖x‖ := by gcongr <;> first | exact ha _ | exact hb _
      _ = _ := by ring
  have hpow : (1+y)^9 ≤ 512 := by
    calc
      _ ≤ (2:ℝ)^9 := by gcongr; dsimp [y]; linarith
      _ = _ := by norm_num
  have hP : ‖P‖ ≤ 512 := by
    have h : ‖P‖ ≤ (1+y)^9 := by
      simpa only [P, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using
        finitePolarProduct_norm_le Finset.univ w hy (fun i _ => hwy i)
    exact h.trans hpow
  have hP1 : ‖P-1‖ ≤ 4608*y := by
    have h := finitePolarProduct_sub_one_norm_le Finset.univ w hy (fun i _ => hwy i)
    norm_num only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_ofNat] at h
    change ‖P-1‖ ≤ 9*y*(1+y)^9 at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 9*y)])
  have hE : ‖P-1+S‖ ≤ 41472*y^2 := by
    have h := finitePolarProduct_linear_error_norm_le Finset.univ w hy (fun i _ => hwy i)
    norm_num only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_ofNat] at h
    change ‖P-1+S‖ ≤ 81*y^2*(1+y)^9 at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 81*y^2)])
  have hS : ‖S‖ ≤ 9*y := by
    calc
      _ ≤ ∑ ij : Fin 3 × Fin 3, ‖w ij‖ := norm_sum_le _ _
      _ ≤ ∑ _ij : Fin 3 × Fin 3, y := Finset.sum_le_sum (fun ij _ => hwy ij)
      _ = _ := by norm_num
  have hSident : S = (∑ i : Fin 3, a i)*(∑ j : Fin 3, b j)*x := by
    dsimp [S, w]
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have hR : ‖D-1-S‖ ≤ 3744*y^2 := by
    rw [hSident]
    exact diagonalPrimeSeries_sub_linear_norm_le hr ha hb hx
  have hid : P*D-1 = (P-1+S)+(P-1)*S+P*(D-1-S) := by ring
  change ‖P*D-1‖ ≤ 2000000*y^2
  rw [hid]
  calc
    _ ≤ ‖P-1+S‖+‖(P-1)*S‖+‖P*(D-1-S)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 41472*y^2+(4608*y)*(9*y)+512*(3744*y^2) := by
      simp only [norm_mul]
      gcongr
    _ ≤ _ := by nlinarith [sq_nonneg y]

end

end Sechstmoment
