import Sechstmoment.Numerator.V.Chi.PolynomialBound
import Sechstmoment.Zeta.Amplifiers


namespace Sechstmoment.Source
open Complex Real Set
open scoped Topology BigOperators
noncomputable section

def profileContourMass (T a : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range ⌊T^a⌋₊, |f (Real.log (n+1 : ℝ)/Real.log T)| *(n+1 : ℝ)

theorem profileContourMass_nonneg (T a : ℝ) (f : ℝ → ℝ) : 0 ≤ profileContourMass T a f := by
  apply Finset.sum_nonneg
  intro n _
  positivity

theorem profileDirichletSum_entire_of_supported {T : ℝ} (hT : 1 < T) (a : ℝ)
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, a < x → f x = 0) :
    Differentiable ℂ (profileDirichletSum T f) := by
  have he : profileDirichletSum T f = fun s : ℂ =>
      ∑ n ∈ Finset.range ⌊T^a⌋₊,
        (f (Real.log (n+1 : ℝ)/Real.log T) : ℂ)/(n+1 : ℂ)^s :=
    funext (profileDirichletSum_eq_finite hT a f hf)
  rw [he]
  apply Differentiable.fun_sum
  intro n _ s
  have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact (differentiableAt_const (f (Real.log (n+1 : ℝ)/Real.log T) : ℂ)).div (differentiableAt_id.const_cpow (Or.inl hn))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hn))

theorem profileDirichletSum_one_sub_norm_le_mass {T : ℝ} (hT : 1 < T) (a : ℝ)
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, a < x → f x = 0) {s : ℂ} (hs : s.re ≤ 2) :
    ‖profileDirichletSum T f (1-s)‖ ≤ profileContourMass T a f := by
  rw [profileDirichletSum_eq_finite hT a f hf]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  have hn : (0 : ℝ) < n+1 := by positivity
  have hn1 : (1 : ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnorm : ‖(n+1 : ℂ)^(1-s)‖ = (n+1 : ℝ)^(1-s.re) := by
    have he : (n+1 : ℂ) = ((n+1 : ℝ) : ℂ) := by push_cast; rfl
    rw [he,Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp only [sub_re,one_re]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,hnorm]
  calc
    _ = |f (Real.log (n+1 : ℝ)/Real.log T)| *(n+1 : ℝ)^(s.re-1) := by
      rw [show s.re-1 = -(1-s.re) by ring,Real.rpow_neg hn.le]
      rfl
    _ ≤ |f (Real.log (n+1 : ℝ)/Real.log T)| *(n+1 : ℝ)^((1 : ℝ)) := by
      gcongr
      linarith
    _ = _ := by rw [Real.rpow_one]

theorem profileContourMass_bound {T a B : ℝ} (hT : 1 < T)
    (f : ℝ → ℝ) (hB : 0 ≤ B) (hf : ∀ x ∈ Icc (0 : ℝ) a, |f x| ≤ B) :
    profileContourMass T a f ≤ B*T^(2*a) := by
  have hTpos : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hX : 0 ≤ T^a := (Real.rpow_pos_of_pos hTpos a).le
  have hfloor : (⌊T^a⌋₊ : ℝ) ≤ T^a := Nat.floor_le hX
  have hpoint (n : ℕ) (hn : n ∈ Finset.range ⌊T^a⌋₊) :
      |f (Real.log (n+1 : ℝ)/Real.log T)| *(n+1 : ℝ) ≤ B*T^a := by
    have hn' : n+1 ≤ ⌊T^a⌋₊ := by simp only [Finset.mem_range] at hn; omega
    have hnR : (n+1 : ℝ) ≤ (⌊T^a⌋₊ : ℝ) := by exact_mod_cast hn'
    have hnX : (n+1 : ℝ) ≤ T^a := hnR.trans hfloor
    have hn0 : (0 : ℝ) < n+1 := by positivity
    have hx0 : 0 ≤ Real.log (n+1 : ℝ)/Real.log T :=
      div_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])) hL.le
    have hxa : Real.log (n+1 : ℝ)/Real.log T ≤ a := by
      apply (div_le_iff₀ hL).mpr
      have hl := Real.log_le_log hn0 hnX
      rwa [Real.log_rpow hTpos] at hl
    exact mul_le_mul (hf _ ⟨hx0,hxa⟩) hnX (by positivity) hB
  calc
    _ ≤ ∑ _n ∈ Finset.range ⌊T^a⌋₊, B*T^a := Finset.sum_le_sum hpoint
    _ = (⌊T^a⌋₊ : ℝ)*(B*T^a) := by simp
    _ ≤ (T^a)*(B*T^a) := mul_le_mul_of_nonneg_right hfloor (by positivity)
    _ = B*T^(2*a) := by rw [show 2*a = a+a by ring,Real.rpow_add hTpos]; ring

end
end Sechstmoment.Source
