import Mathlib.Tactic
import Sechstmoment.Zeta.Amplifiers

/-! Sharp elementary amplifier bound on Re(s)=1+O(1/log T). The actual
Dirichlet sum is used, with its existing finite-support identity. -/

namespace Sechstmoment.Source
open Complex Real Set
open scoped BigOperators
noncomputable section

theorem profileDirichletSum_one_sub_log_bound {T η a B : ℝ}
    (hT : 1 < T) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (f : ℝ → ℝ) (hfs : ∀ x : ℝ, η < x → f x = 0)
    (hf : ∀ x ∈ Icc (0:ℝ) η, |f x| ≤ B)
    {s : ℂ} (hs : s.re ≤ 1+a/Real.log T) :
    ‖profileDirichletSum T f (1-s)‖ ≤ B*Real.exp (η*a)*T^η := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hX : 0 < T^η := Real.rpow_pos_of_pos hT0 η
  have hfloor : (⌊T^η⌋₊:ℝ) ≤ T^η := Nat.floor_le hX.le
  have hpower : (T^η)^(a/Real.log T) = Real.exp (η*a) := by
    rw [Real.rpow_def_of_pos hX,Real.log_rpow hT0]
    congr 1
    field_simp [hL.ne']
  rw [profileDirichletSum_eq_finite hT η f hfs]
  apply (norm_sum_le _ _).trans
  have hpoint (n : ℕ) (hn : n ∈ Finset.range ⌊T^η⌋₊) :
      ‖(f (Real.log (n+1:ℝ)/Real.log T):ℂ)/(n+1:ℂ)^(1-s)‖ ≤ B*Real.exp (η*a) := by
    have hn1 : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hn0 : (0:ℝ) < n+1 := by positivity
    have hnN : n+1 ≤ ⌊T^η⌋₊ := by simp only [Finset.mem_range] at hn; omega
    have hnX : (n+1:ℝ) ≤ T^η := (by exact_mod_cast hnN : (n+1:ℝ) ≤ (⌊T^η⌋₊:ℝ)).trans hfloor
    have hx0 : 0 ≤ Real.log (n+1:ℝ)/Real.log T :=
      div_nonneg (Real.log_nonneg hn1) hL.le
    have hxη : Real.log (n+1:ℝ)/Real.log T ≤ η := by
      apply (div_le_iff₀ hL).mpr
      have H := Real.log_le_log hn0 hnX
      rwa [Real.log_rpow hT0] at H
    have hnorm : ‖(n+1:ℂ)^(1-s)‖ = (n+1:ℝ)^(1-s.re) := by
      have he : (n+1:ℂ) = ((n+1:ℝ):ℂ) := by push_cast; rfl
      rw [he,Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      simp only [sub_re,one_re]
    have hpow : (n+1:ℝ)^(s.re-1) ≤ Real.exp (η*a) := by
      calc
        _ ≤ (n+1:ℝ)^(a/Real.log T) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ ≤ (T^η)^(a/Real.log T) :=
          Real.rpow_le_rpow hn0.le hnX (div_nonneg ha hL.le)
        _ = _ := hpower
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,hnorm]
    calc
      _ = |f (Real.log (n+1:ℝ)/Real.log T)| * (n+1:ℝ)^(s.re-1) := by
        rw [show s.re-1 = -(1-s.re) by ring,Real.rpow_neg hn0.le]
        rfl
      _ ≤ _ := mul_le_mul (hf _ ⟨hx0,hxη⟩) hpow (Real.rpow_nonneg hn0.le _) hB
  calc
    _ ≤ ∑ _n ∈ Finset.range ⌊T^η⌋₊, B*Real.exp (η*a) := Finset.sum_le_sum hpoint
    _ = (⌊T^η⌋₊:ℝ)*(B*Real.exp (η*a)) := by simp
    _ ≤ (T^η)*(B*Real.exp (η*a)) := mul_le_mul_of_nonneg_right hfloor (by positivity)
    _ = _ := by ring

end
end Sechstmoment.Source
