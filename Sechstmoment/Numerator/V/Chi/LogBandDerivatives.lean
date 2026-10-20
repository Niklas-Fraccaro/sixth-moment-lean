import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Sechstmoment.Analysis.Mellin.FourierCutoffUniform


namespace Sechstmoment.Source
open Complex Real Set
open scoped ContDiff BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem schwartz_scaled_log_derivative_bound (h : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ u ∈ Icc (3/4:ℝ) (5/4),
      ‖iteratedDeriv n (fun y : ℝ => h (-T*Real.log y/(2*Real.pi))) u‖ ≤ C*T^n := by
  let g : ℝ → ℝ := fun u => -Real.log u/(2*Real.pi)
  have hg : ContDiffOn ℝ ∞ g (Ioi 0) := by
    intro u hu
    exact ((Real.contDiffAt_log.mpr (ne_of_gt hu)).neg.div_const _).contDiffWithinAt
  have hb (i : ℕ) : ∃ b : ℝ, ∀ u ∈ Icc (3/4:ℝ) (5/4),
      ‖iteratedFDerivWithin ℝ i g (Ioi 0) u‖ ≤ b := by
    apply isCompact_Icc.exists_bound_of_continuousOn
    exact (hg.continuousOn_iteratedFDerivWithin (by simp) (uniqueDiffOn_Ioi (0:ℝ))).mono
      (fun u hu => by change 0 < u; linarith [hu.1])
  choose b hb using hb
  let B : ℕ → ℝ := fun i => max (b i) 0
  have hB (i : ℕ) : 0 ≤ B i := le_max_right _ _
  let E : ℝ := 1+∑ i ∈ Finset.range (n+1), B i
  have hE : 1 ≤ E := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB i))
  have hE0 : 0 ≤ E := by linarith
  let J : ℝ := ∑ i ∈ Finset.range (n+1), SchwartzMap.seminorm ℂ 0 i h
  have hJ : 0 ≤ J := Finset.sum_nonneg (fun i _ => by positivity)
  let C : ℝ := (n.factorial:ℝ)*J*E^n+1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro T hT u hu
  have hT0 : 0 < T := by linarith
  have hu0 : 0 < u := by linarith [hu.1]
  let F : ℝ → ℂ := fun x => h (T*x)
  have hF : ContDiff ℝ ∞ F := h.smooth'.comp (by fun_prop)
  have hA : ContDiffAt ℝ ∞ (fun y : ℝ => h (-T*Real.log y/(2*Real.pi))) u :=
    h.smooth'.contDiffAt.comp u
      ((contDiffAt_const.mul (Real.contDiffAt_log.mpr hu0.ne')).div_const _)
  have hout (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i F univ (g u)‖ ≤ J*T^n := by
    rw [iteratedFDerivWithin_univ,norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    dsimp only [F]
    rw [iteratedDeriv_comp_const_smul (h.smooth i),norm_smul,norm_pow,
      Real.norm_eq_abs,abs_of_pos hT0]
    have hh : ‖iteratedDeriv i h (T*g u)‖ ≤ J := by
      have H := SchwartzMap.le_seminorm' ℂ 0 i h (T*g u)
      simp only [pow_zero,one_mul] at H
      exact H.trans (Finset.single_le_sum
        (f := fun j => SchwartzMap.seminorm ℂ 0 j h) (fun j _ => by positivity)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
    calc
      _ ≤ T^n*J := mul_le_mul (pow_le_pow_right₀ hT hi) hh (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hin (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i g (Ioi 0) u‖ ≤ E^i := by
    have hbi : B i ≤ E := by
      have H := Finset.single_le_sum (fun j _ => hB j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hin))
      dsimp only [E]
      linarith
    exact ((hb i u hu).trans (le_max_left _ _)).trans
      (hbi.trans (le_self_pow₀ hE (by omega)))
  have H := norm_iteratedFDerivWithin_comp_le hF.contDiffOn hg (by simp)
    uniqueDiffOn_univ (uniqueDiffOn_Ioi (0:ℝ)) (mapsTo_univ _ _) hu0 hout hin
  have he : F ∘ g = fun y : ℝ => h (-T*Real.log y/(2*Real.pi)) := by
    funext y
    dsimp only [F,g,Function.comp_apply]
    congr 1
    ring
  rw [he,norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi (0:ℝ))
      (hA.of_le (by simp)) hu0] at H
  apply H.trans
  dsimp only [C]
  nlinarith [pow_nonneg hT0.le n]

end
end Sechstmoment.Source
