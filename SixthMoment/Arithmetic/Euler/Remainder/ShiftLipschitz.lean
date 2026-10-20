import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import SixthMoment.Arithmetic.Euler.Remainder.UniformMajorant

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace SixthMoment.Source.NoDPGlobalRest
open NoDPLocal NoDPResidues NoDPLocalClosure
open scoped BigOperators
noncomputable section

set_option backward.isDefEq.respectTransparency false in
theorem localCoeff_entire_line (p : Nat.Primes) (v : Fin 4 → ℂ) (j : Fin 8) :
    Differentiable ℂ (fun z : ℂ => localCoeff p (fun k => z * v k) j) := by
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have H (k : Fin 4) : Differentiable ℂ (fun z : ℂ => primeRoot p.val (z * v k)) :=
    (differentiable_id.mul_const (v k)).neg.const_cpow (Or.inl hp)
  have HI : Differentiable ℂ (fun z : ℂ => (primeRoot p.val (z * v 0))⁻¹) :=
    (H 0).inv (fun z => primeRoot_ne_zero p.val p.property.ne_zero _)
  have HN (z : ℂ) := primeRoot_ne_zero p.val p.property.ne_zero (z * v 0)
  fin_cases j <;>
    simp [localCoeff, leftDegree, rightDegree,
      residueRest_10 _ _ _ _ _ (HN _), residueRest_01 _ _ _ _ _ (HN _),
      residueRest_20 _ _ _ _ _ (HN _), residueRest_02 _ _ _ _ _ (HN _),
      residueRest_11 _ _ _ _ _ (HN _), residueRest_21 _ _ _ _ _ (HN _),
      residueRest_12 _ _ _ _ _ (HN _), residueRest_22 _ _ _ _ _ (HN _)] <;>
    (try simp only [restA, restB, restC, restD, restE, div_eq_mul_inv, ← inv_pow]) <;> fun_prop

theorem gamma_entire_line (v : Fin 4 → ℂ) (n : ℕ × ℕ) :
    Differentiable ℂ (fun z : ℂ => gamma (fun k => z * v k) n) := by
  by_cases hn : n ∈ Set.range configIndex
  · obtain ⟨c, rfl⟩ := hn
    simp only [gamma_config, configCoeff]
    exact Differentiable.fun_finsetProd (fun p _ => localCoeff_entire_line p.val v (c.2 p))
  · simp only [gamma_outside _ n hn]
    exact differentiable_const 0

theorem cauchy_half_disk_lipschitz (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (R B : ℝ) (hR : 0 < R) (hB : ∀ w : ℂ, ‖w‖ ≤ R → ‖f w‖ ≤ B)
    (z : ℂ) (hz : ‖z‖ ≤ R/2) :
    ‖f z - f 0‖ ≤ (2*B/R) * ‖z‖ := by
  have HD (w : ℂ) (hw : w ∈ Metric.closedBall (0:ℂ) (R/2)) :
      ‖deriv f w‖ ≤ 2*B/R := by
    have HW : ‖w‖ ≤ R/2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
    have H := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (c := w) (R := R/2) (C := B) (by positivity) hf.diffContOnCl (fun t ht => hB t (by
        have HT : ‖t-w‖ = R/2 := by simpa [Metric.mem_sphere, dist_eq_norm] using ht
        calc
          ‖t‖ ≤ ‖t-w‖+‖w‖ := norm_le_norm_sub_add t w
          _ ≤ R := by linarith))
    convert H using 1 <;> ring
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w (_ : w ∈ Metric.closedBall (0:ℂ) (R/2)) => hf w) HD
    (convex_closedBall (0:ℂ) (R/2))
    (by rw [Metric.mem_closedBall, dist_self]; positivity : (0:ℂ) ∈ Metric.closedBall 0 (R/2))
    (by simpa [Metric.mem_closedBall, dist_zero_right] using hz : z ∈ Metric.closedBall 0 (R/2))
  simpa only [sub_zero] using H

theorem gamma_lipschitz_pointwise (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ : ρ < 1/4) (hs : ‖s‖ ≤ ρ/2) (n : ℕ × ℕ) :
    ‖gamma s n - gamma (fun _ => 0) n‖ ≤ (2 * gammaMajorant ρ n / ρ) * ‖s‖ := by
  by_cases hs0 : s = 0
  · subst s
    change ‖gamma (fun _ => 0) n - gamma (fun _ => 0) n‖ ≤
      (2 * gammaMajorant ρ n / ρ) * ‖(0 : Fin 4 → ℂ)‖
    simp
  have hδ : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hδc : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  let v : Fin 4 → ℂ := fun k => s k / (‖s‖ : ℂ)
  have hv (k : Fin 4) : ‖v k‖ ≤ 1 := by
    dsimp [v]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    exact (div_le_one hδ).mpr (norm_le_pi_norm s k)
  have HB (z : ℂ) (hz : ‖z‖ ≤ ρ) :
      ‖gamma (fun k => z * v k) n‖ ≤ gammaMajorant ρ n :=
    gamma_norm_bound _ ρ hρ0.le hρ (fun k => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hv k) (norm_nonneg z)).trans (by simpa using hz)) n
  have H := cauchy_half_disk_lipschitz (fun z : ℂ => gamma (fun k => z * v k) n)
    (gamma_entire_line v n) ρ (gammaMajorant ρ n) hρ0 HB (‖s‖ : ℂ)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] using hs)
  have HV : (fun k => (‖s‖ : ℂ) * v k) = s := by
    funext k
    dsimp [v]
    field_simp
  simpa only [HV, zero_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] using H

theorem gamma_difference_absolute (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ : ρ < 1/4) (hs : ‖s‖ ≤ ρ/2) :
    Summable (fun n => ‖gamma s n - gamma (fun _ => 0) n‖) := by
  apply ((gammaMajorant_summable ρ hρ).mul_left (2/ρ*‖s‖)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro n
  convert gamma_lipschitz_pointwise s ρ hρ0 hρ hs n using 1 <;> ring

theorem gamma_lipschitz_zero (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ : ρ < 1/4) (hs : ‖s‖ ≤ ρ/2) :
    (∑' n : ℕ × ℕ, ‖gamma s n - gamma (fun _ => 0) n‖) ≤
      (2 * uniformBound ρ / ρ) * ‖s‖ := by
  calc
    _ ≤ ∑' n, (2/ρ*‖s‖) * gammaMajorant ρ n := by
      apply (gamma_difference_absolute s ρ hρ0 hρ hs).tsum_le_tsum
      · intro n
        convert gamma_lipschitz_pointwise s ρ hρ0 hρ hs n using 1 <;> ring
      · exact (gammaMajorant_summable ρ hρ).mul_left _
    _ = (2/ρ*‖s‖) * ∑' n, gammaMajorant ρ n := tsum_mul_left
    _ ≤ (2/ρ*‖s‖) * uniformBound ρ :=
      mul_le_mul_of_nonneg_left (gammaMajorant_bound ρ hρ) (by positivity)
    _ = _ := by ring

end
end SixthMoment.Source.NoDPGlobalRest
