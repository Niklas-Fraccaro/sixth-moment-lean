import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Sechstmoment.Numerator.U.Replacement.GaussianBasis

/-! Genuine rapid-strip bounds for the fixed finite Gaussian basis. -/

namespace Sechstmoment.Source
open Complex Real Set Filter Asymptotics Bornology
open scoped BigOperators Topology
open Classical
noncomputable section

theorem gaussian_abs_pow_uniform_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, |v|^n*Real.exp (-v^2) ≤ C := by
  have ht : Tendsto (fun v : ℝ => |v|^n*Real.exp (-v^2))
      (cocompact ℝ) (𝓝 0) := by
    simpa only [Real.rpow_natCast, neg_one_mul] using
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 1) (by norm_num) (n : ℝ)
  have hc : Continuous (fun v : ℝ => |v|^n*Real.exp (-v^2)) := by fun_prop
  have hb := hc.isBounded_range_iff_isBigO.mpr
    (isBigO_const_of_tendsto ht (one_ne_zero : (1 : ℝ) ≠ 0))
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro v
  have hv := hC _ (Set.mem_range_self v)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hv
  exact hv.trans (le_max_left _ _)

theorem gaussian_one_add_abs_pow_uniform_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, Real.exp (-v^2)*(1+|v|)^n ≤ C := by
  obtain ⟨C0, hC0, hc0⟩ := gaussian_abs_pow_uniform_bound 0
  obtain ⟨Cn, hCn, hcn⟩ := gaussian_abs_pow_uniform_bound n
  refine ⟨2^(n-1)*(C0+Cn), by positivity, ?_⟩
  intro v
  have ha := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg v) n
  calc
    _ ≤ Real.exp (-v^2)*(2^(n-1)*(1+|v|^n)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [one_pow] using ha
    _ = 2^(n-1)*(Real.exp (-v^2)+|v|^n*Real.exp (-v^2)) := by ring
    _ ≤ 2^(n-1)*(C0+Cn) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (by simpa using hc0 v) (hcn v)

theorem fixedGaussianBasis_norm_bound (i : Fin 25) (z : ℂ) :
    ‖fixedGaussianBasis i z‖ ≤ Real.exp (z.re^2-z.im^2)*(1+‖z‖^(2*i.val)) := by
  have he : ‖Complex.exp (z^2)‖ = Real.exp (z.re^2-z.im^2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two]
  by_cases hi : i=0
  · simp only [fixedGaussianBasis, ite_eq_left hi, he]
    have hh : 0 ≤ ‖z‖^(2*i.val) := by positivity
    nlinarith [Real.exp_pos (z.re^2-z.im^2)]
  · rw [fixedGaussianBasis, ite_eq_right hi, norm_mul, he]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    simpa only [norm_one, norm_pow] using norm_add_le (1 : ℂ) (z^(2*i.val))

theorem fixedGaussianBasis_rapid_strip (i : Fin 25) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ R →
      ‖fixedGaussianBasis i z‖*(1+|z.im|)^N ≤ C := by
  obtain ⟨B, hB, hb⟩ := gaussian_one_add_abs_pow_uniform_bound (2*i.val+N)
  let D : ℝ := Real.exp (R^2)*(1+(R+1)^(2*i.val))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D*B, mul_nonneg hD hB, ?_⟩
  intro z hz
  have hre : z.re^2 ≤ R^2 := by nlinarith [sq_abs z.re, abs_nonneg z.re]
  have hnorm : ‖z‖ ≤ (R+1)*(1+|z.im|) := by
    have hn := Complex.norm_le_abs_re_add_abs_im z
    nlinarith [abs_nonneg z.im]
  have hpow : 1 ≤ (1+|z.im|)^(2*i.val) := one_le_pow₀ (by linarith [abs_nonneg z.im])
  have hexp : Real.exp (z.re^2-z.im^2) ≤ Real.exp (R^2)*Real.exp (-z.im^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  calc
    _ ≤ Real.exp (z.re^2-z.im^2)*(1+‖z‖^(2*i.val))*(1+|z.im|)^N :=
      mul_le_mul_of_nonneg_right (fixedGaussianBasis_norm_bound i z) (by positivity)
    _ ≤ (Real.exp (R^2)*Real.exp (-z.im^2))*
        (1+((R+1)*(1+|z.im|))^(2*i.val))*(1+|z.im|)^N := by gcongr
    _ ≤ (Real.exp (R^2)*Real.exp (-z.im^2))*
        ((1+(R+1)^(2*i.val))*(1+|z.im|)^(2*i.val))*(1+|z.im|)^N := by
      gcongr
      rw [mul_pow]
      nlinarith
    _ = D*(Real.exp (-z.im^2)*(1+|z.im|)^(2*i.val+N)) := by
      rw [pow_add]
      dsimp [D]
      ring
    _ ≤ D*B := mul_le_mul_of_nonneg_left (hb z.im) hD

theorem fixedGaussianBasis_admissible (i : Fin 25) :
    BBLREntireWeight (fixedGaussianBasis i) (fun _ => 0) := by
  refine ⟨?_, fixedGaussianBasis_even i, fixedGaussianBasis_zero i, ?_⟩
  · exact Complex.analyticOnNhd_univ_iff_differentiable.mpr (fixedGaussianBasis_differentiable i)
  · exact fun R hR N => fixedGaussianBasis_rapid_strip i R hR N

end
end Sechstmoment.Source
