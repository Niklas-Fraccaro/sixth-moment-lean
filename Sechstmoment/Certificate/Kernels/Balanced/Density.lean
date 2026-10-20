import Mathlib.Tactic.FunProp
import Sechstmoment.Analysis.Integration.PositivePartIntegral

namespace Sechstmoment

open MeasureTheory

theorem min_positivePart (r s : ℝ) : min r s = r-max (r-s) 0 := by
  by_cases h : r ≤ s
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    ring

theorem density_inner_integral {m v : ℝ} (hmv : m ≤ v) (t r : ℝ) :
    (∫ s in m..v, min r s-max (s-(t-r)) 0) =
      r*(v-m) - ((max (r-m) 0)^2-(max (r-v) 0)^2)/2 -
      ((max (v-(t-r)) 0)^2-(max (m-(t-r)) 0)^2)/2 := by
  simp_rw [min_positivePart]
  have h₀ : Continuous (fun _ : ℝ => r) := continuous_const
  have h₁ : Continuous (fun s : ℝ => max (r-s) 0) := by fun_prop
  have h₂ : Continuous (fun s : ℝ => max (s-(t-r)) 0) := by fun_prop
  have h₀₁ : Continuous (fun s : ℝ => r-max (r-s) 0) := by fun_prop
  rw [intervalIntegral.integral_sub (h₀₁.intervalIntegrable m v)
    (h₂.intervalIntegrable m v),
    intervalIntegral.integral_sub (h₀.intervalIntegrable m v) (h₁.intervalIntegrable m v),
    intervalIntegral.integral_const]
  have hp₁ : (∫ s in m..v, max (r-s) 0) =
      ((max (r-m) 0)^2-(max (r-v) 0)^2)/2 := by
    have h := positivePart_reflected_integral hmv r 1 (by decide)
    norm_num at h
    exact h
  have hp₂ : (∫ s in m..v, max (s-(t-r)) 0) =
      ((max (v-(t-r)) 0)^2-(max (m-(t-r)) 0)^2)/2 := by
    have h := positivePart_shifted_integral hmv (t-r) 1 (by decide)
    norm_num at h
    exact h
  rw [hp₁, hp₂]
  simp only [smul_eq_mul]
  ring

theorem denominator_density_cubic {l u m v : ℝ} (hlu : l ≤ u) (hmv : m ≤ v)
    (t : ℝ) :
    6*(∫ r in l..u, ∫ s in m..v, min r s-max (s-(t-r)) 0) =
      3*(u^2-l^2)*(v-m) +
      (max (u-v) 0)^3-(max (l-v) 0)^3-(max (u-m) 0)^3+(max (l-m) 0)^3 -
      ((max (u-(t-v)) 0)^3-(max (l-(t-v)) 0)^3-
        (max (u-(t-m)) 0)^3+(max (l-(t-m)) 0)^3) := by
  simp_rw [density_inner_integral hmv]
  have hargv (r : ℝ) : v-(t-r) = r-(t-v) := by ring
  have hargm (r : ℝ) : m-(t-r) = r-(t-m) := by ring
  simp_rw [hargv, hargm]
  let f₀ := fun r : ℝ => r*(v-m)
  let f₁ := fun r : ℝ => ((max (r-m) 0)^2-(max (r-v) 0)^2)/2
  let f₂ := fun r : ℝ => ((max (r-(t-v)) 0)^2-(max (r-(t-m)) 0)^2)/2
  have hc₀ : Continuous f₀ := by dsimp [f₀]; fun_prop
  have hc₁ : Continuous f₁ := by dsimp [f₁]; fun_prop
  have hc₂ : Continuous f₂ := by dsimp [f₂]; fun_prop
  have hc₀₁ : Continuous (fun r : ℝ => f₀ r-f₁ r) := by fun_prop
  change 6*(∫ r in l..u, f₀ r-f₁ r-f₂ r) = _
  rw [intervalIntegral.integral_sub (hc₀₁.intervalIntegrable l u)
      (hc₂.intervalIntegrable l u),
    intervalIntegral.integral_sub (hc₀.intervalIntegrable l u) (hc₁.intervalIntegrable l u)]
  have hf₀ : (∫ r in l..u, f₀ r) = (u^2-l^2)*(v-m)/2 := by
    dsimp [f₀]
    rw [intervalIntegral.integral_mul_const]
    have hp : (∫ r in l..u, r) = (u^2-l^2)/2 := by
      simp
    rw [hp]
    ring
  have hp (c : ℝ) : Continuous (fun r : ℝ => (max (r-c) 0)^2) := by fun_prop
  have hf₁ : (∫ r in l..u, f₁ r) =
      ((max (u-m) 0)^3-(max (l-m) 0)^3-
        ((max (u-v) 0)^3-(max (l-v) 0)^3))/6 := by
    dsimp [f₁]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_sub ((hp m).intervalIntegrable l u)
        ((hp v).intervalIntegrable l u)]
    rw [positivePart_shifted_integral hlu m 2 (by decide),
      positivePart_shifted_integral hlu v 2 (by decide)]
    norm_num
    ring
  have hf₂ : (∫ r in l..u, f₂ r) =
      ((max (u-(t-v)) 0)^3-(max (l-(t-v)) 0)^3-
        ((max (u-(t-m)) 0)^3-(max (l-(t-m)) 0)^3))/6 := by
    dsimp [f₂]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_sub ((hp (t-v)).intervalIntegrable l u)
        ((hp (t-m)).intervalIntegrable l u)]
    rw [positivePart_shifted_integral hlu (t-v) 2 (by decide),
      positivePart_shifted_integral hlu (t-m) 2 (by decide)]
    norm_num
    ring
  rw [hf₀,hf₁,hf₂]
  ring

end Sechstmoment
