import SixthMoment.Arithmetic.Euler.Local.Coefficients.FourFiniteSum


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem step_mono (r : ℝ) (hr : 0≤r) (f g : ℕ → ℝ) (hfg : ∀ n, f n≤g n) (n : ℕ) :
    step r f n≤step r g n := by
  induction n with
  | zero => exact hfg 0
  | succ n ih => exact add_le_add (hfg (n+1)) (mul_le_mul_of_nonneg_left ih hr)
theorem step_nonneg (r : ℝ) (hr : 0≤r) (f : ℕ → ℝ) (hf : ∀ n, 0≤f n) (n : ℕ) : 0≤step r f n := by
  simpa using step_mono r hr (fun _=>0) f hf n

end SixthMoment.Source.NoDPLocal
