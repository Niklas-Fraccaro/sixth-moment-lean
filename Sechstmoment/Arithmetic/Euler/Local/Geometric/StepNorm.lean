import Mathlib.Analysis.Complex.Basic
import Sechstmoment.Arithmetic.Euler.Local.Geometric.StepOrder


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem norm_step_le (a : ℂ) (r : ℝ) (hr : 0≤r) (ha : ‖a‖≤r) (f : ℕ → ℂ) (n : ℕ) :
    ‖step a f n‖≤step r (fun k=>‖f k‖) n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    calc
      ‖step a f (n+1)‖≤‖f (n+1)‖+‖a*step a f n‖ := norm_add_le _ _
      _ = ‖f (n+1)‖+‖a‖*‖step a f n‖ := by rw [norm_mul]
      _ ≤ ‖f (n+1)‖+r*step r (fun k=>‖f k‖) n :=
        add_le_add le_rfl (mul_le_mul ha ih (norm_nonneg _) hr)
      _ = _ := rfl

end Sechstmoment.Source.NoDPLocal
