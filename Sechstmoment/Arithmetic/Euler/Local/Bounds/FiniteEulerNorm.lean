import Sechstmoment.Arithmetic.Euler.Local.Prime.FiniteEulerFactorization

/-! Pointwise local estimates multiply to a finite global norm estimate. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem finite_local_norm_le {ι : Type*} (s : Finset ι) (F : ι → ℂ) (B : ι → ℝ)
    (hB : ∀ i∈s, ‖F i‖≤B i) : ‖∏ i∈s,F i‖≤∏ i∈s,B i := by
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) hB

end Sechstmoment.Source.NoDPLocal
