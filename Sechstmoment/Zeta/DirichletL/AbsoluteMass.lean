import Mathlib.NumberTheory.LSeries.Convolution


namespace Sechstmoment.Source
open Complex Set
open scoped LSeries.notation
noncomputable section

theorem dirichlet_convolution_absolute_mass_le {f g : ℕ → ℂ} {s : ℂ}
    (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    (∑' n : ℕ, ‖LSeries.term (f ⍟ g) s n‖) ≤
      (∑' n : ℕ, ‖LSeries.term f s n‖)*(∑' n : ℕ, ‖LSeries.term g s n‖) := by
  have hprod : Summable (fun p : ℕ × ℕ => LSeries.term f s p.1*LSeries.term g s p.2) :=
    summable_mul_of_summable_norm hf.norm hg.norm
  have hnorm : Summable (fun p : ℕ × ℕ => ‖LSeries.term f s p.1‖*‖LSeries.term g s p.2‖) := by
    simpa only [norm_mul] using hprod.norm
  have hsum := hf.norm.hasSum.mul hg.norm.hasSum hnorm
  have hgroup := hsum.tsum_fiberwise (fun p : ℕ × ℕ => p.1*p.2)
  have hconv := hf.convolution hg
  calc
    _ ≤ ∑' n : ℕ, ∑' p : (fun p : ℕ × ℕ => p.1*p.2) ⁻¹' {n},
        ‖LSeries.term f s p.val.1‖*‖LSeries.term g s p.val.2‖ := by
      apply hconv.norm.tsum_le_tsum _ hgroup.summable
      intro n
      rw [congrFun (LSeries.term_convolution' f g s) n]
      simpa only [norm_mul] using! norm_tsum_le_tsum_norm
        (hprod.norm.subtype (fun p : ℕ × ℕ => p.1*p.2 = n))
    _ = _ := hgroup.tsum_eq

end
end Sechstmoment.Source
