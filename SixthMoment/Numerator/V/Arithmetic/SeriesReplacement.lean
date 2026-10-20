import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace SixthMoment.Source
noncomputable section

theorem summable_series_replacement_bound {ι : Type*} {F G : ι → ℂ} {p : ι → ℝ}
    (hF : Summable F) (hp : Summable p) (hbound : ∀ i, ‖F i-G i‖ ≤ p i) :
    Summable G ∧ ‖(∑' i, F i)-(∑' i, G i)‖ ≤ ∑' i, p i := by
  have henorm : Summable (fun i => ‖F i-G i‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hp
  have he : Summable (fun i => F i-G i) := henorm.of_norm
  have hG : Summable G := by
    convert hF.sub he using 1
    funext i
    ring
  refine ⟨hG,?_⟩
  rw [← hF.tsum_sub hG]
  exact (norm_tsum_le_tsum_norm henorm).trans (henorm.tsum_le_tsum hbound hp)

end
end SixthMoment.Source
