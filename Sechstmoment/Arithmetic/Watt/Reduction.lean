import Sechstmoment.Arithmetic.Watt.MainGlobal
import Sechstmoment.Arithmetic.Watt.TailGlobal
import Sechstmoment.Arithmetic.Watt.ZeroGlobal

/-! Complete reduction of the original weighted Watt theorem to the exact
Proposition 4.1. No additional analytic input is assumed. -/

namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 4000000

theorem weightedWattBound_of_watt41 (hW : Watt41) : WeightedWattBound := by
  intro η hη b hb g hg
  obtain ⟨Cw,F,hCw,hF,hmain⟩ := hW.smoothedSum_bound hη b hb g hg
  obtain ⟨Cz,hCz,hzero⟩ := Watt41.zero_global_bound hη b hb g hg
  obtain ⟨Ct,hCt,htail⟩ := Watt41.tail_global_bound hη b hb g hg
  refine ⟨Cz+2*Cw+Ct,F,by positivity,hF,?_⟩
  intro p Δ a bc u₀ u₁ γ hp hΔ hΔ₁ hw hlarge hfirst hsecond positive
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  have hE : 1 ≤ p.product^η := Real.one_le_rpow (Watt41.product_ge_one hp) hη.le
  have hEp : 0 < p.product^η := by linarith
  have hA := Watt41.dualLength_pos hS hP hV hEp
  have hz := hzero p Δ a bc u₀ u₁ γ hp hΔ hΔ₁ hw positive
  have hsPos := hmain p Δ a bc u₀ u₁ γ hp hΔ hΔ₁ hw hlarge hfirst hsecond positive 1 (Or.inr rfl)
  have hsNeg := hmain p Δ a bc u₀ u₁ γ hp hΔ hΔ₁ hw hlarge hfirst hsecond positive (-1) (Or.inl rfl)
  have ht := htail p Δ a bc u₀ u₁ γ hp hΔ hΔ₁ hw positive
  rw [Watt41.weightedWattSum_smooth_split hw hV hA]
  have hnorm :
      ‖Watt41.frequencySum p a bc u₀ u₁ γ positive 0+
        Watt41.smoothedSum p (Watt41.dualLength p (p.product^η)) positive 1 a bc u₀ u₁ γ+
        Watt41.smoothedSum p (Watt41.dualLength p (p.product^η)) positive (-1) a bc u₀ u₁ γ+
        Watt41.highSum p (Watt41.dualLength p (p.product^η)) positive a bc u₀ u₁ γ‖ ≤
      ‖Watt41.frequencySum p a bc u₀ u₁ γ positive 0‖+
        ‖Watt41.smoothedSum p (Watt41.dualLength p (p.product^η)) positive 1 a bc u₀ u₁ γ‖+
        ‖Watt41.smoothedSum p (Watt41.dualLength p (p.product^η)) positive (-1) a bc u₀ u₁ γ‖+
        ‖Watt41.highSum p (Watt41.dualLength p (p.product^η)) positive a bc u₀ u₁ γ‖ :=
    (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  exact hnorm.trans ((add_le_add (add_le_add (add_le_add hz hsPos) hsNeg) ht).trans_eq (by ring))

end
end DivisorProof
