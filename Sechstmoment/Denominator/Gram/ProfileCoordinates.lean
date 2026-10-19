import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FinCases

/-! Exact coordinate transport for the four-profile Gram integrals.
The measure is product Lebesgue measure; no integrability or limit premise
is needed to transport the Bochner integral along these measurable equivalences. -/
namespace Sechstmoment
open MeasureTheory
noncomputable section

abbrev D06ProfileProductSpace := (ℝ × ℝ) × (ℝ × ℝ)
abbrev D06ProfileIndex := (Unit ⊕ Unit) ⊕ (Unit ⊕ Unit)

def d06ProfileIndex : D06ProfileIndex → Fin 4 :=
  Sum.elim (Sum.elim (fun _ => 0) (fun _ => 1))
    (Sum.elim (fun _ => 2) (fun _ => 3))

def d06ProfileIndexEquiv : D06ProfileIndex ≃ Fin 4 :=
  Equiv.ofBijective d06ProfileIndex (by decide)

def d06ProfilePairEquiv : (Unit ⊕ Unit → ℝ) ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ Unit => ℝ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique Unit ℝ)
      (MeasurableEquiv.funUnique Unit ℝ))

def d06ProfileCoordinates : (Fin 4 → ℝ) ≃ᵐ D06ProfileProductSpace :=
  (MeasurableEquiv.arrowCongr' d06ProfileIndexEquiv.symm (MeasurableEquiv.refl ℝ)).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : D06ProfileIndex => ℝ)).trans
      (MeasurableEquiv.prodCongr d06ProfilePairEquiv d06ProfilePairEquiv))

theorem d06ProfileCoordinates_measurePreserving :
    MeasurePreserving d06ProfileCoordinates volume volume := by
  have hU := volume_preserving_funUnique Unit ℝ
  have hP := (hU.prod hU).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Unit ⊕ Unit => ℝ))
  exact ((hP.prod hP).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : D06ProfileIndex => ℝ))).comp
      (volume_preserving_arrowCongr' d06ProfileIndexEquiv.symm
        (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))

theorem d06ProfileCoordinates_apply (a : Fin 4 → ℝ) :
    d06ProfileCoordinates a = ((a 0,a 1),(a 2,a 3)) := rfl

theorem d06ProfileCoordinates_symm_apply (z : D06ProfileProductSpace) :
    d06ProfileCoordinates.symm z = ![z.1.1,z.1.2,z.2.1,z.2.2] := by
  apply d06ProfileCoordinates.injective
  rw [d06ProfileCoordinates.apply_symm_apply,d06ProfileCoordinates_apply]
  rfl

/-- The Fin-4 product volume and the original paired product volume agree. -/
theorem d06ProfileIntegral_coordinates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : (Fin 4 → ℝ) → E) :
    (∫ a : Fin 4 → ℝ, f a) =
      ∫ z : D06ProfileProductSpace, f ![z.1.1,z.1.2,z.2.1,z.2.2]
        ∂((volume.prod volume).prod (volume.prod volume)) := by
  have h := d06ProfileCoordinates_measurePreserving.symm.integral_comp
    d06ProfileCoordinates.symm.measurableEmbedding f
  simp only [d06ProfileCoordinates_symm_apply] at h
  simpa only [Measure.volume_eq_prod] using h.symm

/-- Relabeling the four real coordinates preserves their product volume. -/
theorem d06ProfileIntegral_permute {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (e : Fin 4 ≃ Fin 4)
    (f : (Fin 4 → ℝ) → E) :
    (∫ a : Fin 4 → ℝ, f (fun i => a (e i))) = ∫ a : Fin 4 → ℝ, f a := by
  have h := volume_preserving_arrowCongr' e.symm (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id (volume : Measure ℝ))
  exact h.integral_comp (MeasurableEquiv.arrowCongr' e.symm
    (MeasurableEquiv.refl ℝ)).measurableEmbedding f

end
end Sechstmoment

namespace Sechstmoment
open MeasureTheory
open scoped BigOperators
noncomputable section

/-- Simultaneous relabeling of profiles and endpoint kernel, retaining all
four actual Lebesgue differentials. -/
theorem d06ProfileIntegral_reindex (e : Fin 4 ≃ Fin 4)
    (ρ : Fin 4 → ℝ → ℝ) (F : (Fin 4 → ℝ) → ℝ) :
    (∫ a : Fin 4 → ℝ, (∏ i, ρ (e i) (a i))*F a) =
      ∫ a : Fin 4 → ℝ, (∏ i, ρ i (a i))*F (fun i => a (e i)) := by
  have h := d06ProfileIntegral_permute e
    (fun a : Fin 4 → ℝ => (∏ i, ρ (e i) (a i))*F a)
  calc
    _ = ∫ a : Fin 4 → ℝ, (∏ i, ρ (e i) (a (e i)))*F (fun i => a (e i)) := h.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with a
      rw [e.prod_comp (fun i => ρ i (a i))]

end
end Sechstmoment
