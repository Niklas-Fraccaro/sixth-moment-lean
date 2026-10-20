import Sechstmoment.Numerator.Polar.General.Contour


namespace Sechstmoment
open Complex Metric
open scoped BigOperators

set_option maxHeartbeats 1000000

noncomputable def polarSourceKnots (σ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![-σ 0, -σ 1, σ 2, σ 3]

theorem polarGeneralTripleProfile_swap01 (η : ℝ) (P : Polynomial ℝ)
    (a b c : ℂ) (R : ℝ) :
    polarGeneralTripleProfile η P ![a,b,c] R =
      polarGeneralTripleProfile η P ![b,a,c] R := by
  have hp (u : ℂ) : (∏ j : Fin 3, (u- (![a,b,c] : Fin 3 → ℂ) j)) =
      (∏ j : Fin 3, (u- (![b,a,c] : Fin 3 → ℂ) j)) := by
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    ring
  unfold polarGeneralTripleProfile polarTripleInverseContour
  simp_rw [hp]

theorem polarGeneralTripleProfile_cycle (η : ℝ) (P : Polynomial ℝ)
    (a b c : ℂ) (R : ℝ) :
    polarGeneralTripleProfile η P ![a,b,c] R =
      polarGeneralTripleProfile η P ![b,c,a] R := by
  have hp (u : ℂ) : (∏ j : Fin 3, (u- (![a,b,c] : Fin 3 → ℂ) j)) =
      (∏ j : Fin 3, (u- (![b,c,a] : Fin 3 → ℂ) j)) := by
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    ring
  unfold polarGeneralTripleProfile polarTripleInverseContour
  simp_rw [hp]

theorem polarGeneralGeneratorContour_source_residues
    (η : ℝ) (P : Polynomial ℝ) (σ : Fin 4 → ℂ) (innerR outerR : ℝ)
    (hσ : Function.Injective (polarSourceKnots σ))
    (hinner : ∀ j, ‖polarSourceKnots σ j‖ < innerR)
    (houter : ∀ j, ‖polarSourceKnots σ j‖ < outerR) :
    polarGeneralGeneratorContour η P (polarSourceKnots σ) innerR outerR =
      Complex.exp (-σ 0-σ 2-σ 3)*
        (polarGeneralTripleProfile η P ![-σ 1,σ 2,σ 3] innerR)^2 /
          ((σ 1-σ 0)*(σ 0+σ 2)*(σ 0+σ 3)) +
      Complex.exp (-σ 1-σ 2-σ 3)*
        (polarGeneralTripleProfile η P ![-σ 0,σ 2,σ 3] innerR)^2 /
          ((σ 0-σ 1)*(σ 1+σ 2)*(σ 1+σ 3)) +
      Complex.exp (-σ 3)*
        (polarGeneralTripleProfile η P ![-σ 1,-σ 0,σ 3] innerR)^2 /
          ((σ 1+σ 2)*(σ 0+σ 2)*(σ 2-σ 3)) +
      Complex.exp (-σ 2)*
        (polarGeneralTripleProfile η P ![-σ 1,σ 2,-σ 0] innerR)^2 /
          ((σ 1+σ 3)*(σ 3-σ 2)*(σ 0+σ 3)) := by
  rw [polarGeneralGeneratorContour_triple_residues η P (polarSourceKnots σ)
    innerR outerR hσ hinner houter]
  have hq0 : (fun k : Fin 3 => polarSourceKnots σ ((0 : Fin 4).succAbove k)) =
      ![-σ 1,σ 2,σ 3] := by funext k; fin_cases k <;> rfl
  have hq1 : (fun k : Fin 3 => polarSourceKnots σ ((1 : Fin 4).succAbove k)) =
      ![-σ 0,σ 2,σ 3] := by funext k; fin_cases k <;> rfl
  have hq2 : (fun k : Fin 3 => polarSourceKnots σ ((2 : Fin 4).succAbove k)) =
      ![-σ 0,-σ 1,σ 3] := by funext k; fin_cases k <;> rfl
  have hq3 : (fun k : Fin 3 => polarSourceKnots σ ((3 : Fin 4).succAbove k)) =
      ![-σ 0,-σ 1,σ 2] := by funext k; fin_cases k <;> rfl
  have hu0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have hu1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have hu2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have hu3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  rw [Fin.sum_univ_four, hq0, hq1, hq2, hq3,
    polarGeneralTripleProfile_swap01 η P (-σ 0) (-σ 1) (σ 3),
    polarGeneralTripleProfile_cycle η P (-σ 0) (-σ 1) (σ 2)]
  norm_num [polarSourceKnots, polarPoleDenominator, hu0,hu1,hu2,hu3,
    Finset.prod_insert]
  have hd0 : (-σ 0+σ 1)*((-σ 0-σ 2)*(-σ 0-σ 3)) =
      (σ 1-σ 0)*(σ 0+σ 2)*(σ 0+σ 3) := by ring
  have hd1 : (-σ 1+σ 0)*((-σ 1-σ 2)*(-σ 1-σ 3)) =
      (σ 0-σ 1)*(σ 1+σ 2)*(σ 1+σ 3) := by ring
  have hd2 : (σ 2+σ 0)*((σ 2+σ 1)*(σ 2-σ 3)) =
      (σ 1+σ 2)*(σ 0+σ 2)*(σ 2-σ 3) := by ring
  have hd3 : (σ 3+σ 0)*((σ 3+σ 1)*(σ 3-σ 2)) =
      (σ 1+σ 3)*(σ 3-σ 2)*(σ 0+σ 3) := by ring
  rw [hd0,hd1,hd2,hd3]

end Sechstmoment
