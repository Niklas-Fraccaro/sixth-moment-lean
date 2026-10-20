import SixthMoment.Numerator.Polar.General.Source
import SixthMoment.Numerator.U.MainTerm.UniformSixMainLimit
import SixthMoment.Numerator.V.DP.DPPolydiscBoundary


namespace SixthMoment
open Complex Source Set
open scoped Topology
noncomputable section

def normalizedPurePolarEndpoints (k : PurePolarIndex) : Fin 4 × Fin 4 :=
  (![ ![![(0,2),(0,3)], ![(1,2),(1,3)]],
      ![![(2,0),(2,1)], ![(3,0),(3,1)]],
      ![![(2,0),(2,3)], ![(1,0),(1,3)]],
      ![![(3,2),(3,0)], ![(1,2),(1,0)]],
      ![![(0,1),(0,3)], ![(2,1),(2,3)]],
      ![![(0,2),(0,1)], ![(3,2),(3,1)]] ]
    : Fin 6 → Fin 2 → Fin 2 → Fin 4 × Fin 4) k.1 k.2.1 k.2.2

theorem normalizedPurePolarEndpoints_ne (k : PurePolarIndex) :
    (normalizedPurePolarEndpoints k).1 ≠ (normalizedPurePolarEndpoints k).2 := by
  rcases k with ⟨m,i,j⟩
  fin_cases m <;> fin_cases i <;> fin_cases j <;> norm_num [normalizedPurePolarEndpoints]

theorem normalizedPurePolarRoot_eq_sourceKnots_difference
    (σ : MomentShifts) (k : PurePolarIndex) :
    normalizedPurePolarRoot σ k =
      (polarSourceKnots σ (normalizedPurePolarEndpoints k).1-
        polarSourceKnots σ (normalizedPurePolarEndpoints k).2)/2 := by
  rcases k with ⟨m,i,j⟩
  fin_cases m <;> fin_cases i <;> fin_cases j <;>
    simp [normalizedPurePolarRoot,normalizedPurePolarEndpoints,polarSourceKnots,
      bblrSixShifts,purePolarLeft,purePolarRight] <;> ring

theorem normalizedPurePolarRoot_ne_zero_of_DPSeparated (σ : MomentShifts)
    (hσ : DPSeparated σ) (k : PurePolarIndex) : normalizedPurePolarRoot σ k ≠ 0 := by
  intro hz
  rw [normalizedPurePolarRoot_eq_sourceKnots_difference] at hz
  have hp : polarSourceKnots σ (normalizedPurePolarEndpoints k).1 =
      polarSourceKnots σ (normalizedPurePolarEndpoints k).2 := by
    apply sub_eq_zero.mp
    exact (div_eq_zero_iff.mp hz).resolve_right (by norm_num)
  exact normalizedPurePolarEndpoints_ne k (hσ hp)

theorem polarSourceKnots_norm (σ : MomentShifts) (j : Fin 4) :
    ‖polarSourceKnots σ j‖ = ‖σ j‖ := by
  fin_cases j <;> simp [polarSourceKnots]

theorem dpCauchyBoundary_pure_root_gap (σ : MomentShifts)
    (hσ : σ ∈ rectangularDistinguishedBoundary dpCauchyRadii) (k : PurePolarIndex) :
    (1/2:ℝ) ≤ ‖normalizedPurePolarRoot σ k‖ := by
  have hg (i j : Fin 4) (hij : i ≠ j) : (1:ℝ) ≤ |dpCauchyRadii i-dpCauchyRadii j| := by
    fin_cases i <;> fin_cases j <;> norm_num [dpCauchyRadii] at *
  have ht := abs_norm_sub_norm_le
    (polarSourceKnots σ (normalizedPurePolarEndpoints k).1)
    (polarSourceKnots σ (normalizedPurePolarEndpoints k).2)
  rw [polarSourceKnots_norm,polarSourceKnots_norm,hσ _,hσ _] at ht
  have hb := (hg _ _ (normalizedPurePolarEndpoints_ne k)).trans ht
  rw [normalizedPurePolarRoot_eq_sourceKnots_difference,norm_div]
  norm_num only [norm_ofNat]
  linarith

theorem dpCauchyBoundary_subset_boundedSeparatedPolarShifts :
    rectangularDistinguishedBoundary dpCauchyRadii ⊆ boundedSeparatedPolarShifts 8 := by
  intro σ hσ
  constructor
  · intro j
    rw [hσ j]
    fin_cases j <;> norm_num [dpCauchyRadii]
  · intro k
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2)
      (dpCauchyBoundary_pure_root_gap σ hσ k))

theorem bblrSixMainTerms_polar_uniform_on_dpCauchyBoundary
    {a b : ℝ} (hab : a+b < 1) (f g Φ : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    TendstoUniformlyOn
      (fun T : ℝ => fun σ : MomentShifts =>
        bblrSixMainTerms T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ/
          ((T:ℂ)*(Real.log T:ℂ)^9))
      (fun σ => actualSixPrincipalPolarLimit σ (fun x => (f x:ℂ))
        (fun x => (g x:ℂ)) Φ 33) Filter.atTop
      (rectangularDistinguishedBoundary dpCauchyRadii) :=
  bblrSixMainTerms_separated_polar_uniform_on_compact
    (R := 8) (c := 33) (δ := 1/8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hab dpCauchyBoundary_isCompact
    dpCauchyBoundary_subset_boundedSeparatedPolarShifts f g Φ hf hg hΦ

end
end SixthMoment
