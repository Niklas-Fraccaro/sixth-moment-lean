import SixthMoment.Zeta.Bounds.LeftStrip


namespace SixthMoment
open Complex Real MeasureTheory Filter Set
open scoped Topology ComplexOrder
noncomputable section

theorem d04RiemannZeta_polynomial_strip_away_pole {a b r : ℝ}
    (ha : -1 ≤ a) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → r ≤ ‖s-1‖ →
      ‖riemannZeta s‖ ≤ C*(1+|s.im|)^6 := by
  obtain ⟨C,hC,hhigh⟩ := d04RiemannZeta_polynomial_halfPlane_high_im
  let K : Set ℂ := (Icc a b ×ℂ Icc (-1 : ℝ) 1) ∩ {s : ℂ | r ≤ ‖s-1‖}
  have hK : IsCompact K :=
    (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (by fun_prop))
  have hζ : ContinuousOn riemannZeta K := by
    intro s hs
    apply (differentiableAt_riemannZeta ?_).continuousAt.continuousWithinAt
    intro he
    have hsep : r ≤ ‖s-1‖ := hs.2
    norm_num [he] at hsep
    linarith
  obtain ⟨D,hD⟩ := hK.bddAbove_image hζ.norm
  let L : ℝ := max C (max 0 D)
  have hL : 0 ≤ L := hC.trans (le_max_left _ _)
  refine ⟨L,hL,?_⟩
  intro s hsa hsb hsep
  by_cases him : 1 ≤ |s.im|
  · exact (hhigh s (ha.trans hsa) him).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hsK : s ∈ K := ⟨⟨⟨hsa,hsb⟩,abs_le.mp
      (le_of_lt (lt_of_not_ge him))⟩,hsep⟩
    calc
      _ ≤ D := hD (mem_image_of_mem (fun s => ‖riemannZeta s‖) hsK)
      _ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
      _ ≤ L*(1+|s.im|)^6 := le_mul_of_one_le_right hL
        (one_le_pow₀ (by linarith [abs_nonneg s.im]))

theorem d04RiemannZeta_sharp_left_strip_all_im {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ -ε →
      ‖riemannZeta s‖ ≤ C*(1+|s.im|)^(1/2-s.re) := by
  obtain ⟨C,hC,hhigh⟩ := d04RiemannZeta_sharp_left_strip hε
  let K : Set ℂ := Icc (-1 : ℝ) (-ε) ×ℂ Icc (-128 : ℝ) 128
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hζ : ContinuousOn riemannZeta K := by
    intro s hs
    apply (differentiableAt_riemannZeta ?_).continuousAt.continuousWithinAt
    intro he
    have hs0 : s.re ≤ -ε := hs.1.2
    norm_num [he] at hs0
    linarith
  obtain ⟨D,hD⟩ := hK.bddAbove_image hζ.norm
  let L : ℝ := max C (max 0 D)
  have hL : 0 ≤ L := hC.trans (le_max_left _ _)
  refine ⟨L,hL,?_⟩
  intro s hs0 hsε
  by_cases him : 128 ≤ |s.im|
  · exact (hhigh s hs0 hsε him).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hsK : s ∈ K := ⟨⟨hs0,hsε⟩,abs_le.mp (le_of_lt (lt_of_not_ge him))⟩
    calc
      _ ≤ D := hD (mem_image_of_mem (fun s => ‖riemannZeta s‖) hsK)
      _ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
      _ ≤ L*(1+|s.im|)^(1/2-s.re) := le_mul_of_one_le_right hL
        (Real.one_le_rpow (by linarith [abs_nonneg s.im]) (by linarith))

end
end SixthMoment
