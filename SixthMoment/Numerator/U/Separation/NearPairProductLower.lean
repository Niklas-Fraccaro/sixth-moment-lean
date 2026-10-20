import SixthMoment.Numerator.U.Reconstruction.RectangularNearUnitExclusion

namespace SixthMoment
open Real Source
open scoped BigOperators

theorem a03_near_both_products_lower {A B η h : ℝ}
    (hA : 0<A) (hB : 0<B) (hη0 : 0<η) (hη : η≤1/2)
    (hh : 1≤h) (hrel : |A-B|=h) (hne : h≤η*Real.sqrt (A*B)) :
    1/(2*η)≤A ∧ 1/(2*η)≤B := by
  have hsA := rectangular_near_product_sqrt_le hA hB.le hη (by simpa [hrel] using hne)
  have hsB := rectangular_near_product_sqrt_le hB hA.le hη
    (by simpa [abs_sub_comm,mul_comm,hrel] using hne)
  have hsB' : Real.sqrt (A*B)≤2*B := by simpa only [mul_comm] using hsB
  have hLA : 1≤2*η*A := hh.trans (hne.trans (by nlinarith [mul_le_mul_of_nonneg_left hsA hη0.le]))
  have hLB : 1≤2*η*B := hh.trans (hne.trans (by nlinarith [mul_le_mul_of_nonneg_left hsB' hη0.le]))
  constructor
  · exact (div_le_iff₀ (by positivity : 0<2*η)).mpr (by nlinarith)
  · exact (div_le_iff₀ (by positivity : 0<2*η)).mpr (by nlinarith)

theorem a03_near_tuple_pair_products_lower (positive : Bool) (n : Fin 7→ℕ)
    {η U V : ℝ} (hη0 : 0<η) (hη : η≤1/2) (hU : 0<U) (hV : 0<V)
    (hn : ∀ j,1≤n j) (hu : (n 0:ℝ)≤U) (hv : (n 1:ℝ)≤V)
    (hrel : signedQuadraticRelation positive n) (hne : rectangularNearRelation η n) :
    1/(2*η*U)≤(n 2:ℝ)*n 3 ∧ 1/(2*η*V)≤(n 4:ℝ)*n 5 := by
  have hp (j : Fin 7) : (0:ℝ)<n j := by exact_mod_cast (show 0<n j by have := hn j; omega)
  have hA : 0<rectangularNearLeftProduct n := by exact mul_pos (mul_pos (hp 0) (hp 2)) (hp 3)
  have hB : 0<rectangularNearRightProduct n := by exact mul_pos (mul_pos (hp 1) (hp 4)) (hp 5)
  have hgap : (1:ℝ)≤n 6 := by exact_mod_cast hn 6
  have hne' : (n 6:ℝ)≤η*Real.sqrt (rectangularNearLeftProduct n*rectangularNearRightProduct n) := by
    simpa only [rectangularNearRelation,rectangular_near_tuple_mass] using hne
  have hl := a03_near_both_products_lower hA hB hη0 hη hgap
    (rectangular_signed_relation_abs_gap positive n hrel) hne'
  have hm : rectangularNearLeftProduct n≤U*((n 2:ℝ)*n 3) := by
    unfold rectangularNearLeftProduct
    nlinarith [mul_le_mul_of_nonneg_right hu (mul_nonneg (hp 2).le (hp 3).le)]
  have hn' : rectangularNearRightProduct n≤V*((n 4:ℝ)*n 5) := by
    unfold rectangularNearRightProduct
    nlinarith [mul_le_mul_of_nonneg_right hv (mul_nonneg (hp 4).le (hp 5).le)]
  constructor
  · rw [←div_div]
    exact (div_le_iff₀ hU).mpr (by nlinarith [hl.1.trans hm])
  · rw [←div_div]
    exact (div_le_iff₀ hV).mpr (by nlinarith [hl.2.trans hn'])

theorem a03_near_tuple_integrated_unit_lower (positive : Bool) (n : Fin 7→ℕ)
    {η U V : ℝ} (hη0 : 0<η) (hη : η≤1/2) (hU : 0<U) (hV : 0<V)
    (hn : ∀ j,1≤n j) (hu : (n 0:ℝ)≤U) (hv : (n 1:ℝ)≤V)
    (hrel : signedQuadraticRelation positive n) (hne : rectangularNearRelation η n) :
    (n 3=1 → 1/(2*η*U)≤(n 2:ℝ)) ∧
    (n 5=1 → 1/(2*η*V)≤(n 4:ℝ)) := by
  have h := a03_near_tuple_pair_products_lower positive n hη0 hη hU hV hn hu hv hrel hne
  constructor
  · intro hm; simpa [hm] using h.1
  · intro hm; simpa [hm] using h.2
end SixthMoment
