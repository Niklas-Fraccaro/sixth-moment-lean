import Sechstmoment.Numerator.U.Separation.ShapeActualPowerNear

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

/-- The relative gap scale is supplied by an actual supported signed near
tuple. It is bounded by sixteen times the actual near width. -/
theorem phase_supported_near_relative_gap_scale (q : QuadraticScales)
    (hq : ∀ j, 0≤q.size j) (hBN : 0<q.B*q.N) (n : Fin 7 → ℕ)
    (hn : ∀ j, (n j:ℝ)∈Icc (q.size j) (2*q.size j)) (hp : ∀ j, 0<n j)
    (positive : Bool) (hrel : signedQuadraticRelation positive n)
    {η : ℝ} (hη0 : 0≤η) (hη : η≤1/2) (hne : rectangularNearRelation η n) :
    q.H/(q.B*q.N)≤16*η := by
  have hR : 0<rectangularNearRightProduct n := by
    unfold rectangularNearRightProduct
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (hp 1) (hp 4)) (hp 5)
  have hL : 0≤rectangularNearLeftProduct n := by
    unfold rectangularNearLeftProduct
    positivity
  have hgap := rectangular_signed_relation_abs_gap positive n hrel
  have hne' : (n 6:ℝ)≤η*Real.sqrt
      (rectangularNearRightProduct n*rectangularNearLeftProduct n) := by
    simpa [rectangularNearRelation,rectangular_near_tuple_mass,mul_comm] using hne
  have hab : |rectangularNearRightProduct n-rectangularNearLeftProduct n|≤η*Real.sqrt
      (rectangularNearRightProduct n*rectangularNearLeftProduct n) := by
    simpa [abs_sub_comm,hgap] using hne'
  have hs := rectangular_near_product_sqrt_le hR hL hη hab
  have hsη := mul_le_mul_of_nonneg_left hs hη0
  have hright := (phase_supported_right_product_bounds q hq n hn).2
  have hb := mul_le_mul_of_nonneg_left hright (show 0≤2*η by positivity)
  have hH : q.H≤(n 6:ℝ) := by simpa [QuadraticScales.size] using (hn 6).1
  apply (div_le_iff₀ hBN).mpr
  nlinarith

theorem phase_actual_near_relative_gap_scale (T A B H η : ℝ) (f g : ℝ → ℝ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) (k : Fin 4 → ℕ)
    (hη0 : 0≤η) (hη : η≤1/2)
    (hactive : phaseActualActiveNearBlock T A B H η f g k) :
    H/(B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3)))≤16*η := by
  obtain ⟨a,b,h,n,positive,ha,hb,hw,hh,hrel,hnear⟩ := hactive
  have hq := boundaryActual_scales_pos A B H k hA hB hH
  have htuple := phase_actual_source_tuple_support T A B H f g hA hB hH k n a b h ha hb hw hh
  have htuplepos := phase_actual_source_tuple_positive T A B H f g hA hB hH k n a b h ha hb hw hh
  have hBN : 0<(phaseActualScales A B H k).B*(phaseActualScales A B H k).N := by
    change 0<B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3))
    exact mul_pos hB (mul_pos (boundaryActual_scale_pos _) (boundaryActual_scale_pos _))
  exact phase_supported_near_relative_gap_scale (phaseActualScales A B H k)
    (fun j => (hq j).le) hBN _ htuple htuplepos positive hrel hη0 hη hnear

/-- The actual small-power near block satisfies every fixed small-r
threshold eventually, uniformly in all retained scales and indices. -/
theorem phase_actual_near_relative_gap_eventually_small {s δ : ℝ} (hs : s<1) (hδ : 0<δ)
    (f g : ℝ → ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H → ∀ k : Fin 4 → ℕ,
      phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      H/(B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3)))≤δ := by
  have ht : Tendsto (fun T : ℝ => T^(s-1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hs)
  have hb : ∀ᶠ T : ℝ in atTop, T^(s-1)≤min (1/2) (δ/16) :=
    ((tendsto_order.1 ht).2 (min (1/2) (δ/16)) (lt_min (by norm_num) (by positivity))).mono
      (fun _ h => h.le)
  filter_upwards [hb,eventually_gt_atTop (0:ℝ)] with T hbound hT
  intro A B H hA hB hH k hactive
  have hη0 : 0≤T^(s-1) := Real.rpow_nonneg hT.le _
  have hη : T^(s-1)≤1/2 := hbound.trans (min_le_left _ _)
  have hsmall : T^(s-1)≤δ/16 := hbound.trans (min_le_right _ _)
  exact (phase_actual_near_relative_gap_scale T A B H _ f g hA hB hH k hη0 hη hactive).trans
    (by nlinarith)

/-- The exact unit and common dilation preserves the relative gap scale. -/
theorem phase_boundary_relative_gap_scale (flags : Fin 4 → Bool) (q : QuadraticScales) :
    (boundaryEmbeddedScales flags q).H/
      ((boundaryEmbeddedScales flags q).B*(boundaryEmbeddedScales flags q).N)=
      q.H/(q.B*q.N) := by
  rw [boundaryEmbedded_H,boundaryEmbedded_right_scale_product]
  have hc : (2:ℝ)*boundaryProductFactor flags≠0 := by
    have h := (boundaryProductFactor_bounds flags).1
    positivity
  exact mul_div_mul_left _ _ hc

end
end Sechstmoment
