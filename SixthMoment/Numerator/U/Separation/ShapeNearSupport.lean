import SixthMoment.Numerator.U.Sources.Weights.ProfileLengths

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

private theorem supported_tuple_mass_le (q : QuadraticScales)
    (_hq : ∀ j, 0 ≤ q.size j) (n : Fin 7 → ℕ)
    (hn : ∀ j, (n j:ℝ) ∈ Icc (q.size j) (2*q.size j)) :
    (n 0:ℝ)*n 1*n 2*n 3*n 4*n 5 ≤ 64*q.mass := by
  have h := Finset.prod_le_prod₀ (s := Finset.univ)
    (f := fun j : Fin 6 => (n j.castSucc:ℝ))
    (g := fun j : Fin 6 => 2*q.size j.castSucc)
    (fun _ _ => Nat.cast_nonneg _)
    (fun j _ => (hn j.castSucc).2)
  calc
    _ = ∏ j : Fin 6, (n j.castSucc:ℝ) := by simp [Fin.prod_univ_six]
    _ ≤ ∏ j : Fin 6, 2*q.size j.castSucc := h
    _ = _ := by
      simp [Fin.prod_univ_six,QuadraticScales.size,QuadraticScales.mass,
        QuadraticScales.M,QuadraticScales.N]
      ring

theorem phase_supported_left_product_bounds (q : QuadraticScales)
    (hq : ∀ j, 0 ≤ q.size j) (n : Fin 7 → ℕ)
    (hn : ∀ j, (n j:ℝ) ∈ Icc (q.size j) (2*q.size j)) :
    q.A*q.M ≤ rectangularNearLeftProduct n ∧
      rectangularNearLeftProduct n ≤ 8*(q.A*q.M) := by
  have hA : 0 ≤ q.A := by simpa [QuadraticScales.size] using hq 0
  have hM₁ : 0 ≤ q.M₁ := by simpa [QuadraticScales.size] using hq 2
  have hM₂ : 0 ≤ q.M₂ := by simpa [QuadraticScales.size] using hq 3
  have ha := hn 0; have hm₁ := hn 2; have hm₂ := hn 3
  norm_num [QuadraticScales.size] at ha hm₁ hm₂
  unfold rectangularNearLeftProduct QuadraticScales.M
  constructor
  · calc
      q.A*(q.M₁*q.M₂) = q.A*q.M₁*q.M₂ := by ring
      _ ≤ _ := by gcongr <;> linarith
  · calc
      _ ≤ (2*q.A)*(2*q.M₁)*(2*q.M₂) := by gcongr <;> linarith
      _ = _ := by ring

theorem phase_supported_right_product_bounds (q : QuadraticScales)
    (hq : ∀ j, 0 ≤ q.size j) (n : Fin 7 → ℕ)
    (hn : ∀ j, (n j:ℝ) ∈ Icc (q.size j) (2*q.size j)) :
    q.B*q.N ≤ rectangularNearRightProduct n ∧
      rectangularNearRightProduct n ≤ 8*(q.B*q.N) := by
  have hB : 0 ≤ q.B := by simpa [QuadraticScales.size] using hq 1
  have hN₁ : 0 ≤ q.N₁ := by simpa [QuadraticScales.size] using hq 4
  have hN₂ : 0 ≤ q.N₂ := by simpa [QuadraticScales.size] using hq 5
  have hb := hn 1; have hn₁ := hn 4; have hn₂ := hn 5
  norm_num [QuadraticScales.size] at hb hn₁ hn₂
  unfold rectangularNearRightProduct QuadraticScales.N
  constructor
  · calc
      q.B*(q.N₁*q.N₂) = q.B*q.N₁*q.N₂ := by ring
      _ ≤ _ := by gcongr <;> linarith
  · calc
      _ ≤ (2*q.B)*(2*q.N₁)*(2*q.N₂) := by gcongr <;> linarith
      _ = _ := by ring

theorem phase_active_near_scales_comparable (q : QuadraticScales)
    (hq : ∀ j, 0 ≤ q.size j) (n : Fin 7 → ℕ)
    (hn : ∀ j, (n j:ℝ) ∈ Icc (q.size j) (2*q.size j))
    (hp : ∀ j, 0 < n j) (positive : Bool) (hrel : signedQuadraticRelation positive n)
    {η : ℝ} (hη : η ≤ 1/2) (hne : rectangularNearRelation η n) :
    q.A*q.M ≤ 32*(q.B*q.N) ∧ q.B*q.N ≤ 32*(q.A*q.M) := by
  have hL : 0 < rectangularNearLeftProduct n := by
    unfold rectangularNearLeftProduct
    exact mul_pos (mul_pos (by exact_mod_cast hp 0) (by exact_mod_cast hp 2))
      (by exact_mod_cast hp 3)
  have hR : 0 < rectangularNearRightProduct n := by
    unfold rectangularNearRightProduct
    exact mul_pos (mul_pos (by exact_mod_cast hp 1) (by exact_mod_cast hp 4))
      (by exact_mod_cast hp 5)
  have hgap := rectangular_signed_relation_abs_gap positive n hrel
  have hab : |rectangularNearLeftProduct n-rectangularNearRightProduct n| ≤
      η*Real.sqrt (rectangularNearLeftProduct n*rectangularNearRightProduct n) := by
    rw [hgap]
    simpa [rectangularNearRelation, rectangular_near_tuple_mass] using hne
  have hRL := rectangular_near_product_comparable hL hR.le hη hab
  have hLR := rectangular_near_product_comparable hR hL.le hη
    (by simpa [abs_sub_comm, mul_comm] using hab)
  have hsl := phase_supported_left_product_bounds q hq n hn
  have hsr := phase_supported_right_product_bounds q hq n hn
  constructor <;> linarith

theorem phase_active_near_gap_scale_bound (q : QuadraticScales)
    (hq : ∀ j, 0 ≤ q.size j) (n : Fin 7 → ℕ)
    (hn : ∀ j, (n j:ℝ) ∈ Icc (q.size j) (2*q.size j))
    {η : ℝ} (hη : 0 ≤ η) (hne : rectangularNearRelation η n) :
    q.H ≤ 8*η*Real.sqrt q.mass := by
  have hm := supported_tuple_mass_le q hq n hn
  have hsr := Real.sqrt_le_sqrt hm
  have hmass : 0 ≤ q.mass := by
    unfold QuadraticScales.mass QuadraticScales.M QuadraticScales.N
    have := hq 0; have := hq 1; have := hq 2
    have := hq 3; have := hq 4; have := hq 5
    norm_num [QuadraticScales.size] at *
    positivity
  have he : Real.sqrt (64*q.mass) = 8*Real.sqrt q.mass := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 64)]
    norm_num
  rw [he] at hsr
  have hh : q.H ≤ (n 6:ℝ) := by simpa [QuadraticScales.size] using (hn 6).1
  have hne' := hne
  unfold rectangularNearRelation at hne'
  have hηs := mul_le_mul_of_nonneg_left hsr hη
  nlinarith

theorem phase_active_near_nontrivial_range (q : QuadraticScales)
    (hq : ∀ j, 0 ≤ q.size j) (hAB : 0 < q.A*q.B) (n : Fin 7 → ℕ)
    (hn : ∀ j, (n j:ℝ) ∈ Icc (q.size j) (2*q.size j)) (hh : 0 < n 6)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : 8*η*(q.A*q.B) ≤ 1)
    (hne : rectangularNearRelation η n) : q.A*q.B ≤ q.M*q.N := by
  have hm := supported_tuple_mass_le q hq n hn
  have hsr := Real.sqrt_le_sqrt hm
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 64)] at hsr
  rw [show Real.sqrt (64:ℝ)=8 by norm_num] at hsr
  have hgap : (1:ℝ) ≤ n 6 := by exact_mod_cast Nat.succ_le_iff.mpr hh
  have hbound : 1 ≤ 8*η*Real.sqrt q.mass := by
    have hne' := hne
    unfold rectangularNearRelation at hne'
    have hηs := mul_le_mul_of_nonneg_left hsr hη
    nlinarith
  have hηpos : 0 < η := by
    by_contra h
    have he : η=0 := le_antisymm (le_of_not_gt h) hη
    simp only [he, mul_zero, zero_mul] at hbound
    norm_num at hbound
  have hs : q.A*q.B ≤ Real.sqrt q.mass := by
    nlinarith
  have hmass : 0 ≤ q.mass := by
    unfold QuadraticScales.mass QuadraticScales.M QuadraticScales.N
    have := hq 0; have := hq 1; have := hq 2
    have := hq 3; have := hq 4; have := hq 5
    norm_num [QuadraticScales.size] at *
    positivity
  have hsq := pow_le_pow_left₀ hAB.le hs 2
  rw [Real.sq_sqrt hmass] at hsq
  unfold QuadraticScales.mass at hsq
  nlinarith

end
end SixthMoment
