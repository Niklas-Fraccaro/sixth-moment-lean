import Sechstmoment.Numerator.U.Separation.UnitActualSource

namespace Sechstmoment
open Complex Source Real Set
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def boundaryProductFactor (f : Fin 4 → Bool) : ℝ :=
  (rectangularUnitMFactor f : ℝ)*rectangularUnitNFactor f
def boundaryEmbeddedTuple (f : Fin 4 → Bool) (n : Fin 7 → ℕ) : Fin 7 → ℕ :=
  boundaryCommonTuple 2 (rectangularUnitTuple f n)

theorem boundaryProductFactor_bounds (f : Fin 4 → Bool) :
    1≤boundaryProductFactor f ∧ boundaryProductFactor f≤16 := by
  have h := rectangular_unit_product_factors_bounds f
  unfold boundaryProductFactor
  constructor
  · exact_mod_cast (show 1≤rectangularUnitMFactor f*rectangularUnitNFactor f by
      simpa using Nat.mul_le_mul h.1 h.2.2.1)
  · exact_mod_cast (show rectangularUnitMFactor f*rectangularUnitNFactor f≤16 by
      simpa using Nat.mul_le_mul h.2.1 h.2.2.2)

theorem boundaryEmbedded_M (f : Fin 4 → Bool) (q : QuadraticScales) :
    (boundaryEmbeddedScales f q).M=(rectangularUnitMFactor f : ℝ)*q.M := by
  simp [boundaryEmbeddedScales,boundaryCommonScales,rectangularUnitScales,
    QuadraticScales.M,rectangularUnitMFactor]
  ring

theorem boundaryEmbedded_N (f : Fin 4 → Bool) (q : QuadraticScales) :
    (boundaryEmbeddedScales f q).N=(rectangularUnitNFactor f : ℝ)*q.N := by
  simp [boundaryEmbeddedScales,boundaryCommonScales,rectangularUnitScales,
    QuadraticScales.N,rectangularUnitNFactor]
  ring

theorem boundaryEmbedded_AB (f : Fin 4 → Bool) (q : QuadraticScales) :
    (boundaryEmbeddedScales f q).A*(boundaryEmbeddedScales f q).B=
      4*boundaryProductFactor f*(q.A*q.B) := by
  simp [boundaryEmbeddedScales,boundaryCommonScales,rectangularUnitScales,boundaryProductFactor]
  ring

theorem boundaryEmbedded_MN (f : Fin 4 → Bool) (q : QuadraticScales) :
    (boundaryEmbeddedScales f q).M*(boundaryEmbeddedScales f q).N=
      boundaryProductFactor f*(q.M*q.N) := by
  rw [boundaryEmbedded_M,boundaryEmbedded_N]
  unfold boundaryProductFactor
  ring

theorem boundaryEmbedded_left_scale_product (f : Fin 4 → Bool) (q : QuadraticScales) :
    (boundaryEmbeddedScales f q).A*(boundaryEmbeddedScales f q).M=
      2*boundaryProductFactor f*(q.A*q.M) := by
  rw [boundaryEmbedded_M]
  simp [boundaryEmbeddedScales,boundaryCommonScales,rectangularUnitScales,boundaryProductFactor]
  ring

theorem boundaryEmbedded_right_scale_product (f : Fin 4 → Bool) (q : QuadraticScales) :
    (boundaryEmbeddedScales f q).B*(boundaryEmbeddedScales f q).N=
      2*boundaryProductFactor f*(q.B*q.N) := by
  rw [boundaryEmbedded_N]
  simp [boundaryEmbeddedScales,boundaryCommonScales,rectangularUnitScales,boundaryProductFactor]
  ring

theorem boundaryEmbedded_H (f : Fin 4 → Bool) (q : QuadraticScales) :
    (boundaryEmbeddedScales f q).H=2*boundaryProductFactor f*q.H := by
  simp [boundaryEmbeddedScales,boundaryCommonScales,rectangularUnitScales,boundaryProductFactor]
  ring

theorem boundaryEmbedded_comparability (f : Fin 4 → Bool) (q : QuadraticScales)
    {K : ℝ} (hl : q.A*q.M≤K*(q.B*q.N)) (hr : q.B*q.N≤K*(q.A*q.M)) :
    (boundaryEmbeddedScales f q).A*(boundaryEmbeddedScales f q).M≤
      K*((boundaryEmbeddedScales f q).B*(boundaryEmbeddedScales f q).N) ∧
    (boundaryEmbeddedScales f q).B*(boundaryEmbeddedScales f q).N≤
      K*((boundaryEmbeddedScales f q).A*(boundaryEmbeddedScales f q).M) := by
  rw [boundaryEmbedded_left_scale_product,boundaryEmbedded_right_scale_product]
  have hc : 0≤2*boundaryProductFactor f := by
    have := (boundaryProductFactor_bounds f).1
    positivity
  constructor
  · simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left hl hc
  · simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_left hr hc

theorem boundaryEmbedded_nontrivial_range (f : Fin 4 → Bool) (q : QuadraticScales)
    (h : q.A*q.B≤q.M*q.N) :
    (boundaryEmbeddedScales f q).A*(boundaryEmbeddedScales f q).B≤
      4*((boundaryEmbeddedScales f q).M*(boundaryEmbeddedScales f q).N) := by
  rw [boundaryEmbedded_AB,boundaryEmbedded_MN]
  have hc : 0≤boundaryProductFactor f := le_trans (by norm_num) (boundaryProductFactor_bounds f).1
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num) hc)

theorem boundaryEmbedded_MN_upper (f : Fin 4 → Bool) (q : QuadraticScales)
    (hq : 0≤q.M*q.N) :
    (boundaryEmbeddedScales f q).M*(boundaryEmbeddedScales f q).N≤16*(q.M*q.N) := by
  rw [boundaryEmbedded_MN]
  exact mul_le_mul_of_nonneg_right (boundaryProductFactor_bounds f).2 hq

theorem boundaryEmbedded_gap_shape (f : Fin 4 → Bool) (q : QuadraticScales)
    {K ε : ℝ} (hK : 0≤K) (hε : 0≤ε) (hAB : 0<q.A*q.B)
    (hH : q.H≤K*(q.A*q.B)^(1/2+ε)) :
    (boundaryEmbeddedScales f q).H≤4*K*
      ((boundaryEmbeddedScales f q).A*(boundaryEmbeddedScales f q).B)^(1/2+ε) := by
  let c := boundaryProductFactor f
  have hc1 : 1≤c := (boundaryProductFactor_bounds f).1
  have hc16 : c≤16 := (boundaryProductFactor_bounds f).2
  have hc : 0≤c := by linarith
  have hr : Real.sqrt c≤4 := by
    have hs := Real.sqrt_le_sqrt hc16
    norm_num at hs
    exact hs
  have hs : 2*c≤4*(4*c)^(1/2:ℝ) := by
    rw [←Real.sqrt_eq_rpow,Real.sqrt_mul (by norm_num : (0 : ℝ)≤4)]
    norm_num
    have he := Real.sq_sqrt hc
    have hp := Real.sqrt_nonneg c
    nlinarith
  have hsε : (4*c)^(1/2:ℝ)≤(4*c)^(1/2+ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hfactor : 2*c≤4*(4*c)^(1/2+ε) :=
    hs.trans (mul_le_mul_of_nonneg_left hsε (by norm_num))
  rw [boundaryEmbedded_H,boundaryEmbedded_AB,Real.mul_rpow (by linarith : 0≤4*c) hAB.le]
  change 2*c*q.H≤4*K*((4*c)^(1/2+ε)*(q.A*q.B)^(1/2+ε))
  calc
    _ ≤ 2*c*(K*(q.A*q.B)^(1/2+ε)) := mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ 4*(4*c)^(1/2+ε)*(K*(q.A*q.B)^(1/2+ε)) :=
      mul_le_mul_of_nonneg_right hfactor (mul_nonneg hK (Real.rpow_nonneg hAB.le _))
    _ = _ := by ring

theorem boundaryEmbedded_tuple_left (f : Fin 4 → Bool) (n : Fin 7 → ℕ) :
    rectangularNearLeftProduct (boundaryEmbeddedTuple f n)=
      2*boundaryProductFactor f*rectangularNearLeftProduct n := by
  simp [boundaryEmbeddedTuple,boundaryCommonTuple,boundaryCommonFactors,
    rectangularUnitTuple,rectangularUnitFactors,rectangularNearLeftProduct,
    boundaryProductFactor,rectangularUnitMFactor,rectangularUnitNFactor]
  ring

theorem boundaryEmbedded_tuple_right (f : Fin 4 → Bool) (n : Fin 7 → ℕ) :
    rectangularNearRightProduct (boundaryEmbeddedTuple f n)=
      2*boundaryProductFactor f*rectangularNearRightProduct n := by
  simp [boundaryEmbeddedTuple,boundaryCommonTuple,boundaryCommonFactors,
    rectangularUnitTuple,rectangularUnitFactors,rectangularNearRightProduct,
    boundaryProductFactor,rectangularUnitMFactor,rectangularUnitNFactor]
  ring

theorem boundaryEmbedded_tuple_gap (f : Fin 4 → Bool) (n : Fin 7 → ℕ) :
    ((boundaryEmbeddedTuple f n 6) : ℝ)=2*boundaryProductFactor f*(n 6 : ℝ) := by
  simp [boundaryEmbeddedTuple,boundaryCommonTuple,boundaryCommonFactors,
    rectangularUnitTuple,rectangularUnitFactors,boundaryProductFactor]
  ring

theorem boundaryEmbedded_near_relation (f : Fin 4 → Bool) (η : ℝ) (n : Fin 7 → ℕ) :
    rectangularNearRelation η (boundaryEmbeddedTuple f n) ↔ rectangularNearRelation η n := by
  let L := 2*boundaryProductFactor f
  have hL : 0<L := by
    have := (boundaryProductFactor_bounds f).1
    dsimp [L]
    positivity
  have he : Real.sqrt (rectangularNearLeftProduct (boundaryEmbeddedTuple f n)*
      rectangularNearRightProduct (boundaryEmbeddedTuple f n))=
      L*Real.sqrt (rectangularNearLeftProduct n*rectangularNearRightProduct n) := by
    rw [boundaryEmbedded_tuple_left,boundaryEmbedded_tuple_right]
    change Real.sqrt ((L*rectangularNearLeftProduct n)*(L*rectangularNearRightProduct n))=_
    rw [show (L*rectangularNearLeftProduct n)*(L*rectangularNearRightProduct n)=
      L^2*(rectangularNearLeftProduct n*rectangularNearRightProduct n) by ring]
    rw [Real.sqrt_mul (sq_nonneg L),Real.sqrt_sq_eq_abs,abs_of_pos hL]
  unfold rectangularNearRelation
  rw [rectangular_near_tuple_mass,rectangular_near_tuple_mass,boundaryEmbedded_tuple_gap,he]
  change L*(n 6 : ℝ)≤η*(L*Real.sqrt (rectangularNearLeftProduct n*rectangularNearRightProduct n)) ↔ _
  rw [mul_left_comm η L]
  exact mul_le_mul_iff_right₀ hL

theorem boundaryEmbedded_tuple_index (f : Fin 4 → Bool) (q : QuadraticScales)
    (hq : ∀ j, 0<q.size j) (n : Fin 7 → ℕ) :
    boundaryEmbeddedTuple f n∈quadraticIndexSet (boundaryEmbeddedScales f q) ↔
      n∈quadraticIndexSet q := by
  unfold boundaryEmbeddedTuple boundaryEmbeddedScales
  rw [boundaryCommon_index_mem (by norm_num) _
    (fun j => by
      rw [rectangular_unit_scales_size]
      exact mul_pos (by exact_mod_cast rectangular_unit_factors_pos f j) (hq j))]
  exact rectangular_unit_index_mem f q hq n

theorem boundaryEmbedded_tuple_signed (f : Fin 4 → Bool) (positive : Bool) (n : Fin 7 → ℕ) :
    signedQuadraticRelation positive (boundaryEmbeddedTuple f n) ↔ signedQuadraticRelation positive n := by
  unfold boundaryEmbeddedTuple
  rw [boundaryCommon_signed_relation (by norm_num)]
  exact rectangular_unit_signed_relation f positive n

theorem boundaryEmbedded_A_bounds (f : Fin 4 → Bool) (q : QuadraticScales)
    (hA : 0≤q.A) : q.A≤(boundaryEmbeddedScales f q).A ∧ (boundaryEmbeddedScales f q).A≤8*q.A := by
  have h := rectangular_unit_product_factors_bounds f
  have hn1 : (1 : ℝ)≤rectangularUnitNFactor f := by exact_mod_cast h.2.2.1
  have hn4 : (rectangularUnitNFactor f : ℝ)≤4 := by exact_mod_cast h.2.2.2
  change q.A≤2*((rectangularUnitNFactor f : ℝ)*q.A) ∧
    2*((rectangularUnitNFactor f : ℝ)*q.A)≤8*q.A
  have hl := mul_le_mul_of_nonneg_right hn1 hA
  have hu := mul_le_mul_of_nonneg_right hn4 hA
  constructor <;> nlinarith

theorem boundaryEmbedded_B_bounds (f : Fin 4 → Bool) (q : QuadraticScales)
    (hB : 0≤q.B) : q.B≤(boundaryEmbeddedScales f q).B ∧ (boundaryEmbeddedScales f q).B≤8*q.B := by
  have h := rectangular_unit_product_factors_bounds f
  have hm1 : (1 : ℝ)≤rectangularUnitMFactor f := by exact_mod_cast h.1
  have hm4 : (rectangularUnitMFactor f : ℝ)≤4 := by exact_mod_cast h.2.1
  change q.B≤2*((rectangularUnitMFactor f : ℝ)*q.B) ∧
    2*((rectangularUnitMFactor f : ℝ)*q.B)≤8*q.B
  have hl := mul_le_mul_of_nonneg_right hm1 hB
  have hu := mul_le_mul_of_nonneg_right hm4 hB
  constructor <;> nlinarith

theorem boundaryEmbedded_profile_lengths (f : Fin 4 → Bool) (q : QuadraticScales)
    {T a b ν μ : ℝ} (hA : 0≤q.A) (hB : 0≤q.B)
    (hAl : T^ν≤2*q.A) (hBl : T^μ≤2*q.B) (hAu : q.A≤T^a) (hBu : q.B≤T^b) :
    T^ν≤2*(boundaryEmbeddedScales f q).A ∧ T^μ≤2*(boundaryEmbeddedScales f q).B ∧
      (boundaryEmbeddedScales f q).A≤8*T^a ∧ (boundaryEmbeddedScales f q).B≤8*T^b := by
  have ha := boundaryEmbedded_A_bounds f q hA
  have hb := boundaryEmbedded_B_bounds f q hB
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem boundaryEmbedded_tuple_coordinate (f : Fin 4 → Bool) (n : Fin 7 → ℕ) (j : Fin 7) :
    ((boundaryEmbeddedTuple f n j) : ℝ)=
      (boundaryCommonFactors 2 j : ℝ)*(rectangularUnitFactors f j : ℝ)*(n j : ℝ) := by
  simp [boundaryEmbeddedTuple,boundaryCommonTuple,rectangularUnitTuple,mul_assoc]

theorem boundaryEmbedded_scale_coordinate (f : Fin 4 → Bool) (q : QuadraticScales) (j : Fin 7) :
    (boundaryEmbeddedScales f q).size j=
      (boundaryCommonFactors 2 j : ℝ)*(rectangularUnitFactors f j : ℝ)*q.size j := by
  unfold boundaryEmbeddedScales
  rw [boundaryCommon_scale_size,rectangular_unit_scales_size]
  ring

theorem boundaryEmbedded_tuple_support (f : Fin 4 → Bool) (q : QuadraticScales) (n : Fin 7 → ℕ)
    (hn : ∀ j, (n j : ℝ)∈Icc (q.size j) (2*q.size j)) :
    ∀ j, ((boundaryEmbeddedTuple f n j) : ℝ)∈
      Icc ((boundaryEmbeddedScales f q).size j) (2*(boundaryEmbeddedScales f q).size j) := by
  intro j
  rw [boundaryEmbedded_tuple_coordinate,boundaryEmbedded_scale_coordinate]
  have hc : 0≤(boundaryCommonFactors 2 j : ℝ)*(rectangularUnitFactors f j : ℝ) := by positivity
  constructor
  · exact mul_le_mul_of_nonneg_left (hn j).1 hc
  · have h := mul_le_mul_of_nonneg_left (hn j).2 hc
    nlinarith

theorem boundaryEmbedded_tuple_positive (f : Fin 4 → Bool) (n : Fin 7 → ℕ)
    (hn : ∀ j, 0<n j) : ∀ j, 0<boundaryEmbeddedTuple f n j := by
  intro j
  exact Nat.mul_pos (boundaryCommon_factor_pos (by norm_num) j)
    (Nat.mul_pos (rectangular_unit_factors_pos f j) (hn j))

end
end Sechstmoment
