import Sechstmoment.Numerator.U.Diagonal.NearMassNumeric
import Sechstmoment.Numerator.U.Diagonal.NearMassPowers
import Sechstmoment.Numerator.U.Replacement.WeightReplacementFarFinite
import Sechstmoment.Numerator.U.Separation.UnitActualScales

namespace Sechstmoment
open Real Source Set Filter Asymptotics
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def nearSmoothLeftScale (k : Fin 4→ℕ) : ℝ :=
  rectangularAFESmoothScale (k 0)*rectangularAFESmoothScale (k 1)
def nearSmoothRightScale (k : Fin 4→ℕ) : ℝ :=
  rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3)
def nearSmoothLowerCap (x : ℝ) : ℕ := max 1 ⌊x⌋₊
def nearSmoothUpperCap (x : ℝ) : ℕ := ⌊4*x⌋₊
def nearSmoothRootCap (Q : ℕ) : ℕ := ⌈Real.sqrt (Q:ℝ)⌉₊

theorem nearSmoothScale_lower (k : Fin 4→ℕ) :
    4/9≤nearSmoothLeftScale k ∧ 4/9≤nearSmoothRightScale k := by
  have hs (j : Fin 4) := boundaryActual_scale_ge_two_thirds (k j)
  constructor
  · unfold nearSmoothLeftScale
    nlinarith [mul_le_mul (hs 0) (hs 1) (by norm_num : (0:ℝ)≤2/3)
      (by linarith [hs 0] : 0≤rectangularAFESmoothScale (k 0))]
  · unfold nearSmoothRightScale
    nlinarith [mul_le_mul (hs 2) (hs 3) (by norm_num : (0:ℝ)≤2/3)
      (by linarith [hs 2] : 0≤rectangularAFESmoothScale (k 2))]

theorem nearSmoothCaps_bounds {x : ℝ} (hx : 4/9≤x) :
    0<nearSmoothLowerCap x ∧ 0<nearSmoothUpperCap x ∧
      nearSmoothUpperCap x≤8*nearSmoothLowerCap x ∧
      (nearSmoothUpperCap x:ℝ)≤4*x := by
  have hx0 : 0≤x := by linarith
  have hlo : (1:ℝ)≤nearSmoothLowerCap x := by
    exact_mod_cast (le_max_left 1 ⌊x⌋₊)
  have hfloor : (⌊x⌋₊:ℝ)≤nearSmoothLowerCap x := by
    exact_mod_cast (le_max_right 1 ⌊x⌋₊)
  have hxlo : x≤2*(nearSmoothLowerCap x:ℝ) := by
    have hf := Nat.lt_floor_add_one x
    nlinarith
  have hup := Nat.floor_le (by linarith : 0≤4*x)
  have hp : 0<nearSmoothUpperCap x := by
    have hf : 1≤⌊4*x⌋₊ := (Nat.le_floor_iff (by linarith : 0≤4*x)).mpr (by norm_num; linarith)
    change 0<⌊4*x⌋₊
    omega
  refine ⟨by unfold nearSmoothLowerCap; omega,hp,?_,hup⟩
  exact_mod_cast (show (nearSmoothUpperCap x:ℝ)≤8*nearSmoothLowerCap x by
    change (⌊4*x⌋₊:ℝ)≤8*nearSmoothLowerCap x
    nlinarith)

theorem nearSmoothRootCap_bounds {Q : ℕ} (hQ : 0<Q) :
    Q≤(nearSmoothRootCap Q)^2 ∧
      (nearSmoothRootCap Q:ℝ)≤2*Real.sqrt (Q:ℝ) ∧
      (nearSmoothRootCap Q:ℝ)≤2*Q := by
  have hQ1 : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hs1 : 1≤Real.sqrt (Q:ℝ) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs := Nat.le_ceil (Real.sqrt (Q:ℝ))
  have hh := Nat.ceil_lt_add_one (Real.sqrt_nonneg (Q:ℝ))
  have hsq := Real.sq_sqrt (Nat.cast_nonneg Q)
  have hK : (nearSmoothRootCap Q:ℝ)≤2*Real.sqrt (Q:ℝ) := by
    change (⌈Real.sqrt (Q:ℝ)⌉₊:ℝ)≤2*Real.sqrt (Q:ℝ)
    linarith
  refine ⟨?_,hK,?_⟩
  · have hr : (Q:ℝ)≤(nearSmoothRootCap Q:ℝ)^2 := by
      change (Q:ℝ)≤(⌈Real.sqrt (Q:ℝ)⌉₊:ℝ)^2
      nlinarith [Real.sqrt_nonneg (Q:ℝ)]
    exact_mod_cast hr
  · apply hK.trans
    have hb : Real.sqrt (Q:ℝ)≤Q := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
    nlinarith

theorem actualSmoothNear_product_support (k n : Fin 4→ℕ)
    (hw : rectangularAFESmoothWeight k n≠0) :
    nearSmoothLowerCap (nearSmoothLeftScale k)≤(n 0+1)*(n 1+1) ∧
    (n 0+1)*(n 1+1)≤nearSmoothUpperCap (nearSmoothLeftScale k) ∧
    nearSmoothLowerCap (nearSmoothRightScale k)≤(n 2+1)*(n 3+1) ∧
    (n 2+1)*(n 3+1)≤nearSmoothUpperCap (nearSmoothRightScale k) := by
  have hs (j : Fin 4) : (n j+1:ℝ)∈Icc (rectangularAFESmoothScale (k j))
      (2*rectangularAFESmoothScale (k j)) := by
    have hj := (Finset.prod_ne_zero_iff.mp hw) j (Finset.mem_univ j)
    have hh := rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hj)
    unfold rectangularAFESmoothScale
    constructor
    · have h := (le_div_iff₀ (pow_pos (by norm_num : (0:ℝ)<3/2) (k j))).mp hh.1
      apply (div_le_iff₀ (by norm_num : (0:ℝ)<3/2)).mpr
      nlinarith
    · have h := (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<3/2) (k j))).mp hh.2
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<3/2)).mpr
      nlinarith
  have hsp (j : Fin 4) := boundaryActual_scale_pos (k j)
  have hm : nearSmoothLeftScale k≤((n 0+1)*(n 1+1):ℕ) ∧
      (((n 0+1)*(n 1+1):ℕ):ℝ)≤4*nearSmoothLeftScale k := by
    unfold nearSmoothLeftScale
    push_cast
    constructor
    · exact mul_le_mul (hs 0).1 (hs 1).1 (hsp 1).le (by positivity)
    · nlinarith [mul_le_mul (hs 0).2 (hs 1).2 (by positivity)
        (mul_nonneg (by norm_num) (hsp 0).le)]
  have hn : nearSmoothRightScale k≤((n 2+1)*(n 3+1):ℕ) ∧
      (((n 2+1)*(n 3+1):ℕ):ℝ)≤4*nearSmoothRightScale k := by
    unfold nearSmoothRightScale
    push_cast
    constructor
    · exact mul_le_mul (hs 2).1 (hs 3).1 (hsp 3).le (by positivity)
    · nlinarith [mul_le_mul (hs 2).2 (hs 3).2 (by positivity)
        (mul_nonneg (by norm_num) (hsp 2).le)]
  refine ⟨?_,?_,?_,?_⟩
  · unfold nearSmoothLowerCap
    apply max_le (Nat.succ_le_iff.mpr (by positivity))
    have hh := (Nat.floor_le (by linarith [nearSmoothScale_lower k] : 0≤nearSmoothLeftScale k)).trans hm.1
    exact_mod_cast hh
  · exact (Nat.le_floor_iff (by linarith [nearSmoothScale_lower k] : 0≤4*nearSmoothLeftScale k)).mpr hm.2
  · unfold nearSmoothLowerCap
    apply max_le (Nat.succ_le_iff.mpr (by positivity))
    have hh := (Nat.floor_le (by linarith [nearSmoothScale_lower k] : 0≤nearSmoothRightScale k)).trans hn.1
    exact_mod_cast hh
  · exact (Nat.le_floor_iff (by linarith [nearSmoothScale_lower k] : 0≤4*nearSmoothRightScale k)).mpr hn.2

theorem integer_near_gap_floor {a b : ℕ} {E : ℝ} (hE : 0≤E)
    (hab : |(a:ℝ)-(b:ℝ)|≤E) : a≤b+⌊E⌋₊ ∧ b≤a+⌊E⌋₊ := by
  by_cases h : a≤b
  · have hr : (a:ℝ)≤b := by exact_mod_cast h
    have hd : ((b-a:ℕ):ℝ)≤E := by
      rw [Nat.cast_sub h]
      rw [abs_of_nonpos (sub_nonpos.mpr hr)] at hab
      linarith
    have hh : b-a≤⌊E⌋₊ := (Nat.le_floor_iff hE).mpr hd
    omega
  · have h' : b≤a := by omega
    have hr : (b:ℝ)≤a := by exact_mod_cast h'
    have hd : ((a-b:ℕ):ℝ)≤E := by
      rw [Nat.cast_sub h']
      rw [abs_of_nonneg (sub_nonneg.mpr hr)] at hab
      exact hab
    have hh : a-b≤⌊E⌋₊ := (Nat.le_floor_iff hE).mpr hd
    omega

def actualSmoothNearIndices (T ρ : ℝ) (u v : ℕ) (k : Fin 4→ℕ) : Finset (Fin 4→ℕ) :=
  (rectangularAFESmoothBox k).filter fun n => rectangularAFESmoothWeight k n≠0 ∧
    a03ActualWeightReplacementNearSelection T ρ u v n

theorem actualSmoothNearIndices_support {T ρ : ℝ} (hT : 0<T) (u v : ℕ)
    (k : Fin 4→ℕ) (n : Fin 4→ℕ) (hn : n∈actualSmoothNearIndices T ρ u v k) :
    bblrAFEFactorPairs n∈positiveNearFactorBlock
      (nearSmoothLowerCap (nearSmoothLeftScale k)) (nearSmoothUpperCap (nearSmoothLeftScale k))
      (nearSmoothLowerCap (nearSmoothRightScale k)) (nearSmoothUpperCap (nearSmoothRightScale k))
      (u+1) (v+1)
      ⌊T^(ρ-1)*Real.sqrt ((u+1:ℝ)*(v+1)*
        (nearSmoothUpperCap (nearSmoothLeftScale k):ℝ)*(nearSmoothUpperCap (nearSmoothRightScale k):ℝ))⌋₊ := by
  obtain ⟨_,hw,hnear⟩ := Finset.mem_filter.mp hn
  have hs := actualSmoothNear_product_support k n hw
  let P := nearSmoothUpperCap (nearSmoothLeftScale k)
  let Q := nearSmoothUpperCap (nearSmoothRightScale k)
  have hwidth : 0≤T^(ρ-1)*Real.sqrt ((u+1:ℝ)*(v+1)*(P:ℝ)*Q) := by positivity
  have hprod : ((n 0+1:ℝ)*(n 1+1))*((n 2+1:ℝ)*(n 3+1))≤(P:ℝ)*Q := by
    have hm : (n 0+1:ℝ)*(n 1+1)≤P := by exact_mod_cast hs.2.1
    have hnr : (n 2+1:ℝ)*(n 3+1)≤Q := by exact_mod_cast hs.2.2.2
    exact mul_le_mul hm hnr (by positivity) (by positivity)
  have hlarge : Real.sqrt ((u+1:ℝ)*(v+1)*(n 0+1)*(n 1+1)*(n 2+1)*(n 3+1))≤
      Real.sqrt ((u+1:ℝ)*(v+1)*(P:ℝ)*Q) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul_of_nonneg_left hprod (by positivity : 0≤(u+1:ℝ)*(v+1))]
  have hgap : |(((u+1)*(n 0+1)*(n 1+1):ℕ):ℝ)-
      (((v+1)*(n 2+1)*(n 3+1):ℕ):ℝ)|≤
      T^(ρ-1)*Real.sqrt ((u+1:ℝ)*(v+1)*(P:ℝ)*Q) := by
    exact hnear.trans (mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hT.le _))
  have hfloor := integer_near_gap_floor hwidth hgap
  apply Finset.mem_filter.mpr
  refine ⟨mem_positiveNearFactorRectangle.mpr ⟨?_,?_⟩,hs.1,hs.2.2.1⟩
  · exact mem_positiveProductFactorPairs.mpr ⟨by omega,by omega,hs.2.1⟩
  · exact Finset.mem_filter.mpr ⟨mem_positiveProductFactorPairs.mpr
      ⟨by omega,by omega,hs.2.2.2⟩,by simpa [Nat.mul_assoc] using hfloor.1,
      by simpa [Nat.mul_assoc] using hfloor.2⟩

theorem actualSmoothNearCaps_product_cutoff {T η : ℝ} (k : Fin 4→ℕ)
    (hk : k∈rectangularAFEProductScaleGrid (T^(2+η))) :
    (nearSmoothUpperCap (nearSmoothLeftScale k):ℝ)*
      nearSmoothUpperCap (nearSmoothRightScale k)≤16*T^(2+η) := by
  have hl := nearSmoothCaps_bounds (nearSmoothScale_lower k).1
  have hr := nearSmoothCaps_bounds (nearSmoothScale_lower k).2
  have hsc : nearSmoothLeftScale k*nearSmoothRightScale k≤T^(2+η) := by
    simpa [nearSmoothLeftScale,nearSmoothRightScale,Fin.prod_univ_four,mul_assoc]
      using (Finset.mem_filter.mp hk).2
  have hh := mul_le_mul hl.2.2.2 hr.2.2.2 (Nat.cast_nonneg _)
    (show 0≤4*nearSmoothLeftScale k by linarith [nearSmoothScale_lower k])
  nlinarith

def actualSmoothNearMass (T ρ : ℝ) (u v : ℕ) (k : Fin 4→ℕ) : ℝ :=
  ∑ n∈actualSmoothNearIndices T ρ u v k,
    positiveNearFactorWeight (u+1) (v+1) (bblrAFEFactorPairs n)

theorem actualSmoothNearMass_le_power {T η ρ : ℝ} (hT : 1≤T) (hη : 0≤η)
    (u v : ℕ) (k : Fin 4→ℕ) (hk : k∈rectangularAFEProductScaleGrid (T^(2+η))) :
    actualSmoothNearMass T ρ u v k≤
      320*(bblrNearMassLogRadius T η)^2*
        (T^(ρ+η/2)+T^(1/2+η/4)) := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  let L := nearSmoothLowerCap (nearSmoothLeftScale k)
  let P := nearSmoothUpperCap (nearSmoothLeftScale k)
  let J := nearSmoothLowerCap (nearSmoothRightScale k)
  let Q := nearSmoothUpperCap (nearSmoothRightScale k)
  let Kp := nearSmoothRootCap P
  let Kq := nearSmoothRootCap Q
  let H := ⌊T^(ρ-1)*Real.sqrt ((u+1:ℝ)*(v+1)*(P:ℝ)*Q)⌋₊
  let R := bblrNearMassLogRadius T η
  have hl := nearSmoothCaps_bounds (nearSmoothScale_lower k).1
  have hj := nearSmoothCaps_bounds (nearSmoothScale_lower k).2
  have hP : 0<P := hl.2.1
  have hQ : 0<Q := hj.2.1
  have hp := nearSmoothRootCap_bounds hP
  have hq := nearSmoothRootCap_bounds hQ
  have hcut : (P:ℝ)*Q≤16*T^(2+η) := actualSmoothNearCaps_product_cutoff k hk
  have hcut' : (Q:ℝ)*P≤16*T^(2+η) := by simpa [mul_comm] using hcut
  have hKp : Kp≤2*P := by exact_mod_cast hp.2.2
  have hKq : Kq≤2*Q := by exact_mod_cast hq.2.2
  have hH : (H:ℝ)≤T^(ρ-1)*Real.sqrt ((u+1:ℝ)*(v+1)*(P:ℝ)*Q) :=
    Nat.floor_le (by positivity)
  have hHcast : (H:ℝ)≤T^(ρ-1)*Real.sqrt (((u+1:ℕ):ℝ)*((v+1:ℕ):ℝ)*(P:ℝ)*Q) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hH
  have hs : (actualSmoothNearIndices T ρ u v k).image bblrAFEFactorPairs ⊆
      positiveNearFactorBlock L P J Q (u+1) (v+1) H := by
    intro pq hpq
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hpq
    exact actualSmoothNearIndices_support hTp u v k n hn
  have hmass : actualSmoothNearMass T ρ u v k≤
      80*R^2*(T^(ρ-1)*Real.sqrt ((P:ℝ)*Q)+Real.sqrt ((min P Q:ℕ):ℝ)) := by
    calc
      _ = ∑ pq∈(actualSmoothNearIndices T ρ u v k).image bblrAFEFactorPairs,
          positiveNearFactorWeight (u+1) (v+1) pq := by
        unfold actualSmoothNearMass
        rw [Finset.sum_image]
        exact fun _ _ _ _ he => bblrAFEFactorPairs_injective he
      _ ≤ ∑ pq∈positiveNearFactorBlock L P J Q (u+1) (v+1) H,
          positiveNearFactorWeight (u+1) (v+1) pq :=
        Finset.sum_le_sum_of_subset_of_nonneg hs
          (fun pq _ _ => positiveNearFactorWeight_nonneg _ _ pq)
      _ ≤ _ := positiveNearFactorBlock_mass_le_symmetric (by omega) (by omega)
        hl.1 hj.1 hP hQ hl.2.2.1 hj.2.2.1 hp.1 hq.1 hp.2.1 hq.2.1 hHcast
        (Real.rpow_nonneg hTp.le _) (bblrNearMassLogRadius_one_le hT hη)
        (bblrNearMass_harmonic_P_le_radius hT hη hP hQ hcut)
        (bblrNearMass_harmonic_P_le_radius hT hη hQ hP hcut')
        (bblrNearMass_harmonic_K_le_radius hT hη hQ hP hcut' hKp)
        (bblrNearMass_harmonic_K_le_radius hT hη hP hQ hcut hKq)
  have hsmall : Real.sqrt ((min P Q:ℕ):ℝ)≤2*T^(1/2+η/4) := by
    rcases le_total P Q with hPQ | hQP
    · rw [min_eq_left hPQ]
      exact bblrNearMass_sqrt_small_product_le_power hT hPQ hcut
    · rw [min_eq_right hQP]
      exact bblrNearMass_sqrt_small_product_le_power hT hQP hcut'
  have hlarge : T^(ρ-1)*Real.sqrt ((P:ℝ)*Q)≤4*T^(ρ+η/2) := by
    calc
      _ ≤ T^(ρ-1)*(4*T^(1+η/2)) := mul_le_mul_of_nonneg_left
        (bblrNearMass_sqrt_product_le_power hT hcut) (Real.rpow_nonneg hTp.le _)
      _ = _ := by rw [show T^(ρ-1)*(4*T^(1+η/2))=4*(T^(ρ-1)*T^(1+η/2)) by ring,
        ← Real.rpow_add hTp]; congr 2; ring
  apply hmass.trans
  change 80*R^2*(T^(ρ-1)*Real.sqrt ((P:ℝ)*Q)+Real.sqrt ((min P Q:ℕ):ℝ))≤_
  nlinarith [mul_le_mul_of_nonneg_left hsmall (sq_nonneg R),
    mul_le_mul_of_nonneg_left hlarge (sq_nonneg R),Real.rpow_nonneg hTp.le (1/2+η/4)]

theorem actualSmoothWeight_le_one (k n : Fin 4→ℕ) : rectangularAFESmoothWeight k n≤1 := by
  unfold rectangularAFESmoothWeight
  simpa only [Finset.prod_const_one] using Finset.prod_le_prod₀
    (fun _ _ => rectangularSmoothBlockWeight_nonneg _)
    (fun _ _ => rectangularSmoothBlockWeight_le_one _)

def actualSmoothNearWeightedMass (T ρ : ℝ) (u v : ℕ) (k : Fin 4→ℕ) : ℝ :=
  ∑ n∈rectangularAFESmoothBox k,
    if a03ActualWeightReplacementNearSelection T ρ u v n then
      rectangularAFESmoothWeight k n*
        positiveNearFactorWeight (u+1) (v+1) (bblrAFEFactorPairs n) else 0

theorem actualSmoothNearWeightedMass_le_mass (T ρ : ℝ) (u v : ℕ) (k : Fin 4→ℕ) :
    actualSmoothNearWeightedMass T ρ u v k≤actualSmoothNearMass T ρ u v k := by
  unfold actualSmoothNearWeightedMass actualSmoothNearMass actualSmoothNearIndices
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hs : a03ActualWeightReplacementNearSelection T ρ u v n
  · by_cases hw : rectangularAFESmoothWeight k n=0
    · simp [hs,hw]
    · rw [ite_eq_left hs,ite_eq_left (show rectangularAFESmoothWeight k n≠0 ∧
        a03ActualWeightReplacementNearSelection T ρ u v n from ⟨hw,hs⟩)]
      exact mul_le_of_le_one_left (positiveNearFactorWeight_nonneg _ _ _)
        (actualSmoothWeight_le_one k n)
  · simp [hs]

end
end Sechstmoment
