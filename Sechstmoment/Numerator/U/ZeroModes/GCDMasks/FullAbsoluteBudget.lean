import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.AbsoluteConvergence

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000

def a03NativeGCDSpatialBudget (Y : ℝ) : ℝ :=
  (40/91:ℝ)*Y^(7/2:ℝ)+(40/99:ℝ)*Y^(9/2:ℝ)

def a03NativeGCDFullBudgetRow (T e : ℝ) (k : ℕ) (C : ℝ)
    (f g : ℝ→ℝ) (u v : ℕ) : ℝ :=
  (|f (Real.log (u+1:ℝ)/Real.log T)| * |g (Real.log (v+1:ℝ)/Real.log T)| *
    C*T^e*(Real.log T)^k/((u+1:ℝ)*(v+1:ℝ)*T^2))*
      a03NativeGCDSpatialBudget (T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ)))

def a03NativeGCDFullBudget (T a b e : ℝ) (k : ℕ) (C : ℝ) (f g : ℝ→ℝ) : ℝ :=
  T*∑ _positive : Bool,∑ u∈Finset.range ⌊T^a⌋₊,∑ v∈Finset.range ⌊T^b⌋₊,
    a03NativeGCDFullBudgetRow T e k C f g u v

def a03NativeGCDFullBudgetPower (a b : ℝ) : ℝ :=
  9/2+(13/4:ℝ)*(a+b)

theorem a03NativeGCDSpatialBudget_le {Y : ℝ} (hY : 1≤Y) :
    a03NativeGCDSpatialBudget Y≤Y^(9/2:ℝ) := by
  have hp := Real.rpow_le_rpow_of_exponent_le hY (by norm_num : (7/2:ℝ)≤9/2)
  unfold a03NativeGCDSpatialBudget
  calc
    _≤((40/91:ℝ)+(40/99:ℝ))*Y^(9/2:ℝ) := by nlinarith
    _≤_ := mul_le_of_le_one_left (Real.rpow_nonneg (zero_le_one.trans hY) _) (by norm_num)

theorem a03NativeGCDFullBudgetRow_bound
    {T a b e C F G : ℝ} (hT : 1≤T) (_ha : 0≤a) (_hb : 0≤b) (hC : 0≤C)
    (hF : 0≤F) (hG : 0≤G) (k : ℕ) (f g : ℝ→ℝ)
    (hf : ∀ x,‖f x‖≤F) (hg : ∀ x,‖g x‖≤G)
    {u v : ℕ} (hu : u∈Finset.range ⌊T^a⌋₊) (hv : v∈Finset.range ⌊T^b⌋₊) :
    a03NativeGCDFullBudgetRow T e k C f g u v≤
      (F*G*C*T^e*(Real.log T)^k/T^2)*T^((1+(a+b)/2)*(9/2:ℝ)) := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hL : 0≤Real.log T := Real.log_nonneg hT
  have hAu : (u+1:ℝ)≤T^a := by
    have hn : u+1≤⌊T^a⌋₊ := Nat.succ_le_of_lt (Finset.mem_range.mp hu)
    exact (by exact_mod_cast hn : (u+1:ℝ)≤(⌊T^a⌋₊:ℝ)).trans
      (Nat.floor_le (Real.rpow_nonneg hTp.le a))
  have hBv : (v+1:ℝ)≤T^b := by
    have hn : v+1≤⌊T^b⌋₊ := Nat.succ_le_of_lt (Finset.mem_range.mp hv)
    exact (by exact_mod_cast hn : (v+1:ℝ)≤(⌊T^b⌋₊:ℝ)).trans
      (Nat.floor_le (Real.rpow_nonneg hTp.le b))
  have hu0 : (0:ℝ)≤u := Nat.cast_nonneg u
  have hv0 : (0:ℝ)≤v := Nat.cast_nonneg v
  have hAB : 1≤(u+1:ℝ)*(v+1:ℝ) := by nlinarith
  have hY : 1≤T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ)) :=
    by simpa only [one_mul] using mul_le_mul hT (Real.one_le_sqrt.mpr hAB) (by norm_num : (0:ℝ)≤1) hTp.le
  have hSqrt : Real.sqrt ((u+1:ℝ)*(v+1:ℝ))≤T^((a+b)/2) := by
    calc
      _≤Real.sqrt (T^a*T^b) := Real.sqrt_le_sqrt (mul_le_mul hAu hBv (by positivity) (by positivity))
      _=_ := by
        rw [←Real.rpow_add hTp,Real.sqrt_eq_rpow,←Real.rpow_mul hTp.le]
        congr 1
        ring
  have hYup : T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ))≤T^(1+(a+b)/2) := by
    rw [Real.rpow_add hTp,Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hSqrt hTp.le
  have hJ : a03NativeGCDSpatialBudget (T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ)))≤
      T^((1+(a+b)/2)*(9/2:ℝ)) := by
    apply (a03NativeGCDSpatialBudget_le hY).trans
    rw [Real.rpow_mul hTp.le]
    exact Real.rpow_le_rpow (by positivity) hYup (by norm_num)
  have hD : T^2≤(u+1:ℝ)*(v+1:ℝ)*T^2 :=
    le_mul_of_one_le_left (sq_nonneg T) hAB
  have hN : |f (Real.log (u+1:ℝ)/Real.log T)| * |g (Real.log (v+1:ℝ)/Real.log T)| *
      C*T^e*(Real.log T)^k≤F*G*C*T^e*(Real.log T)^k := by
    gcongr
    · simpa only [Real.norm_eq_abs] using hf (Real.log (u+1:ℝ)/Real.log T)
    · simpa only [Real.norm_eq_abs] using hg (Real.log (v+1:ℝ)/Real.log T)
  unfold a03NativeGCDFullBudgetRow
  apply mul_le_mul (div_le_div₀ (by positivity) hN (sq_pos_of_pos hTp) hD) hJ
    (by unfold a03NativeGCDSpatialBudget; positivity) (by positivity)

theorem a03NativeGCDFullBudget_bounded_profiles
    {T a b e C F G : ℝ} (hT : 1≤T) (ha : 0≤a) (hb : 0≤b) (hC : 0≤C)
    (hF : 0≤F) (hG : 0≤G) (k : ℕ) (f g : ℝ→ℝ)
    (hf : ∀ x,‖f x‖≤F) (hg : ∀ x,‖g x‖≤G) :
    a03NativeGCDFullBudget T a b e k C f g≤
      (2*F*G*C)*(Real.log T)^k*T^(e+7/2+(13/4:ℝ)*(a+b)) := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hL := Real.log_nonneg hT
  let q : ℝ := (1+(a+b)/2)*(9/2:ℝ)
  let P : ℝ := (F*G*C*T^e*(Real.log T)^k/T^2)*T^q
  have hP : 0≤P := by dsimp [P]; positivity
  have hN₁ : (⌊T^a⌋₊:ℝ)≤T^a := Nat.floor_le (Real.rpow_nonneg hTp.le a)
  have hN₂ : (⌊T^b⌋₊:ℝ)≤T^b := Nat.floor_le (Real.rpow_nonneg hTp.le b)
  have hsum : (∑ _positive : Bool,∑ u∈Finset.range ⌊T^a⌋₊,∑ v∈Finset.range ⌊T^b⌋₊,
      a03NativeGCDFullBudgetRow T e k C f g u v)≤2*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*P := by
    calc
      _≤∑ _positive : Bool,∑ _u∈Finset.range ⌊T^a⌋₊,∑ _v∈Finset.range ⌊T^b⌋₊,P := by
        apply Finset.sum_le_sum
        intro positive _hp
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        exact a03NativeGCDFullBudgetRow_bound hT ha hb hC hF hG k f g hf hg hu hv
      _=_ := by simp [Finset.sum_const,Finset.card_range]; ring
  unfold a03NativeGCDFullBudget
  calc
    _≤T*(2*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*P) := mul_le_mul_of_nonneg_left hsum hTp.le
    _≤T*(2*T^a*T^b*P) := by gcongr
    _=_ := by
      have hp : T*T^a*T^b*T^e/T^2*T^q=T^(e+7/2+(13/4:ℝ)*(a+b)) := by
        calc
          _=T^(1:ℝ)*T^a*T^b*T^e*T^(-2:ℝ)*T^q := by
            rw [Real.rpow_one,Real.rpow_neg hTp.le,Real.rpow_two]
            ring
          _=_ := by
            rw [←Real.rpow_add hTp,←Real.rpow_add hTp,←Real.rpow_add hTp,
              ←Real.rpow_add hTp,←Real.rpow_add hTp]
            congr 1
            dsimp [q]
            ring
      dsimp only [P]
      calc
        _=(2*F*G*C)*(Real.log T)^k*(T*T^a*T^b*T^e/T^2*T^q) := by ring
        _=_ := by rw [hp]

theorem a03NativeGCDFullBudget_smooth_uniform_power {a b : ℝ}
    (ha : 0≤a) (hb : 0≤b) (k : ℕ) (f g : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ D : ℝ,0≤D ∧ ∀ T : ℝ,1≤T → ∀ C : ℝ,0≤C → ∀ e : ℝ,
      a03NativeGCDFullBudget T a b e k C f g≤D*C*T^(e+a03NativeGCDFullBudgetPower a b) := by
  obtain ⟨F,hF,hfB⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgB⟩ := rectangular_supported_profile_bounded g hg
  let L : ℝ := (k.factorial:ℝ)*Real.exp 1
  refine ⟨2*F*G*L,by dsimp [L]; positivity,?_⟩
  intro T hT C hC e
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hlog : (Real.log T)^k≤L*T := by
    apply (pow_le_pow_left₀ (Real.log_nonneg hT) (by linarith : Real.log T≤1+Real.log T) k).trans
    simpa only [one_pow,div_one,Real.rpow_one] using logarithmic_power_le_rpow (by norm_num : (0:ℝ)<1) hT k
  calc
    _≤(2*F*G*C)*(Real.log T)^k*T^(e+7/2+(13/4:ℝ)*(a+b)) :=
      a03NativeGCDFullBudget_bounded_profiles hT ha hb hC hF hG k f g hfB hgB
    _≤(2*F*G*C)*(L*T)*T^(e+7/2+(13/4:ℝ)*(a+b)) := by gcongr
    _=(2*F*G*L)*C*T^(e+a03NativeGCDFullBudgetPower a b) := by
      have hpow : T^(e+a03NativeGCDFullBudgetPower a b)=T*T^(e+7/2+(13/4:ℝ)*(a+b)) := by
        unfold a03NativeGCDFullBudgetPower
        rw [show e+(9/2+(13/4:ℝ)*(a+b))=1+(e+7/2+(13/4:ℝ)*(a+b)) by ring,
          Real.rpow_add hTp,Real.rpow_one]
      rw [hpow]
      ring

theorem a03NativeGCDFullBudget_complex_rows
    {T a b e C : ℝ} (hT : 0≤T) (k : ℕ) (f g : ℝ→ℝ)
    (row : Bool→ℕ→ℕ→ℂ)
    (hrow : ∀ positive : Bool,∀ u∈Finset.range ⌊T^a⌋₊,∀ v∈Finset.range ⌊T^b⌋₊,
      ‖row positive u v‖≤a03NativeGCDFullBudgetRow T e k C f g u v) :
    ‖(T:ℂ)*∑ positive : Bool,∑ u∈Finset.range ⌊T^a⌋₊,∑ v∈Finset.range ⌊T^b⌋₊,
      row positive u v‖≤a03NativeGCDFullBudget T a b e k C f g := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hT]
  unfold a03NativeGCDFullBudget
  apply mul_le_mul_of_nonneg_left _ hT
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro positive _hp
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro u hu
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v hv
  exact hrow positive u hu v hv

theorem a03NativeGCDFullBudget_complex_norm_le
    {T a b e C : ℝ} {k : ℕ} {f g : ℝ→ℝ} (hT : 1≤T)
    (row : Bool→ℕ→ℕ→ℂ)
    (hrow : ∀ positive : Bool,∀ u∈Finset.range ⌊T^a⌋₊,∀ v∈Finset.range ⌊T^b⌋₊,
      ‖row positive u v‖≤a03NativeGCDFullBudgetRow T e k C f g u v) :
    ‖(T:ℂ)*∑ positive : Bool,∑ u∈Finset.range ⌊T^a⌋₊,∑ v∈Finset.range ⌊T^b⌋₊,
      row positive u v‖≤a03NativeGCDFullBudget T a b e k C f g :=
  a03NativeGCDFullBudget_complex_rows (zero_le_one.trans hT) k f g row hrow

theorem a03NativeGCDFullBudget_smooth_uniform_rapid {a b : ℝ}
    (ha : 0≤a) (hb : 0≤b) (k N : ℕ) (f g : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ M : ℕ,∃ D : ℝ,0≤D ∧ ∀ T : ℝ,1≤T → ∀ C : ℝ,0≤C →
      a03NativeGCDFullBudget T a b (-(M:ℝ)) k C f g≤D*C*T^(-(N:ℝ)) := by
  obtain ⟨D,hD,hbound⟩ := a03NativeGCDFullBudget_smooth_uniform_power ha hb k f g hf hg
  obtain ⟨M,hM⟩ := exists_nat_gt (a03NativeGCDFullBudgetPower a b+(N:ℝ))
  refine ⟨M,D,hD,?_⟩
  intro T hT C hC
  apply (hbound T hT C hC (-(M:ℝ))).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD hC)
  exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)

def a03NativeGCDFullAbsoluteMajorantMass (T a b : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℝ :=
  T*∑ _positive : Bool,∑ u∈Finset.range ⌊T^a⌋₊,∑ v∈Finset.range ⌊T^b⌋₊,
    |f (Real.log (u+1:ℝ)/Real.log T)| * |g (Real.log (v+1:ℝ)/Real.log T)| *
      ∫ X : ℝ in Ioi 0,∑'p : (ℕ×ℕ)×ℕ,a03NativeGCDAbsoluteMajorant T σ (u+1) (v+1)
        (T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ))) X p

theorem a03NativeGCDFullAbsoluteMajorantMass_uniform_power {a b κ : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hκ : 0<κ) (f g : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,1<T → 1≤Real.log T → ∀ σ : MomentShifts,
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      a03NativeGCDFullAbsoluteMajorantMass T a b σ f g≤C*T^(a03NativeGCDFullBudgetPower a b) := by
  obtain ⟨D,hD,hMass⟩ := a03NativeGCDAbsoluteMajorant_integral_uniform_bound hκ
  obtain ⟨E,hE,hBudget⟩ := a03NativeGCDFullBudget_smooth_uniform_power ha hb 8 f g hf hg
  refine ⟨E*D,mul_nonneg hE hD,?_⟩
  intro T hT hlog σ hroot
  have hTp : 0<T := zero_lt_one.trans hT
  calc
    _≤a03NativeGCDFullBudget T a b 0 8 D f g := by
      unfold a03NativeGCDFullAbsoluteMajorantMass a03NativeGCDFullBudget
      apply mul_le_mul_of_nonneg_left _ hTp.le
      apply Finset.sum_le_sum
      intro positive _hp
      apply Finset.sum_le_sum
      intro u _hu
      apply Finset.sum_le_sum
      intro v _hv
      have hY : 0<T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ)) := by positivity
      have hrow := hMass T hT hlog σ hroot (u+1) (v+1) (by positivity) (by positivity)
        (T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ))) hY
      push_cast at hrow
      have hm := mul_le_mul_of_nonneg_left hrow
        (by positivity : 0≤|f (Real.log (u+1:ℝ)/Real.log T)| * |g (Real.log (v+1:ℝ)/Real.log T)|)
      convert hm using 1
      unfold a03NativeGCDFullBudgetRow a03NativeGCDSpatialBudget
      rw [Real.rpow_zero]
      ring
    _≤(E*D)*T^(a03NativeGCDFullBudgetPower a b) := by
      simpa only [zero_add] using hBudget T hT.le D hD 0

end
end Sechstmoment
