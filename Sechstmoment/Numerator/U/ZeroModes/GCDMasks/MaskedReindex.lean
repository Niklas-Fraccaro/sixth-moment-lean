import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.AbsoluteConvergence
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.PassiveMaskPartition
import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.FiniteGCDVStarJoin

/-! Exact regrouping of the selected finite seven-dyadic retained GCD
expression into the actual positive native indices. The finite tuple
bijection, amplifier profile cutoff and bounded-mask Bochner exchange
are proved separately and consumed in the literal integrated endpoint. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03NativeGCDNatTuple (u v m n h : ℕ) : Fin 5→ℕ := ![u+1,v+1,m+1,n+1,h+1]

def a03NativeGCDNatGrid (q : QuadraticScales) : Finset (Fin 5→ℕ) :=
  Fintype.piFinset fun j => Finset.range ⌊2*(![q.A,q.B,q.M₁,q.N₁,q.H] : Fin 5→ℝ) j⌋₊

@[simp] theorem a03NativeGCDNatGrid_succ_mem (q : QuadraticScales) (z : Fin 5→ℕ) :
    z∈a03NativeGCDNatGrid q ↔ (fun j => z j+1)∈quadraticMainIndexSet q := by
  simp only [a03NativeGCDNatGrid,quadraticMainIndexSet,Fintype.mem_piFinset,
    Finset.mem_range,Finset.mem_Icc]
  constructor
  · intro hz j
    exact ⟨by omega,by have := hz j; omega⟩
  · intro hz j
    have := hz j
    omega

/-- The exact five native positive indices are the successors of a
finite natural-index grid; the inverse map is coordinatewise predecessor. -/
theorem a03_native_GCD_main_sum_eq_nat_grid (q : QuadraticScales) (F : (Fin 5→ℕ)→ℂ) :
    (∑w∈quadraticMainIndexSet q,F w)=
      ∑z∈a03NativeGCDNatGrid q,F (fun j => z j+1) := by
  apply Finset.sum_bij (fun w _ => fun j => w j-1)
  · intro w hw
    apply (a03NativeGCDNatGrid_succ_mem q _).mpr
    have he : (fun j => w j-1+1)=w := by
      funext j
      have hp := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
      omega
    rw [he]
    exact hw
  · intro w hw z hz he
    funext j
    have hp := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
    have hq := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hz j)).1
    have hj := congrFun he j
    omega
  · intro z hz
    refine ⟨(fun j => z j+1),(a03NativeGCDNatGrid_succ_mem q z).mp hz,?_⟩
    funext j
    dsimp only
    omega
  · intro w hw
    congr 1
    funext j
    have hp := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
    dsimp only
    omega

def a03NativeGCDFiveIndexEquiv : (ℕ×(ℕ×(ℕ×(ℕ×ℕ)))) ≃ (Fin 5→ℕ) where
  toFun p := ![p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2]
  invFun z := (z 0,(z 1,(z 2,(z 3,z 4))))
  left_inv p := by rcases p with ⟨u,v,m,n,h⟩; rfl
  right_inv z := by ext j; fin_cases j <;> rfl

/-- A genuinely finitely supported positive native sum is exactly the
nested five natural series, with no conditional reindexing premise. -/
theorem a03_native_GCD_main_sum_eq_nested_tsum (q : QuadraticScales)
    (F : (Fin 5→ℕ)→ℂ) (hF : ∀w,w∉quadraticMainIndexSet q→F w=0) :
    (∑w∈quadraticMainIndexSet q,F w)=
      ∑'u : ℕ,∑'v : ℕ,∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,F (a03NativeGCDNatTuple u v m n h) := by
  let G : (Fin 5→ℕ)→ℂ := fun z => F (fun j => z j+1)
  have hz (z : Fin 5→ℕ) (hz : z∉a03NativeGCDNatGrid q) : G z=0 :=
    hF _ (fun h => hz ((a03NativeGCDNatGrid_succ_mem q z).mpr h))
  have hs : Summable G := summable_of_ne_finset_zero hz
  have ht : (∑' z,G z)=∑z∈a03NativeGCDNatGrid q,G z := tsum_eq_sum hz
  have hp : Summable (fun p => G (a03NativeGCDFiveIndexEquiv p)) :=
    hs.comp_injective a03NativeGCDFiveIndexEquiv.injective
  rw [a03_native_GCD_main_sum_eq_nat_grid,←ht,
    ←a03NativeGCDFiveIndexEquiv.tsum_eq G,hp.tsum_prod]
  apply tsum_congr
  intro u
  rw [(hp.prod_factor u).tsum_prod]
  apply tsum_congr
  intro v
  rw [((hp.prod_factor u).prod_factor v).tsum_prod]
  apply tsum_congr
  intro m
  rw [(((hp.prod_factor u).prod_factor v).prod_factor m).tsum_prod]
  apply tsum_congr
  intro n
  apply tsum_congr
  intro h
  dsimp [G]
  congr 1
  ext j
  fin_cases j <;> rfl


theorem a03_native_GCD_finite_positive_sum_eq_nested_tsum
    (S : Finset (Fin 5→ℕ)) (hS : ∀w∈S,∀ j,1≤w j)
    (F : (Fin 5→ℕ)→ℂ) (hF : ∀w,w∉S→F w=0) :
    (∑w∈S,F w)=∑'u : ℕ,∑'v : ℕ,∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,
      F (a03NativeGCDNatTuple u v m n h) := by
  let R := S.image (fun w => fun j => w j-1)
  let G : (Fin 5→ℕ)→ℂ := fun z => F (fun j => z j+1)
  have hz (z : Fin 5→ℕ) (hz : z∉R) : G z=0 := by
    apply hF
    intro hw
    apply hz
    apply Finset.mem_image.mpr
    refine ⟨(fun j => z j+1),hw,?_⟩
    funext j
    dsimp only
    omega
  have hf : (∑w∈S,F w)=∑z∈R,G z := by
    apply Finset.sum_bij (fun w _ => fun j => w j-1)
    · intro w hw
      exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
    · intro w hw z hz he
      funext j
      have hp := hS w hw j
      have hq := hS z hz j
      have hj := congrFun he j
      omega
    · intro z hz
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hz
      exact ⟨w,hw,he⟩
    · intro w hw
      dsimp [G]
      congr 1
      funext j
      have hp := hS w hw j
      omega
  have hs : Summable G := summable_of_ne_finset_zero hz
  have ht : (∑'z,G z)=∑z∈R,G z := tsum_eq_sum hz
  have hp : Summable (fun p => G (a03NativeGCDFiveIndexEquiv p)) :=
    hs.comp_injective a03NativeGCDFiveIndexEquiv.injective
  rw [hf,←ht,←a03NativeGCDFiveIndexEquiv.tsum_eq G,hp.tsum_prod]
  apply tsum_congr
  intro u
  rw [(hp.prod_factor u).tsum_prod]
  apply tsum_congr
  intro v
  rw [((hp.prod_factor u).prod_factor v).tsum_prod]
  apply tsum_congr
  intro m
  rw [(((hp.prod_factor u).prod_factor v).prod_factor m).tsum_prod]
  apply tsum_congr
  intro n
  apply tsum_congr
  intro h
  dsimp [G]
  congr 1
  ext j
  fin_cases j <;> rfl


def a03NativeGCDActualScales (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : QuadraticScales :=
  phaseActualScales (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
    (rectangularAFESmoothScale (i.1 2)) i.2


theorem a03NativeGCDActualScales_pos (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :
    ∀ j,0<(a03NativeGCDActualScales i).size j :=
  boundaryActual_scales_pos _ _ _ i.2
    (boundaryActual_scale_pos _) (boundaryActual_scale_pos _) (boundaryActual_scale_pos _)

def a03NativeGCDDensity (dual positive : Bool) (Φ : ℝ→ℂ) (T : ℝ)
    (σ α : MomentShifts) (f g : ℝ→ℝ) (w : Fin 5→ℕ) (X : ℝ) : ℂ :=
  (f (Real.log (w 0:ℝ)/Real.log T):ℂ)*(g (Real.log (w 1:ℝ)/Real.log T):ℂ)*
    (Nat.gcd (w 0*w 2) (w 1*w 3):ℂ)*
      (w 0:ℂ)^(-1+α 1)*(w 1:ℂ)^(-1+α 3)*(w 2:ℂ)^(-1-α 0+α 1)*
        (w 3:ℂ)^(-1-α 2+α 3)*(X:ℂ)^(-1-α 1-α 3)*
          (a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((w 0:ℝ)*(w 2:ℝ)^2/X)*
            a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((w 1:ℝ)*(w 3:ℝ)^2/X))*
              ∫t : ℝ,Complex.exp (((-(T*rectangularGapSign positive*
                (Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)*w 4/X):ℝ):ℂ)*I*(t:ℂ))*
                  a03RatioLeadingBranchProfile dual Φ T σ t*
                    bblrVStar (polarPoleKiller T σ) (X^2/((w 0:ℝ)*w 1*(T*t)^2))

@[simp] theorem a03NativeGCDDensity_nat_tuple (dual positive : Bool) (Φ : ℝ→ℂ) (T : ℝ)
    (σ α : MomentShifts) (f g : ℝ→ℝ) (u v m n h : ℕ) (X : ℝ) :
    a03NativeGCDDensity dual positive Φ T σ α f g (a03NativeGCDNatTuple u v m n h) X=
      a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v m n h X := rfl

@[simp] theorem a03NativeGCDNatTuple_positive (u v m n h : ℕ) :
    ∀ j,1≤a03NativeGCDNatTuple u v m n h j := by
  intro j
  fin_cases j <;> dsimp [a03NativeGCDNatTuple] <;> omega

theorem a03NativeGCDDensity_integrable (dual positive : Bool) (Φ : ℝ→ℂ) (T : ℝ)
    (σ α : MomentShifts) (f g : ℝ→ℝ)
    (hFI : ∀u v m n h,IntegrableOn
      (a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v m n h) (Ioi 0))
    (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) :
    IntegrableOn (a03NativeGCDDensity dual positive Φ T σ α f g w) (Ioi 0) := by
  have he : a03NativeGCDNatTuple (w 0-1) (w 1-1) (w 2-1) (w 3-1) (w 4-1)=w := by
    have he' (j : Fin 5) : w j-1+1=w j := by have := hw j; omega
    ext j
    fin_cases j <;> exact he' _
  have heF : a03NativeGCDDensity dual positive Φ T σ α f g w=
      a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g
        (w 0-1) (w 1-1) (w 2-1) (w 3-1) (w 4-1) := by
    funext X
    rw [←he]
    exact a03NativeGCDDensity_nat_tuple _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [heF]
  exact hFI (w 0-1) (w 1-1) (w 2-1) (w 3-1) (w 4-1)

theorem a03NativeGCDAllDyadicWeight_actual_integrable
    (dual positive : Bool) (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (hFI : ∀u v m n h,IntegrableOn
      (a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v m n h) (Ioi 0))
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) :
    IntegrableOn (fun X => (a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X:ℂ)*
      a03NativeGCDDensity dual positive Φ T σ α f g w X) (Ioi 0) := by
  have hcont : Continuous (fun X => a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X) := by
    simp_rw [a03NativeGCDActualScales,a03_native_GCD_all_weight_eq_seven_weight i w hw]
    exact a03NativeGCDSevenWeight_continuous w (a03GCDScaleTuple i)
  apply (a03NativeGCDDensity_integrable dual positive Φ T σ α f g hFI w hw).bdd_mul (c:=(1:ℝ))
    ((Complex.continuous_ofReal.comp hcont).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro X
  have hb := a03_native_GCD_selected_grid_weight_bounds {i} (fun _ => True) w hw X
  simp only [Finset.sum_singleton,ite_true] at hb
  change 0≤a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X ∧
    a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X≤1 at hb
  change ‖(a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X:ℂ)‖≤1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb.1]
  exact hb.2

def a03NativeGCDSelectedIndexSet (T a b s u : ℝ) : Finset (Fin 5→ℕ) :=
  (a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))).biUnion
    (fun i => quadraticMainIndexSet (a03NativeGCDActualScales i))

theorem a03NativeGCDSelectedIndexSet_positive (T a b s u : ℝ)
    (w : Fin 5→ℕ) (hw : w∈a03NativeGCDSelectedIndexSet T a b s u) : ∀ j,1≤w j := by
  obtain ⟨i,_,hwi⟩ := Finset.mem_biUnion.mp hw
  intro j
  exact (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hwi j)).1

theorem a03NativeGCDSelectedDyadicMask_zero_outside
    (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (T a b s u ε : ℝ) (f g : ℝ→ℝ)
    (w : Fin 5→ℕ) (hw : w∉a03NativeGCDSelectedIndexSet T a b s u) (X : ℝ) :
    a03NativeGCDSelectedDyadicMask select T a b s u ε f g w X=0 := by
  unfold a03NativeGCDSelectedDyadicMask
  apply Finset.sum_eq_zero
  intro i hi
  have hwi : w∉quadraticMainIndexSet (a03NativeGCDActualScales i) := by
    intro h
    exact hw (Finset.mem_biUnion.mpr ⟨i,hi,h⟩)
  have hq := a03NativeGCDActualScales_pos i
  have hz := a03NativeGCDAllDyadicWeight_zero_outside_main _ hq w hwi X
  simp only [a03NativeGCDActualScales] at hz
  rw [hz]
  exact ite_self 0

theorem a03_retained_ratio_GCD_expanded_eq_native (dual positive : Bool) (Φ : ℝ→ℂ)
    (T : ℝ) (σ α : MomentShifts) (q : QuadraticScales) (f g : ℝ→ℝ) :
    a03RetainedRatioGCDVStarExpandedZeroMode dual Φ T σ α (rectangularGapSign positive) q f g=
      ∑w∈quadraticMainIndexSet q,∫X : ℝ in Ioi 0,
        (a03NativeGCDAllDyadicWeight q w X:ℂ)*a03NativeGCDDensity dual positive Φ T σ α f g w X := by
  unfold a03RetainedRatioGCDVStarExpandedZeroMode
  apply Finset.sum_congr rfl
  intro w _
  apply integral_congr_ae
  filter_upwards [] with X
  unfold a03NativeGCDDensity
  ring

/-- The literal selected native expression retains the actual independent
amplifier cutoffs and the original nested positive m,n,h series. -/
def a03ActualMaskedRatioGCDVStar
    (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (dual : Bool) (Φ : ℝ→ℂ)
    (T a b s u ε : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  (T:ℂ)*∑positive : Bool,∑z∈Finset.range ⌊T^a⌋₊,∑v∈Finset.range ⌊T^b⌋₊,
    ∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,∫X : ℝ in Ioi 0,
      (a03NativeGCDSelectedDyadicMask select T a b s u ε f g (a03NativeGCDNatTuple z v m n h) X:ℂ)*
        a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v m n h X

theorem a03NativeGCD_actual_profile_zero_outside {T a : ℝ} (hT : 1<T)
    (f : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (z : ℕ)
    (hz : z∉Finset.range ⌊T^a⌋₊) : f (Real.log (z+1:ℝ)/Real.log T)=0 := by
  have hfloor : ⌊T^a⌋₊<z+1 := by
    have := Nat.le_of_not_gt (fun h => hz (Finset.mem_range.mpr h))
    omega
  have hpow : T^a<(z+1:ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (Nat.lt_of_floor_lt hfloor)
  exact rectangular_supported_profile_zero_above f hf _
    ((lt_div_iff₀ (Real.log_pos hT)).mpr (Real.lt_log_of_rpow_lt (zero_lt_one.trans hT) hpow))

/-- Exact finite-grid regrouping. The analytic premise is literal
integrability, proved automatically in the eventual theorem below. -/
theorem a03_actual_passive_retained_GCD_eq_masked_of_integrable
    (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (dual : Bool) (Φ : ℝ→ℂ)
    {T : ℝ} (hT : 1<T) (a b s u ε : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hFI : ∀positive : Bool,∀ z v m n h,IntegrableOn
      (a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v m n h) (Ioi 0)) :
    a03ActualPassiveRetainedRatioGCDVStarFinite select dual Φ T a b s u ε σ α f g=
      a03ActualMaskedRatioGCDVStar select dual Φ T a b s u ε σ α f g := by
  let S := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  let J := a03NativeGCDSelectedIndexSet T a b s u
  let P := fun i => select i ∧ a03ActualPassiveRatioSourceGoodBlock T s ε f g i
  let W := fun i w X => if P i then a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X else 0
  let D := fun positive w X => a03NativeGCDDensity dual positive Φ T σ α f g w X
  have hJ (w : Fin 5→ℕ) (hw : w∈J) : ∀ j,1≤w j :=
    a03NativeGCDSelectedIndexSet_positive T a b s u w hw
  have hI (positive : Bool) (i : (Fin 3→ℕ)×(Fin 4→ℕ)) (w : Fin 5→ℕ) (hw : w∈J) :
      IntegrableOn (fun X => (W i w X:ℂ)*D positive w X) (Ioi 0) := by
    by_cases hP : P i
    · simp only [W,hP,ite_true]
      exact a03NativeGCDAllDyadicWeight_actual_integrable dual positive Φ T σ α f g (hFI positive) i w (hJ w hw)
    · simp only [W,hP,ite_false,Complex.ofReal_zero,zero_mul]
      exact integrable_zero _ _ _
  have hblock (positive : Bool) (i : (Fin 3→ℕ)×(Fin 4→ℕ)) (hi : i∈S) :
      a03ActualPassiveRetainedRatioGCDVStarBlock select dual positive Φ T s ε σ α f g i=
        (T:ℂ)*∑w∈J,∫X : ℝ in Ioi 0,(W i w X:ℂ)*D positive w X := by
    unfold a03ActualPassiveRetainedRatioGCDVStarBlock
    dsimp only
    by_cases hP : P i
    · simp only [show select i ∧ a03ActualPassiveRatioSourceGoodBlock T s ε f g i from hP,and_self,ite_true,
        W,hP]
      change (T:ℂ)*a03RetainedRatioGCDVStarZeroMode dual Φ T σ α (rectangularGapSign positive)
        (a03NativeGCDActualScales i)
        (phaseActualAmplifierCoefficient T f (a03NativeGCDActualScales i).A)
        (phaseActualAmplifierCoefficient T g (a03NativeGCDActualScales i).B)=_
      rw [a03_actual_retained_ratio_GCD_VStar_eq_expanded dual Φ T σ α (rectangularGapSign positive)
        (a03NativeGCDActualScales i) f g,a03_retained_ratio_GCD_expanded_eq_native]
      congr 1
      apply Finset.sum_subset
      · intro w hw
        exact Finset.mem_biUnion.mpr ⟨i,hi,hw⟩
      · intro w _ hw
        have hq := a03NativeGCDActualScales_pos i
        have hz := a03NativeGCDAllDyadicWeight_zero_outside_main _ hq w hw
        simp only [hz,Complex.ofReal_zero,zero_mul,integral_zero]
    · have hPn : ¬(select i ∧ a03ActualPassiveRatioSourceGoodBlock T s ε f g i) := hP
      simp only [hPn,ite_false,W,hP,ite_false,Complex.ofReal_zero,zero_mul,integral_zero,
        Finset.sum_const_zero,mul_zero]
  calc
    _=(T:ℂ)*∑positive : Bool,∑i∈S,∑w∈J,∫X : ℝ in Ioi 0,(W i w X:ℂ)*D positive w X := by
      unfold a03ActualPassiveRetainedRatioGCDVStarFinite
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro positive _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i hi => hblock positive i hi)
    _=(T:ℂ)*∑positive : Bool,∑w∈J,∫X : ℝ in Ioi 0,
        (a03NativeGCDSelectedDyadicMask select T a b s u ε f g w X:ℂ)*D positive w X := by
      congr 1
      apply Finset.sum_congr rfl
      intro positive _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      rw [←integral_finsetSum S (fun i _ => hI positive i w hw)]
      apply integral_congr_ae
      filter_upwards [] with X
      simp only [a03NativeGCDSelectedDyadicMask,Complex.ofReal_sum,Finset.sum_mul,
        S,W,P,a03NativeGCDActualScales]
    _=(T:ℂ)*∑positive : Bool,∑'z : ℕ,∑'v : ℕ,∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,
        ∫X : ℝ in Ioi 0,
          (a03NativeGCDSelectedDyadicMask select T a b s u ε f g (a03NativeGCDNatTuple z v m n h) X:ℂ)*
            a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v m n h X := by
      congr 1
      apply Finset.sum_congr rfl
      intro positive _
      rw [a03_native_GCD_finite_positive_sum_eq_nested_tsum J hJ]
      · apply tsum_congr
        intro z
        apply tsum_congr
        intro v
        apply tsum_congr
        intro m
        apply tsum_congr
        intro n
        apply tsum_congr
        intro h
        simp only [D,a03NativeGCDDensity_nat_tuple]
      · intro w hw
        simp only [a03NativeGCDSelectedDyadicMask_zero_outside select T a b s u ε f g w hw,
          Complex.ofReal_zero,zero_mul,integral_zero]
    _=_ := by
      unfold a03ActualMaskedRatioGCDVStar
      congr 1
      apply Finset.sum_congr rfl
      intro positive _
      rw [tsum_eq_sum (s:=Finset.range ⌊T^a⌋₊)]
      · apply Finset.sum_congr rfl
        intro z _
        apply tsum_eq_sum
        intro v hv
        have hz := a03NativeGCD_actual_profile_zero_outside hT g hg v hv
        simp [a03UnrestrictedRatioGCDVStarIntegrand,hz]
      · intro z hz
        have hz := a03NativeGCD_actual_profile_zero_outside hT f hf z hz
        simp [a03UnrestrictedRatioGCDVStarIntegrand,hz]

/-- No reconstruction hypothesis is assumed: the actual branch envelope
proves absolute integrability, and the finite tuple bijection supplies
exact equality with the countable native masked expression. -/
theorem a03_actual_passive_retained_GCD_eq_masked {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (a b s u ε : ℝ) (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,(∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤1/4) →∀ dual : Bool,
      ∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
      a03ActualPassiveRetainedRatioGCDVStarFinite select dual Φ T a b s u ε σ α f g=
        a03ActualMaskedRatioGCDVStar select dual Φ T a b s u ε σ α f g := by
  filter_upwards [a03UnrestrictedRatioGCDVStar_absolute_convergence hΦ hSupp K hK hκ f g,
    eventually_gt_atTop (1:ℝ)] with T hconv hT
  intro σ hσ hroot α hα dual select
  apply a03_actual_passive_retained_GCD_eq_masked_of_integrable select dual Φ hT a b s u ε σ α f g hf hg
  intro positive z v m n h
  exact (hconv σ hσ hroot α hα dual positive z v).1 ((m,n),h)


theorem a03NativeGCD_triple_tsum {F : ((ℕ×ℕ)×ℕ)→ℂ} (hF : Summable F) :
    (∑'p : (ℕ×ℕ)×ℕ,F p)=∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,F ((m,n),h) := by
  rw [hF.tsum_prod,hF.prod.tsum_prod]

/-- The common-X integral and the actual nested masked native series
exchange automatically by the proved unmasked absolute majorant. -/
theorem a03_actual_native_masked_tsum_integral {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (a b s u ε : ℝ) (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,(∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤1/4) →∀ dual positive : Bool,
      ∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,∀ z v : ℕ,
      (∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,∫X : ℝ in Ioi 0,
        (a03NativeGCDSelectedDyadicMask select T a b s u ε f g (a03NativeGCDNatTuple z v m n h) X:ℂ)*
          a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v m n h X)=
      ∫X : ℝ in Ioi 0,∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,
        (a03NativeGCDSelectedDyadicMask select T a b s u ε f g (a03NativeGCDNatTuple z v m n h) X:ℂ)*
          a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v m n h X := by
  filter_upwards [a03UnrestrictedRatioGCDVStar_absolute_convergence hΦ hSupp K hK hκ f g]
    with T hconv
  intro σ hσ hroot α hα dual positive select z v
  let F := fun p : (ℕ×ℕ)×ℕ =>
    a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v p.1.1 p.1.2 p.2
  let mask := fun (p : (ℕ×ℕ)×ℕ) X => a03NativeGCDSelectedDyadicMask select T a b s u ε f g
    (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2) X
  have hc := hconv σ hσ hroot α hα dual positive z v
  have hm (p : (ℕ×ℕ)×ℕ) : AEStronglyMeasurable (mask p) (volume.restrict (Ioi 0)) :=
    (a03NativeGCDSelectedDyadicMask_continuous select T a b s u ε f g _
      (a03NativeGCDNatTuple_positive z v p.1.1 p.1.2 p.2)).aestronglyMeasurable
  have hb (p : (ℕ×ℕ)×ℕ) (X : ℝ) (_hX : 0<X) : |mask p X|≤1 := by
    have h := a03NativeGCDSelectedDyadicMask_bounds select T a b s u ε f g
      (a03NativeGCDNatTuple z v p.1.1 p.1.2 p.2)
      (a03NativeGCDNatTuple_positive z v p.1.1 p.1.2 p.2) X
    dsimp only [mask]
    rw [abs_of_nonneg h.1]
    exact h.2
  have hmasked := a03NativeGCD_bounded_mask_absolute_convergence hc.1 hc.2.1 mask hm hb
  have hs : Summable (fun p : (ℕ×ℕ)×ℕ => ∫X : ℝ in Ioi 0,(mask p X:ℂ)*F p X) :=
    hmasked.2.2.1
  have hpoint (X : ℝ) (hX : 0<X) : Summable (fun p : (ℕ×ℕ)×ℕ => (mask p X:ℂ)*F p X) := by
    apply summable_norm_iff.mp
    apply (hc.2.2.2.1 X hX).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro p
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb p X hX)
  rw [←a03NativeGCD_triple_tsum hs]
  apply Eq.trans hmasked.2.2.2
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  exact a03NativeGCD_triple_tsum (hpoint X hX)


def a03ActualMaskedIntegratedRatioGCDVStar
    (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (dual : Bool) (Φ : ℝ→ℂ)
    (T a b s u ε : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  (T:ℂ)*∑positive : Bool,∑z∈Finset.range ⌊T^a⌋₊,∑v∈Finset.range ⌊T^b⌋₊,
    ∫X : ℝ in Ioi 0,∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,
      (a03NativeGCDSelectedDyadicMask select T a b s u ε f g (a03NativeGCDNatTuple z v m n h) X:ℂ)*
        a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v m n h X

/-- Literal integrated masked endpoint, with the finite source scales
fully regrouped into the actual countable native common-X expression. -/
theorem a03_actual_passive_retained_GCD_eq_integrated_masked {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (a b s u ε : ℝ) (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,(∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤1/4) →∀ dual : Bool,
      ∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
      a03ActualPassiveRetainedRatioGCDVStarFinite select dual Φ T a b s u ε σ α f g=
        a03ActualMaskedIntegratedRatioGCDVStar select dual Φ T a b s u ε σ α f g := by
  filter_upwards [a03_actual_passive_retained_GCD_eq_masked hΦ hSupp K hK hκ a b s u ε f g hf hg,
    a03_actual_native_masked_tsum_integral hΦ hSupp K hK hκ a b s u ε f g] with T he hx
  intro σ hσ hroot α hα dual select
  rw [he σ hσ hroot α hα dual select]
  unfold a03ActualMaskedRatioGCDVStar a03ActualMaskedIntegratedRatioGCDVStar
  congr 1
  apply Finset.sum_congr rfl
  intro positive _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro v _
  exact hx σ hσ hroot α hα dual positive select z v

def a03NativeGCDSelectedGridMask (S : Finset ((Fin 3→ℕ)×(Fin 4→ℕ)))
    (P : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (w : Fin 5→ℕ) (X : ℝ) : ℝ :=
  ∑i∈S,if P i then a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X else 0

theorem a03NativeGCDSelectedGridMask_bounds (S : Finset ((Fin 3→ℕ)×(Fin 4→ℕ)))
    (P : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (w : Fin 5→ℕ) (hw : ∀j,1≤w j) (X : ℝ) :
    0≤a03NativeGCDSelectedGridMask S P w X ∧ a03NativeGCDSelectedGridMask S P w X≤1 := by
  simpa only [a03NativeGCDSelectedGridMask,a03NativeGCDActualScales] using
    a03_native_GCD_selected_grid_weight_bounds S P w hw X

theorem a03NativeGCDSelectedGridMask_continuous (S : Finset ((Fin 3→ℕ)×(Fin 4→ℕ)))
    (P : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (w : Fin 5→ℕ) (hw : ∀j,1≤w j) :
    Continuous (a03NativeGCDSelectedGridMask S P w) := by
  unfold a03NativeGCDSelectedGridMask
  apply continuous_finsetSum
  intro i _
  by_cases hi : P i
  · simp only [hi,ite_true]
    convert a03NativeGCDSevenWeight_continuous w (a03GCDScaleTuple i) using 1
    funext X
    exact a03_native_GCD_all_weight_eq_seven_weight i w hw X
  · simp only [hi,ite_false]
    exact continuous_const

theorem a03NativeGCDSelectedGridMask_zero_outside (S : Finset ((Fin 3→ℕ)×(Fin 4→ℕ)))
    (P : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (w : Fin 5→ℕ)
    (hw : w∉S.biUnion (fun i => quadraticMainIndexSet (a03NativeGCDActualScales i))) (X : ℝ) :
    a03NativeGCDSelectedGridMask S P w X=0 := by
  unfold a03NativeGCDSelectedGridMask
  apply Finset.sum_eq_zero
  intro i hi
  have hwi : w∉quadraticMainIndexSet (a03NativeGCDActualScales i) :=
    fun h => hw (Finset.mem_biUnion.mpr ⟨i,hi,h⟩)
  rw [a03NativeGCDAllDyadicWeight_zero_outside_main _ (a03NativeGCDActualScales_pos i) w hwi X]
  exact ite_self 0

/-- Arbitrary genuine finite source selectors regroup into one common-X
mask. In particular the selector may be the actual discrete SourceGood. -/
theorem a03_native_GCD_selected_grid_integral_reindex
    (S : Finset ((Fin 3→ℕ)×(Fin 4→ℕ))) (P : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop)
    (dual positive : Bool) (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (hFI : ∀z v m n h,IntegrableOn
      (a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g z v m n h) (Ioi 0)) :
    (∑i∈S,if P i then ∑w∈quadraticMainIndexSet (a03NativeGCDActualScales i),
      ∫X : ℝ in Ioi 0,(a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X:ℂ)*
        a03NativeGCDDensity dual positive Φ T σ α f g w X else 0)=
    ∑w∈S.biUnion (fun i => quadraticMainIndexSet (a03NativeGCDActualScales i)),
      ∫X : ℝ in Ioi 0,(a03NativeGCDSelectedGridMask S P w X:ℂ)*
        a03NativeGCDDensity dual positive Φ T σ α f g w X := by
  let J := S.biUnion (fun i => quadraticMainIndexSet (a03NativeGCDActualScales i))
  let D := a03NativeGCDDensity dual positive Φ T σ α f g
  let W := fun i w X => if P i then a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X else 0
  have hJ (w : Fin 5→ℕ) (hw : w∈J) : ∀j,1≤w j := by
    obtain ⟨i,_,hwi⟩ := Finset.mem_biUnion.mp hw
    intro j
    exact (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hwi j)).1
  have hI (i : (Fin 3→ℕ)×(Fin 4→ℕ)) (w : Fin 5→ℕ) (hw : w∈J) :
      IntegrableOn (fun X => (W i w X:ℂ)*D w X) (Ioi 0) := by
    by_cases hi : P i
    · simp only [W,hi,ite_true]
      exact a03NativeGCDAllDyadicWeight_actual_integrable dual positive Φ T σ α f g hFI i w (hJ w hw)
    · simp only [W,hi,ite_false,Complex.ofReal_zero,zero_mul]
      exact integrable_zero _ _ _
  have hblock (i : (Fin 3→ℕ)×(Fin 4→ℕ)) (hi : i∈S) :
      (if P i then ∑w∈quadraticMainIndexSet (a03NativeGCDActualScales i),∫X : ℝ in Ioi 0,
        (a03NativeGCDAllDyadicWeight (a03NativeGCDActualScales i) w X:ℂ)*D w X else 0)=
      ∑w∈J,∫X : ℝ in Ioi 0,(W i w X:ℂ)*D w X := by
    by_cases hP : P i
    · simp only [hP,ite_true,W]
      apply Finset.sum_subset
      · intro w hw
        exact Finset.mem_biUnion.mpr ⟨i,hi,hw⟩
      · intro w _ hw
        simp only [a03NativeGCDAllDyadicWeight_zero_outside_main _ (a03NativeGCDActualScales_pos i) w hw,
          Complex.ofReal_zero,zero_mul,integral_zero]
    · simp only [hP,ite_false,W,Complex.ofReal_zero,zero_mul,integral_zero,Finset.sum_const_zero]
  calc
    _=∑i∈S,∑w∈J,∫X : ℝ in Ioi 0,(W i w X:ℂ)*D w X :=
      Finset.sum_congr rfl hblock
    _=_ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      rw [←integral_finsetSum S (fun i _ => hI i w hw)]
      apply integral_congr_ae
      filter_upwards [] with X
      simp only [a03NativeGCDSelectedGridMask,Complex.ofReal_sum,Finset.sum_mul,W,D]

end
end Sechstmoment
