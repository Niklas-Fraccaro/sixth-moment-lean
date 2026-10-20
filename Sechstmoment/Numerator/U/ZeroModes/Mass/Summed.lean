import Mathlib.Data.Fin.Tuple.Finset
import Sechstmoment.Numerator.U.ZeroModes.Mass.ActualSupport

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ZeroModeSmoothProduct (q : QuadraticScales) (v : Fin 5→ℕ) (x : ℝ) : ℝ :=
  ∏ i : Fin 5,rectangularSmoothBlockWeight (rectangularZeroArguments q v x i)

def a03ZeroModeLiteralMass (q : QuadraticScales) : ℝ :=
  ∑ v∈quadraticMainIndexSet q, ∫ x : ℝ in Ioi 0,a03ZeroModeSmoothProduct q v x*
    a03ZeroModeSixDensity (v 0) (v 1) (v 2) (v 3) (Nat.gcd (v 0*v 2) (v 1*v 3)) x

def a03ZeroModeQuadIndexSet (q : QuadraticScales) : Finset (Fin 4→ℕ) :=
  Fintype.piFinset (fun j => Finset.Icc 1 ⌊2*(![q.A,q.B,q.M₁,q.N₁] : Fin 4→ℝ) j⌋₊)

theorem a03ZeroModeSmoothProduct_factor (q : QuadraticScales) (v : Fin 5→ℕ) (x : ℝ) :
    a03ZeroModeSmoothProduct q v x=
      rectangularSmoothBlockWeight ((Nat.gcd (v 0*v 2) (v 1*v 3):ℝ)*(v 4:ℝ)/q.H)*
      rectangularSmoothBlockWeight ((v 2:ℝ)/q.M₁)*rectangularSmoothBlockWeight ((v 3:ℝ)/q.N₁)*
      a03ZeroModeContinuousSmoothWeight (v 0) (v 1) (v 2) (v 3)
        (Nat.gcd (v 0*v 2) (v 1*v 3)) q.M₂ q.N₂ x := by
  unfold a03ZeroModeSmoothProduct a03ZeroModeContinuousSmoothWeight rectangularZeroArguments
  simp only [Fin.prod_univ_five,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]
  ring

private theorem sum_snoc (q : QuadraticScales) (F : (Fin 5→ℕ)→ℝ) :
    (∑ v∈quadraticMainIndexSet q,F v)=
      ∑ u∈a03ZeroModeQuadIndexSet q, ∑ h∈Finset.Icc 1 ⌊2*q.H⌋₊, F (Fin.snoc u h) := by
  change _=∑ u∈a03ZeroModeQuadIndexSet q, ∑ h∈Finset.Icc 1 ⌊2*q.H⌋₊,
    (fun p : (Fin 4→ℕ)×ℕ => F (Fin.snoc p.1 p.2)) (u,h)
  rw [←Finset.sum_product (a03ZeroModeQuadIndexSet q) (Finset.Icc 1 ⌊2*q.H⌋₊)
    (fun p : (Fin 4→ℕ)×ℕ => F (Fin.snoc p.1 p.2))]
  symm
  apply Finset.sum_bij (fun p _ => Fin.snoc p.1 p.2)
  · intro p hp
    obtain ⟨hu,hh⟩ := Finset.mem_product.mp hp
    unfold quadraticMainIndexSet
    rw [Fin.mem_piFinset_iff_last_init]
    have hl : Fin.snoc (α:=fun _ : Fin 5 => ℕ) p.1 p.2 (4:Fin 5)=p.2 :=
      Fin.snoc_last (α:=fun _ : Fin 5 => ℕ) p.2 p.1
    simpa [Fin.init_snoc,hl,a03ZeroModeQuadIndexSet,Fin.init,Fin.forall_fin_succ] using And.intro hh hu
  · intro p hp r hr he
    have hi := congrArg Fin.init he
    have hl := congrFun he (Fin.last 4)
    simp only [Fin.init_snoc,Fin.snoc_last] at hi hl
    exact Prod.ext hi hl
  · intro v hv
    refine ⟨(Fin.init v,v (Fin.last 4)),?_,Fin.snoc_init_self v⟩
    unfold quadraticMainIndexSet at hv
    rw [Fin.mem_piFinset_iff_last_init] at hv
    apply Finset.mem_product.mpr
    simpa [a03ZeroModeQuadIndexSet,Fin.init,Fin.forall_fin_succ] using And.intro hv.2 hv.1
  · intro _ _
    rfl

theorem a03ZeroModeLiteralMass_eq_pair_mass (q : QuadraticScales) :
    a03ZeroModeLiteralMass q=∑ u∈a03ZeroModeQuadIndexSet q,
      a03ZeroModeLiteralPairMass (u 0) (u 1) (u 2) (u 3)
        (Nat.gcd (u 0*u 2) (u 1*u 3)) q.H q.M₁ q.M₂ q.N₁ q.N₂ := by
  unfold a03ZeroModeLiteralMass
  rw [sum_snoc]
  apply Finset.sum_congr rfl
  intro u _
  simp_rw [a03ZeroModeSmoothProduct_factor]
  simp only [show (0:Fin 5)=(0:Fin 4).castSucc by rfl,
    show (1:Fin 5)=(1:Fin 4).castSucc by rfl,show (2:Fin 5)=(2:Fin 4).castSucc by rfl,
    show (3:Fin 5)=(3:Fin 4).castSucc by rfl,show (4:Fin 5)=Fin.last 4 by rfl,
    Fin.snoc_castSucc,Fin.snoc_last]
  simp only [mul_assoc,integral_const_mul]
  unfold a03ZeroModeLiteralPairMass a03ZeroModeGapWeightSum a03ZeroModeContinuousSmoothMass
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem a03ZeroModeLiteralMass_nonneg (q : QuadraticScales) : 0≤a03ZeroModeLiteralMass q := by
  rw [a03ZeroModeLiteralMass_eq_pair_mass]
  exact Finset.sum_nonneg (fun _ _ => a03ZeroModeLiteralPairMass_nonneg _ _ _ _ _ _ _ _ _ _)

theorem a03ZeroModeLiteralMass_le_harmonic (q : QuadraticScales) (hH : 0<q.H) (hM₂ : 0<q.M₂) :
    a03ZeroModeLiteralMass q≤2*q.H*Real.log 2*
      (harmonic ⌊2*q.A⌋₊:ℝ)*(harmonic ⌊2*q.B⌋₊:ℝ)*
      (harmonic ⌊2*q.M₁⌋₊:ℝ)*(harmonic ⌊2*q.N₁⌋₊:ℝ) := by
  rw [a03ZeroModeLiteralMass_eq_pair_mass]
  have hh (n : ℕ) : (∑ j∈Finset.Icc 1 n,1/(j:ℝ))=(harmonic n:ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  calc
    _≤∑ u∈a03ZeroModeQuadIndexSet q,2*q.H*Real.log 2/((u 0:ℝ)*u 1*u 2*u 3) := by
      apply Finset.sum_le_sum
      intro u hu
      have hp (i : Fin 4) : 0<u i := by
        have h := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hu i)).1
        omega
      exact a03ZeroModeLiteralPairMass_le (by exact_mod_cast hp 0) (by exact_mod_cast hp 1)
        (by exact_mod_cast hp 2) (by exact_mod_cast hp 3)
        (a03ZeroMode_gcd_pos (hp 0) (hp 1) (hp 2) (hp 3)) hH hM₂
    _=(2*q.H*Real.log 2)*∑ u∈a03ZeroModeQuadIndexSet q,∏ i : Fin 4,1/(u i:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      simp only [Fin.prod_univ_four]
      ring
    _=(2*q.H*Real.log 2)*∏ i : Fin 4,
        ∑ j∈Finset.Icc 1 ⌊2*(![q.A,q.B,q.M₁,q.N₁] : Fin 4→ℝ) i⌋₊,1/(j:ℝ) := by
      unfold a03ZeroModeQuadIndexSet
      rw [←Finset.prod_univ_sum (fun i : Fin 4 => Finset.Icc 1 ⌊2*(![q.A,q.B,q.M₁,q.N₁] : Fin 4→ℝ) i⌋₊)
        (fun _ j => (1:ℝ)/(j:ℝ))]
    _=_ := by
      simp only [Fin.prod_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
      simp_rw [hh]
      ring


theorem a03ZeroModeHarmonic_le_uniform_log {T x r : ℝ} (hT : 1≤T) (hx : 2/3≤x)
    (hr : 0≤r) (hcut : x≤4*T^r) :
    (harmonic ⌊2*x⌋₊:ℝ)≤(1+Real.log 8+r)*(1+Real.log T) := by
  have hxp : 0<x := by linarith
  have hfloor : 1≤⌊2*x⌋₊ := by apply Nat.le_floor; norm_num; linarith
  have hfpos : 0<(⌊2*x⌋₊:ℝ) := by exact_mod_cast (show 0<⌊2*x⌋₊ by omega)
  have hf : (⌊2*x⌋₊:ℝ)≤8*T^r := (Nat.floor_le (by positivity : 0≤2*x)).trans (by linarith)
  have hlog := Real.log_le_log hfpos hf
  rw [Real.log_mul (by norm_num : (8:ℝ)≠0) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hT) r).ne',
    Real.log_rpow (zero_lt_one.trans_le hT)] at hlog
  have hlT : 0≤Real.log T := Real.log_nonneg hT
  have hl8 : 0≤Real.log 8 := Real.log_nonneg (by norm_num)
  calc
    _≤1+Real.log (⌊2*x⌋₊:ℝ) := harmonic_le_one_add_log _
    _≤1+Real.log 8+r*Real.log T := by linarith
    _≤_ := by nlinarith

theorem a03ZeroModeLiteralMass_le_polylog {T r : ℝ} (hT : 1≤T) (hr : 0≤r)
    (q : QuadraticScales) (hH : 0<q.H) (hM₂ : 0<q.M₂)
    (hl : 2/3≤q.A ∧ 2/3≤q.B ∧ 2/3≤q.M₁ ∧ 2/3≤q.N₁)
    (hc : q.A≤4*T^r ∧ q.B≤4*T^r ∧ q.M₁≤4*T^r ∧ q.N₁≤4*T^r) :
    a03ZeroModeLiteralMass q≤(2*Real.log 2*(1+Real.log 8+r)^4)*q.H*(1+Real.log T)^4 := by
  have hhA := a03ZeroModeHarmonic_le_uniform_log hT hl.1 hr hc.1
  have hhB := a03ZeroModeHarmonic_le_uniform_log hT hl.2.1 hr hc.2.1
  have hhM := a03ZeroModeHarmonic_le_uniform_log hT hl.2.2.1 hr hc.2.2.1
  have hhN := a03ZeroModeHarmonic_le_uniform_log hT hl.2.2.2 hr hc.2.2.2
  have hhn (n : ℕ) : 0≤(harmonic n:ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hl2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hl8 : 0≤Real.log 8 := Real.log_nonneg (by norm_num)
  have hlT : 0≤Real.log T := Real.log_nonneg hT
  calc
    _≤2*q.H*Real.log 2*(harmonic ⌊2*q.A⌋₊:ℝ)*(harmonic ⌊2*q.B⌋₊:ℝ)*
      (harmonic ⌊2*q.M₁⌋₊:ℝ)*(harmonic ⌊2*q.N₁⌋₊:ℝ) := a03ZeroModeLiteralMass_le_harmonic q hH hM₂
    _≤2*q.H*Real.log 2*((1+Real.log 8+r)*(1+Real.log T))*((1+Real.log 8+r)*(1+Real.log T))*
      ((1+Real.log 8+r)*(1+Real.log T))*((1+Real.log 8+r)*(1+Real.log T)) := by
        gcongr <;> exact hhn _
    _=_ := by ring

end
end Sechstmoment
