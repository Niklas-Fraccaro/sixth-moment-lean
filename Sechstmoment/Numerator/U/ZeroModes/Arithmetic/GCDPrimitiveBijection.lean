import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.GCDCoprimeZeta
import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.GCDDirichletBijection

/-! Primitive-pair decomposition of the genuinely restricted GCD series (22).
The common factor is itself restricted at the exceptional amplifier primes. -/

namespace Sechstmoment
open ArithmeticFunction Nat Complex
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 0

structure A03CoprimeGCDPair (A B : ℕ) where
  m : ℕ
  n : ℕ
  m_pos : 0<m
  n_pos : 0<n
  m_coprime : m.Coprime B
  n_coprime : n.Coprime A

@[ext] theorem A03CoprimeGCDPair.ext {A B : ℕ} {x y : A03CoprimeGCDPair A B}
    (hm : x.m=y.m) (hn : x.n=y.n) : x=y := by
  cases x
  cases y
  simp_all

structure A03PrimitiveGCDPair (A B : ℕ) extends A03CoprimeGCDPair A B where
  coprime : m.Coprime n

@[ext] theorem A03PrimitiveGCDPair.ext {A B : ℕ} {x y : A03PrimitiveGCDPair A B}
    (hm : x.m=y.m) (hn : x.n=y.n) : x=y := by
  cases x
  cases y
  congr 1
  exact A03CoprimeGCDPair.ext hm hn

abbrev A03GCDScale (A B : ℕ) := {d : ℕ // 0<d ∧ d.Coprime (A*B)}

def a03GCDPrimitiveEquiv (A B : ℕ) : A03CoprimeGCDPair A B ≃
    (A03GCDScale A B × A03PrimitiveGCDPair A B) where
  toFun x :=
    let d := Nat.gcd x.m x.n
    let hd := Nat.gcd_pos_of_pos_left x.n x.m_pos
    (⟨d,hd,(x.n_coprime.coprime_dvd_left (Nat.gcd_dvd_right x.m x.n)).mul_right
      (x.m_coprime.coprime_dvd_left (Nat.gcd_dvd_left x.m x.n))⟩,
    { m := x.m/d
      n := x.n/d
      m_pos := Nat.div_pos (Nat.gcd_le_left _ x.m_pos) hd
      n_pos := Nat.div_pos (Nat.gcd_le_right _ x.n_pos) hd
      m_coprime := x.m_coprime.coprime_div_left (Nat.gcd_dvd_left x.m x.n)
      n_coprime := x.n_coprime.coprime_div_left (Nat.gcd_dvd_right x.m x.n)
      coprime := Nat.coprime_div_gcd_div_gcd hd })
  invFun x :=
    { m := x.1.val*x.2.m
      n := x.1.val*x.2.n
      m_pos := Nat.mul_pos x.1.property.1 x.2.m_pos
      n_pos := Nat.mul_pos x.1.property.1 x.2.n_pos
      m_coprime := x.1.property.2.coprime_mul_left_right.mul_left x.2.m_coprime
      n_coprime := x.1.property.2.coprime_mul_right_right.mul_left x.2.n_coprime }
  left_inv x := by
    apply A03CoprimeGCDPair.ext
    · exact Nat.mul_div_cancel' (Nat.gcd_dvd_left x.m x.n)
    · exact Nat.mul_div_cancel' (Nat.gcd_dvd_right x.m x.n)
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [Nat.gcd_mul_left,x.2.coprime.gcd_eq_one,mul_one]
    · apply A03PrimitiveGCDPair.ext <;>
        simp only [Nat.gcd_mul_left,x.2.coprime.gcd_eq_one,mul_one,
          Nat.mul_div_cancel_left _ x.1.property.1]

def a03RestrictedGCDTerm {A B : ℕ} (w z s : ℂ) (x : A03CoprimeGCDPair A B) : ℂ :=
  (Nat.gcd x.m x.n:ℂ)^(1-s)*(x.m:ℂ)^(-(1+w))*(x.n:ℂ)^(-(1+z))

def a03RestrictedGCDSeries (A B : ℕ) (w z s : ℂ) : ℂ :=
  ∑' x : A03CoprimeGCDPair A B, a03RestrictedGCDTerm w z s x

def a03PrimitivePairTerm {A B : ℕ} (w z : ℂ) (x : A03PrimitiveGCDPair A B) : ℂ :=
  (x.m:ℂ)^(-(1+w))*(x.n:ℂ)^(-(1+z))

def a03PrimitivePairSeries (A B : ℕ) (w z : ℂ) : ℂ :=
  ∑' x : A03PrimitiveGCDPair A B, a03PrimitivePairTerm w z x

theorem a03RestrictedGCDTerm_primitive {A B : ℕ} (w z s : ℂ)
    (x : A03GCDScale A B × A03PrimitiveGCDPair A B) :
    a03RestrictedGCDTerm w z s ((a03GCDPrimitiveEquiv A B).symm x)=
      (x.1.val:ℂ)^(-(1+w+z+s))*a03PrimitivePairTerm w z x.2 := by
  simp only [a03RestrictedGCDTerm,a03GCDPrimitiveEquiv,Equiv.coe_fn_symm_mk,
    Nat.gcd_mul_left,x.2.coprime.gcd_eq_one,mul_one]
  have hcpow (k l : ℕ) (r : ℂ) : ((k*l:ℕ):ℂ)^r=(k:ℂ)^r*(l:ℂ)^r := by
    simpa only [Nat.cast_mul] using Complex.natCast_mul_natCast_cpow k l r
  simp only [hcpow]
  have hd0 : (x.1.val:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt x.1.property.1)
  have hd : (x.1.val:ℂ)^(1-s)*(x.1.val:ℂ)^(-(1+w))*
      (x.1.val:ℂ)^(-(1+z))=(x.1.val:ℂ)^(-(1+w+z+s)) := by
    rw [←Complex.cpow_add _ _ hd0,←Complex.cpow_add _ _ hd0]
    congr 1
    ring
  unfold a03PrimitivePairTerm
  calc
    _ = ((x.1.val:ℂ)^(1-s)*(x.1.val:ℂ)^(-(1+w))*(x.1.val:ℂ)^(-(1+z)))*
      ((x.2.m:ℂ)^(-(1+w))*(x.2.n:ℂ)^(-(1+z))) := by ring
    _ = _ := by rw [hd]

theorem a03PrimitivePairTerm_norm_summable (A B : ℕ)
    {w z : ℂ} (hw : 0<w.re) (hz : 0<z.re) :
    Summable (fun x : A03PrimitiveGCDPair A B => ‖a03PrimitivePairTerm w z x‖) := by
  have hm := shiftedPowerArithmetic_norm_summable
    (show 1<(1+w).re by simp only [add_re,one_re]; linarith)
  have hn := shiftedPowerArithmetic_norm_summable
    (show 1<(1+z).re by simp only [add_re,one_re]; linarith)
  have hprod := @Summable.mul_of_nonneg ℕ ℕ
    (fun n => ‖shiftedPowerArithmetic (1+w) n‖)
    (fun n => ‖shiftedPowerArithmetic (1+z) n‖) hm hn
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hinj : Function.Injective (fun x : A03PrimitiveGCDPair A B => (x.m,x.n)) := by
    intro x y h
    exact A03PrimitiveGCDPair.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  apply (hprod.comp_injective hinj).congr
  intro x
  simp only [Function.comp_def,a03PrimitivePairTerm,norm_mul,
    shiftedPowerArithmetic_apply _ (Nat.ne_of_gt x.m_pos),
    shiftedPowerArithmetic_apply _ (Nat.ne_of_gt x.n_pos)]

theorem a03GCDScale_power_tsum (A B : ℕ) (t : ℂ) :
    (∑' d : A03GCDScale A B, (d.val:ℂ)^(-t))=a03CoprimeZeta (A*B) t := by
  have hs : Function.support (fun n : ℕ => a03CoprimePowerArithmetic (A*B) t n) ⊆
      {n : ℕ | 0<n ∧ n.Coprime (A*B)} := by
    intro n hn
    by_cases hn0 : n=0
    · exact False.elim (hn (by simp [hn0]))
    by_cases hcop : n.Coprime (A*B)
    · exact ⟨Nat.pos_of_ne_zero hn0,hcop⟩
    · exact False.elim (hn (by simp [a03CoprimePowerArithmetic,hcop]))
  unfold a03CoprimeZeta
  rw [←tsum_subtype_eq_of_support_subset hs]
  apply tsum_congr
  intro d
  change (d.val:ℂ)^(-t)=if d.val.Coprime (A*B) then shiftedPowerArithmetic t d.val else 0
  rw [ite_eq_left d.property.2,shiftedPowerArithmetic_apply _ (Nat.ne_of_gt d.property.1)]

/-- The genuine restricted GCD series factors into its common-factor
Dirichlet sum and its primitive pair sum, via the proved bijection. -/
theorem a03RestrictedGCDSeries_eq_coprimeZeta_mul_primitive
    (A B : ℕ) {w z s : ℂ} (hw : 0<w.re) (hz : 0<z.re)
    (ht : 1<(1+w+z+s).re) :
    a03RestrictedGCDSeries A B w z s=
      a03CoprimeZeta (A*B) (1+w+z+s)*a03PrimitivePairSeries A B w z := by
  have hs : Summable (fun d : A03GCDScale A B => ‖(d.val:ℂ)^(-(1+w+z+s))‖) := by
    apply ((shiftedPowerArithmetic_norm_summable ht).subtype
      (fun d : ℕ => 0<d ∧ d.Coprime (A*B))).congr
    intro d
    simp only [Function.comp_def]
    rw [shiftedPowerArithmetic_apply _ (Nat.ne_of_gt d.property.1)]
  have hp := a03PrimitivePairTerm_norm_summable A B hw hz
  have hprod := @Summable.mul_of_nonneg (A03GCDScale A B) (A03PrimitiveGCDPair A B)
    (fun d => ‖(d.val:ℂ)^(-(1+w+z+s))‖)
    (fun x => ‖a03PrimitivePairTerm w z x‖) hs hp
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hnorm : Summable (fun x : A03GCDScale A B × A03PrimitiveGCDPair A B =>
      ‖(x.1.val:ℂ)^(-(1+w+z+s))*a03PrimitivePairTerm w z x.2‖) := by
    simpa only [norm_mul] using hprod
  unfold a03RestrictedGCDSeries a03PrimitivePairSeries
  rw [←(a03GCDPrimitiveEquiv A B).symm.tsum_eq]
  simp_rw [a03RestrictedGCDTerm_primitive]
  rw [←a03GCDScale_power_tsum A B (1+w+z+s)]
  exact (hs.of_norm.tsum_mul_tsum hp.of_norm hnorm.of_norm).symm

abbrev A03CoprimePositive (q : ℕ) := {d : ℕ // 0<d ∧ d.Coprime q}

def a03RestrictedPairEquiv (A B : ℕ) : A03CoprimeGCDPair A B ≃
    (A03CoprimePositive B × A03CoprimePositive A) where
  toFun x := (⟨x.m,x.m_pos,x.m_coprime⟩,⟨x.n,x.n_pos,x.n_coprime⟩)
  invFun x := ⟨x.1.val,x.2.val,x.1.property.1,x.2.property.1,
    x.1.property.2,x.2.property.2⟩
  left_inv x := by apply A03CoprimeGCDPair.ext <;> rfl
  right_inv x := by apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem a03CoprimePositive_power_tsum (q : ℕ) (t : ℂ) :
    (∑' d : A03CoprimePositive q, (d.val:ℂ)^(-t))=a03CoprimeZeta q t := by
  have hs : Function.support (fun n : ℕ => a03CoprimePowerArithmetic q t n) ⊆
      {n : ℕ | 0<n ∧ n.Coprime q} := by
    intro n hn
    by_cases hn0 : n=0
    · exact False.elim (hn (by simp [hn0]))
    by_cases hcop : n.Coprime q
    · exact ⟨Nat.pos_of_ne_zero hn0,hcop⟩
    · exact False.elim (hn (by simp [a03CoprimePowerArithmetic,hcop]))
  unfold a03CoprimeZeta
  rw [←tsum_subtype_eq_of_support_subset hs]
  apply tsum_congr
  intro d
  change (d.val:ℂ)^(-t)=if d.val.Coprime q then shiftedPowerArithmetic t d.val else 0
  rw [ite_eq_left d.property.2,shiftedPowerArithmetic_apply _ (Nat.ne_of_gt d.property.1)]

theorem a03CoprimePositive_power_norm_summable (q : ℕ) {t : ℂ} (ht : 1<t.re) :
    Summable (fun d : A03CoprimePositive q => ‖(d.val:ℂ)^(-t)‖) := by
  apply ((shiftedPowerArithmetic_norm_summable ht).subtype
    (fun d : ℕ => 0<d ∧ d.Coprime q)).congr
  intro d
  simp only [Function.comp_def]
  rw [shiftedPowerArithmetic_apply _ (Nat.ne_of_gt d.property.1)]

theorem a03RestrictedGCDSeries_one (A B : ℕ) {w z : ℂ}
    (hw : 0<w.re) (hz : 0<z.re) :
    a03RestrictedGCDSeries A B w z 1=
      a03CoprimeZeta B (1+w)*a03CoprimeZeta A (1+z) := by
  have hm := a03CoprimePositive_power_norm_summable B
    (show 1<(1+w).re by simp only [add_re,one_re]; linarith)
  have hn := a03CoprimePositive_power_norm_summable A
    (show 1<(1+z).re by simp only [add_re,one_re]; linarith)
  have hprod := @Summable.mul_of_nonneg (A03CoprimePositive B) (A03CoprimePositive A)
    (fun m => ‖(m.val:ℂ)^(-(1+w))‖) (fun n => ‖(n.val:ℂ)^(-(1+z))‖) hm hn
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hnorm : Summable (fun x : A03CoprimePositive B × A03CoprimePositive A =>
      ‖(x.1.val:ℂ)^(-(1+w))*(x.2.val:ℂ)^(-(1+z))‖) := by
    simpa only [norm_mul] using hprod
  unfold a03RestrictedGCDSeries
  rw [←(a03RestrictedPairEquiv A B).symm.tsum_eq]
  simp only [a03RestrictedGCDTerm,a03RestrictedPairEquiv,Equiv.coe_fn_symm_mk,
    sub_self,Complex.cpow_zero,one_mul]
  rw [←a03CoprimePositive_power_tsum B (1+w),←a03CoprimePositive_power_tsum A (1+z)]
  exact (hm.of_norm.tsum_mul_tsum hn.of_norm hnorm.of_norm).symm

/-- Complete evaluation of the restricted GCD series in terms of actual
coprime Dirichlet sums.  Both factorizations arise from proved bijections. -/
theorem a03RestrictedGCDSeries_eq_coprimeZeta_quotient {A B : ℕ}
    (hA : A≠0) (hB : B≠0) {w z s : ℂ} (hw : 0<w.re) (hz : 0<z.re)
    (ht : 1<(1+w+z+s).re) :
    a03RestrictedGCDSeries A B w z s=
      a03CoprimeZeta (A*B) (1+w+z+s)*a03CoprimeZeta B (1+w)*
        a03CoprimeZeta A (1+z)/a03CoprimeZeta (A*B) (2+w+z) := by
  have h2 : 1<(2+w+z).re := by simp only [add_re]; norm_num; linarith
  have hden := a03CoprimeZeta_ne_zero (mul_ne_zero hA hB) h2
  have hone := a03RestrictedGCDSeries_eq_coprimeZeta_mul_primitive A B hw hz
    (show 1<(1+w+z+(1:ℂ)).re by simp only [add_re,one_re]; linarith)
  have hexp : 1+w+z+(1:ℂ)=2+w+z := by ring
  rw [hexp,a03RestrictedGCDSeries_one A B hw hz] at hone
  rw [a03RestrictedGCDSeries_eq_coprimeZeta_mul_primitive A B hw hz ht]
  apply (eq_div_iff hden).mpr
  rw [show (a03CoprimeZeta (A*B) (1+w+z+s)*a03PrimitivePairSeries A B w z)*
      a03CoprimeZeta (A*B) (2+w+z)=
      a03CoprimeZeta (A*B) (1+w+z+s)*
        (a03CoprimeZeta (A*B) (2+w+z)*a03PrimitivePairSeries A B w z) by ring,
    ←hone]
  ring

end
end Sechstmoment
