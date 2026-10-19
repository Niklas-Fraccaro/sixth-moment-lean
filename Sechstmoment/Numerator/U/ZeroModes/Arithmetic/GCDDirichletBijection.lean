import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.GCDDirichlet

/-! Genuine divisor reindexing of the original GCD kernel.  Each divisor
and residual factor is recovered by a gcd and exact natural-number division. -/

namespace Sechstmoment
open Nat Complex
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

structure A03GCDDivisorIndex (b : ℕ) where
  divisor : ℕ
  divides : divisor∣b
  divisor_pos : 0<divisor
  residual : ℕ
  residual_pos : 0<residual
  coprime : residual.Coprime (b/divisor)

theorem a03GCDDivisorIndex_gcd {b : ℕ} (x : A03GCDDivisorIndex b) :
    Nat.gcd b (x.divisor*x.residual)=x.divisor := by
  nth_rw 1 [←Nat.mul_div_cancel' x.divides]
  rw [Nat.gcd_mul_left,x.coprime.symm.gcd_eq_one,mul_one]

def a03GCDDivisorEquiv (b : ℕ) (hb : 0<b) :
    {n : ℕ // 0<n} ≃ A03GCDDivisorIndex b where
  toFun n :=
    { divisor := Nat.gcd b n
      divides := Nat.gcd_dvd_left b n
      divisor_pos := Nat.gcd_pos_of_pos_left _ hb
      residual := n/Nat.gcd b n
      residual_pos := Nat.div_pos (Nat.gcd_le_right _ n.property)
        (Nat.gcd_pos_of_pos_left _ hb)
      coprime := (Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ hb)).symm }
  invFun x := ⟨x.divisor*x.residual,Nat.mul_pos x.divisor_pos x.residual_pos⟩
  left_inv n := by
    apply Subtype.ext
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right b n)
  right_inv x := by
    cases x with
    | mk k hk hkpos m hm hcop =>
      have hgcd : Nat.gcd b (k*m)=k := a03GCDDivisorIndex_gcd
        ⟨k,hk,hkpos,m,hm,hcop⟩
      simp only [hgcd,Nat.mul_div_cancel_left _ hkpos]

/-- This is the actual `k|b`, `l|a` bijection used before (22). -/
def a03GCDPairDivisorEquiv (a b : ℕ) (ha : 0<a) (hb : 0<b) :
    ({m : ℕ // 0<m} × {n : ℕ // 0<n}) ≃
      (A03GCDDivisorIndex b × A03GCDDivisorIndex a) :=
  Equiv.prodCongr (a03GCDDivisorEquiv b hb) (a03GCDDivisorEquiv a ha)

/-- The original gcd is exactly `k*l*gcd(m',n')`, including all prime powers
of the two amplifier integers. -/
theorem a03GCDPairDivisor_gcd {a b : ℕ} (hab : a.Coprime b)
    (x : A03GCDDivisorIndex b) (y : A03GCDDivisorIndex a) :
    Nat.gcd (a*(x.divisor*x.residual)) (b*(y.divisor*y.residual))=
      x.divisor*y.divisor*Nat.gcd x.residual y.residual := by
  have hab' : (a/y.divisor).Coprime (b/x.divisor) :=
    (hab.coprime_div_left y.divides).coprime_div_right x.divides
  have han : (a/y.divisor).Coprime ((b/x.divisor)*y.residual) :=
    hab'.mul_right y.coprime.symm
  have hbm : (b/x.divisor).Coprime x.residual := x.coprime.symm
  have h₁ : a*(x.divisor*x.residual)=
      (x.divisor*y.divisor)*((a/y.divisor)*x.residual) := by
    nth_rw 1 [←Nat.mul_div_cancel' y.divides]
    ring
  have h₂ : b*(y.divisor*y.residual)=
      (x.divisor*y.divisor)*((b/x.divisor)*y.residual) := by
    nth_rw 1 [←Nat.mul_div_cancel' x.divides]
    ring
  rw [h₁,h₂,Nat.gcd_mul_left,han.gcd_mul_left_cancel,
    hbm.gcd_mul_left_cancel_right]

def a03GCDDivisorDirichletTerm {a b : ℕ} (w z s : ℂ)
    (x : A03GCDDivisorIndex b) (y : A03GCDDivisorIndex a) : ℂ :=
  (x.divisor:ℂ)^(-(w+s))*(y.divisor:ℂ)^(-(z+s))*
    (Nat.gcd x.residual y.residual:ℂ)^(1-s)*
      (x.residual:ℂ)^(-(1+w))*(y.residual:ℂ)^(-(1+z))

/-- Reindexing preserves the literal summand, with the actual powers in (22). -/
theorem a03GCDDirichletTerm_divisor {a b : ℕ} (hab : a.Coprime b)
    (w z s : ℂ) (x : A03GCDDivisorIndex b) (y : A03GCDDivisorIndex a) :
    a03GCDDirichletTerm a b w z s
      (x.divisor*x.residual,y.divisor*y.residual)=
        a03GCDDivisorDirichletTerm w z s x y := by
  rw [a03GCDDirichletTerm_apply _ _ _ _ _
    (Nat.ne_of_gt (Nat.mul_pos x.divisor_pos x.residual_pos))
    (Nat.ne_of_gt (Nat.mul_pos y.divisor_pos y.residual_pos)),
    a03GCDPairDivisor_gcd hab]
  have hcpow (k l : ℕ) (r : ℂ) : ((k*l:ℕ):ℂ)^r=(k:ℂ)^r*(l:ℂ)^r := by
    simpa only [Nat.cast_mul] using Complex.natCast_mul_natCast_cpow k l r
  simp only [hcpow]
  have hx0 : (x.divisor:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt x.divisor_pos)
  have hy0 : (y.divisor:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt y.divisor_pos)
  have hx : (x.divisor:ℂ)^(1-s)*(x.divisor:ℂ)^(-(1+w))=
      (x.divisor:ℂ)^(-(w+s)) := by
    rw [←Complex.cpow_add _ _ hx0]
    congr 1
    ring
  have hy : (y.divisor:ℂ)^(1-s)*(y.divisor:ℂ)^(-(1+z))=
      (y.divisor:ℂ)^(-(z+s)) := by
    rw [←Complex.cpow_add _ _ hy0]
    congr 1
    ring
  unfold a03GCDDivisorDirichletTerm
  calc
    _ = ((x.divisor:ℂ)^(1-s)*(x.divisor:ℂ)^(-(1+w)))*
      ((y.divisor:ℂ)^(1-s)*(y.divisor:ℂ)^(-(1+z)))*
      (Nat.gcd x.residual y.residual:ℂ)^(1-s)*
      (x.residual:ℂ)^(-(1+w))*(y.residual:ℂ)^(-(1+z)) := by ring
    _ = _ := by rw [hx,hy]

def a03PositivePairEquiv : {x : ℕ × ℕ // 0<x.1 ∧ 0<x.2} ≃
    ({m : ℕ // 0<m} × {n : ℕ // 0<n}) where
  toFun x := (⟨x.val.1,x.property.1⟩,⟨x.val.2,x.property.2⟩)
  invFun x := ⟨(x.1,x.2),x.1.property,x.2.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by rcases x with ⟨⟨m,hm⟩,⟨n,hn⟩⟩; rfl

theorem a03GCDDirichlet_eq_positiveSum (a b : ℕ) (w z s : ℂ) :
    a03GCDDirichlet a b w z s=
      ∑' x : ({m : ℕ // 0<m} × {n : ℕ // 0<n}),
        a03GCDDirichletTerm a b w z s (x.1,x.2) := by
  have hsupport : Function.support (a03GCDDirichletTerm a b w z s) ⊆
      {x : ℕ × ℕ | 0<x.1 ∧ 0<x.2} := by
    intro x hx
    have hm : x.1≠0 := by
      intro hm
      exact hx (by simp [hm,a03GCDDirichletTerm])
    have hn : x.2≠0 := by
      intro hn
      exact hx (by simp [hn,a03GCDDirichletTerm])
    exact ⟨Nat.pos_of_ne_zero hm,Nat.pos_of_ne_zero hn⟩
  unfold a03GCDDirichlet
  rw [←tsum_subtype_eq_of_support_subset hsupport]
  exact a03PositivePairEquiv.symm.tsum_eq
    (fun x : {x : ℕ × ℕ // 0<x.1 ∧ 0<x.2} => a03GCDDirichletTerm a b w z s x.val)
    |>.symm

/-- Exact (22)-reindexing of the *original* GCD Dirichlet series.  The two
divisor sets, positive residuals and both coprimality restrictions are retained
in the target index type. -/
theorem a03GCDDirichlet_eq_divisorSum {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (hab : a.Coprime b) (w z s : ℂ) :
    a03GCDDirichlet a b w z s=
      ∑' xy : A03GCDDivisorIndex b × A03GCDDivisorIndex a,
        a03GCDDivisorDirichletTerm w z s xy.1 xy.2 := by
  rw [a03GCDDirichlet_eq_positiveSum]
  have h := (a03GCDPairDivisorEquiv a b ha hb).symm.tsum_eq
    (fun x : ({m : ℕ // 0<m} × {n : ℕ // 0<n}) =>
      a03GCDDirichletTerm a b w z s (x.1,x.2))
  rw [←h]
  apply tsum_congr
  intro xy
  exact a03GCDDirichletTerm_divisor hab w z s xy.1 xy.2

theorem a03GCDDivisorDirichletTerm_norm_summable {a b : ℕ}
    (ha : 0<a) (hb : 0<b) (hab : a.Coprime b)
    {w z s : ℂ} (hw : 0<w.re) (hz : 0<z.re) (hs : 1<s.re) :
    Summable (fun xy : A03GCDDivisorIndex b × A03GCDDivisorIndex a =>
      ‖a03GCDDivisorDirichletTerm w z s xy.1 xy.2‖) := by
  have hpos := (a03GCDDirichlet_norm_summable (Nat.ne_of_gt ha)
    (Nat.ne_of_gt hb) hw hz hs).subtype (fun x : ℕ × ℕ => 0<x.1 ∧ 0<x.2)
  have hp := hpos.comp_injective a03PositivePairEquiv.symm.injective
  have hd := hp.comp_injective (a03GCDPairDivisorEquiv a b ha hb).symm.injective
  apply hd.congr
  intro xy
  exact congrArg norm (a03GCDDirichletTerm_divisor hab w z s xy.1 xy.2)

/-- The first, common-amplifier gcd in BBLR §4 is retained explicitly. -/
theorem a03GCDDirichletTerm_commonAmplifier (g a b : ℕ) (w z s : ℂ)
    (x : ℕ × ℕ) :
    a03GCDDirichletTerm (g*a) (g*b) w z s x=
      (g:ℂ)^(1-s)*a03GCDDirichletTerm a b w z s x := by
  simp only [a03GCDDirichletTerm]
  rw [show g*a*x.1=g*(a*x.1) by ring,show g*b*x.2=g*(b*x.2) by ring,
    Nat.gcd_mul_left]
  have hcpow : ((g*Nat.gcd (a*x.1) (b*x.2):ℕ):ℂ)^(1-s)=
      (g:ℂ)^(1-s)*(Nat.gcd (a*x.1) (b*x.2):ℂ)^(1-s) := by
    simpa only [Nat.cast_mul] using
      Complex.natCast_mul_natCast_cpow g (Nat.gcd (a*x.1) (b*x.2)) (1-s)
  rw [hcpow]
  ring

theorem a03GCDDirichlet_commonAmplifier (g a b : ℕ) (w z s : ℂ) :
    a03GCDDirichlet (g*a) (g*b) w z s=
      (g:ℂ)^(1-s)*a03GCDDirichlet a b w z s := by
  unfold a03GCDDirichlet
  simp_rw [a03GCDDirichletTerm_commonAmplifier]
  exact tsum_mul_left

/-- Both reindexings applied to arbitrary positive amplifier integers, with
`g=gcd(a,b)` and the genuinely coprime residual amplifiers. -/
theorem a03GCDDirichlet_eq_gcdAmplifier_divisorSum {a b : ℕ}
    (ha : 0<a) (hb : 0<b) (w z s : ℂ) :
    a03GCDDirichlet a b w z s=
      (Nat.gcd a b:ℂ)^(1-s)*
      ∑' xy : A03GCDDivisorIndex (b/Nat.gcd a b) ×
        A03GCDDivisorIndex (a/Nat.gcd a b),
          a03GCDDivisorDirichletTerm w z s xy.1 xy.2 := by
  have hg : 0<Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
  have ha' : 0<a/Nat.gcd a b := Nat.div_pos (Nat.gcd_le_left _ ha) hg
  have hb' : 0<b/Nat.gcd a b := Nat.div_pos (Nat.gcd_le_right _ hb) hg
  calc
    a03GCDDirichlet a b w z s=
        a03GCDDirichlet (Nat.gcd a b*(a/Nat.gcd a b))
          (Nat.gcd a b*(b/Nat.gcd a b)) w z s := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left a b),
        Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
    _ = _ := by
      rw [a03GCDDirichlet_commonAmplifier,
        a03GCDDirichlet_eq_divisorSum ha' hb' (Nat.coprime_div_gcd_div_gcd hg)]

end
end Sechstmoment
