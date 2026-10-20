import SixthMoment.Numerator.U.ZeroModes.Arithmetic.GCDRestrictedEuler
import SixthMoment.Numerator.U.ZeroModes.Ratio.EtaAnalytic


namespace SixthMoment
open ArithmeticFunction Nat Complex
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 0

abbrev A03DivisorPair (a b : ℕ) := {k : ℕ // k∈b.divisors} × {l : ℕ // l∈a.divisors}

def a03GCDDivisorSigmaEquiv {a b : ℕ} (ha : a≠0) (hb : b≠0) :
    (A03GCDDivisorIndex b × A03GCDDivisorIndex a) ≃
      (Σ kl : A03DivisorPair a b, A03CoprimeGCDPair (a/kl.2.val) (b/kl.1.val)) where
  toFun xy :=
    ⟨(⟨xy.1.divisor,Nat.mem_divisors.mpr ⟨xy.1.divides,hb⟩⟩,
      ⟨xy.2.divisor,Nat.mem_divisors.mpr ⟨xy.2.divides,ha⟩⟩),
      ⟨xy.1.residual,xy.2.residual,xy.1.residual_pos,xy.2.residual_pos,
        xy.1.coprime,xy.2.coprime⟩⟩
  invFun x :=
    (⟨x.1.1.val,Nat.dvd_of_mem_divisors x.1.1.property,
      Nat.pos_of_mem_divisors x.1.1.property,x.2.m,x.2.m_pos,x.2.m_coprime⟩,
     ⟨x.1.2.val,Nat.dvd_of_mem_divisors x.1.2.property,
      Nat.pos_of_mem_divisors x.1.2.property,x.2.n,x.2.n_pos,x.2.n_coprime⟩)
  left_inv x := by rcases x with ⟨⟨_,_,_,_,_,_⟩,⟨_,_,_,_,_,_⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨⟨_,_⟩,⟨_,_⟩⟩,⟨_,_,_,_,_,_⟩⟩; rfl

theorem a03GCDDivisorSigmaEquiv_term {a b : ℕ} (ha : a≠0) (hb : b≠0)
    (w z s : ℂ)
    (x : Σ kl : A03DivisorPair a b, A03CoprimeGCDPair (a/kl.2.val) (b/kl.1.val)) :
    a03GCDDivisorDirichletTerm w z s
      ((a03GCDDivisorSigmaEquiv ha hb).symm x).1
      ((a03GCDDivisorSigmaEquiv ha hb).symm x).2=
      ((x.1.1.val:ℂ)^(-(w+s))*(x.1.2.val:ℂ)^(-(z+s)))*a03RestrictedGCDTerm w z s x.2 := by
  simp only [a03GCDDivisorSigmaEquiv,Equiv.coe_fn_symm_mk,
    a03GCDDivisorDirichletTerm,a03RestrictedGCDTerm]
  ring

theorem a03GCDDirichlet_eq_restrictedDivisorSum {a b : ℕ}
    (ha : 0<a) (hb : 0<b) (hab : a.Coprime b)
    {w z s : ℂ} (hw : 0<w.re) (hz : 0<z.re) (hs : 1<s.re) :
    a03GCDDirichlet a b w z s=
      ∑ kl : A03DivisorPair a b,
        ((kl.1.val:ℂ)^(-(w+s))*(kl.2.val:ℂ)^(-(z+s)))*
          a03RestrictedGCDSeries (a/kl.2.val) (b/kl.1.val) w z s := by
  let e := a03GCDDivisorSigmaEquiv (Nat.ne_of_gt ha) (Nat.ne_of_gt hb)
  have hnorm := a03GCDDivisorDirichletTerm_norm_summable ha hb hab hw hz hs
  have hsig := hnorm.comp_injective e.symm.injective
  rw [a03GCDDirichlet_eq_divisorSum ha hb hab]
  rw [←e.symm.tsum_eq]
  rw [hsig.of_norm.tsum_sigma]
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro kl _
  unfold a03RestrictedGCDSeries
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  exact a03GCDDivisorSigmaEquiv_term _ _ w z s ⟨kl,x⟩

theorem bblrEtaArithmetic_eq_divisorSubtype (w z s : ℂ) {a : ℕ} (ha : a≠0) :
    bblrEtaArithmetic w 0 z 0 0 0 s a=
      ∑ l : {l : ℕ // l∈a.divisors},
        (l.val:ℂ)^(-(z+s))*a03GCDPrimeCorrectionProduct (a/l.val) w z s := by
  rw [bblrEtaArithmetic_apply _ _ _ _ _ _ _ ha]
  simp only [sub_zero,mul_zero,add_zero]
  rw [←Finset.sum_attach]
  rfl

theorem a03GCDDirichlet_eq_zeta_mul_eta {a b : ℕ}
    (ha : 0<a) (hb : 0<b) (hab : a.Coprime b)
    {w z s : ℂ} (hw : 0<w.re) (hz : 0<z.re) (hs : 1<s.re) :
    a03GCDDirichlet a b w z s=
      a03GCDZetaQuotient w z s*bblrEtaArithmetic w 0 z 0 0 0 s a*
        bblrEtaArithmetic z 0 w 0 0 0 s b := by
  rw [a03GCDDirichlet_eq_restrictedDivisorSum ha hb hab hw hz hs,
    bblrEtaArithmetic_eq_divisorSubtype w z s (Nat.ne_of_gt ha),
    bblrEtaArithmetic_eq_divisorSubtype z w s (Nat.ne_of_gt hb),Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  have haq : a/l.val≠0 := Nat.ne_of_gt
    (Nat.div_pos (Nat.le_of_dvd ha (Nat.dvd_of_mem_divisors l.property))
      (Nat.pos_of_mem_divisors l.property))
  have hbq : b/k.val≠0 := Nat.ne_of_gt
    (Nat.div_pos (Nat.le_of_dvd hb (Nat.dvd_of_mem_divisors k.property))
      (Nat.pos_of_mem_divisors k.property))
  have habq := (hab.coprime_div_left (Nat.dvd_of_mem_divisors l.property)).coprime_div_right
    (Nat.dvd_of_mem_divisors k.property)
  rw [a03RestrictedGCDSeries_eq_zeta_mul_corrections haq hbq habq hw hz
    (show 1<(1+w+z+s).re by simp only [add_re,one_re]; linarith)]
  ring

theorem bblrEtaArithmetic_reparametrize (α β γ δ u v s : ℂ) :
    bblrEtaArithmetic α β γ δ u v s=
      bblrEtaArithmetic (α-β+2*u) 0 (γ-δ+2*v) 0 0 0 s := by
  unfold bblrEtaArithmetic
  simp only [sub_zero,mul_zero,add_zero]
  rw [show α-β+γ-δ+2*u+2*v=(α-β+2*u)+(γ-δ+2*v) by ring]

namespace Source

theorem a03_source_gcdDirichlet_eq_ratioEta {a b : ℕ}
    (ha : 0<a) (hb : 0<b) (hab : a.Coprime b)
    (α : MomentShifts) (u v s : ℂ)
    (hu : 0<(α 0-α 1+2*u).re) (hv : 0<(α 2-α 3+2*v).re) (hs : 1<s.re) :
    a03GCDDirichlet a b (α 0-α 1+2*u) (α 2-α 3+2*v) s=
      a03GCDZetaQuotient (α 0-α 1+2*u) (α 2-α 3+2*v) s*
        a03ZeroModeRatioEtaPair α a b u v s := by
  rw [a03GCDDirichlet_eq_zeta_mul_eta ha hb hab hu hv hs]
  unfold a03ZeroModeRatioEtaPair
  rw [bblrEtaArithmetic_reparametrize (α 0) (α 1) (α 2) (α 3) u v s,
    bblrEtaArithmetic_reparametrize (α 2) (α 3) (α 0) (α 1) v u s]
  ring

theorem a03_source_gcdDirichlet_eq_commonAmplifier_ratioEta {a b : ℕ}
    (ha : 0<a) (hb : 0<b) (α : MomentShifts) (u v s : ℂ)
    (hu : 0<(α 0-α 1+2*u).re) (hv : 0<(α 2-α 3+2*v).re) (hs : 1<s.re) :
    a03GCDDirichlet a b (α 0-α 1+2*u) (α 2-α 3+2*v) s=
      (Nat.gcd a b:ℂ)^(1-s)*
        a03GCDZetaQuotient (α 0-α 1+2*u) (α 2-α 3+2*v) s*
          a03ZeroModeRatioEtaPair α (a/Nat.gcd a b) (b/Nat.gcd a b) u v s := by
  have hg : 0<Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
  have ha' : 0<a/Nat.gcd a b := Nat.div_pos (Nat.gcd_le_left _ ha) hg
  have hb' : 0<b/Nat.gcd a b := Nat.div_pos (Nat.gcd_le_right _ hb) hg
  calc
    _ = a03GCDDirichlet (Nat.gcd a b*(a/Nat.gcd a b))
        (Nat.gcd a b*(b/Nat.gcd a b)) (α 0-α 1+2*u) (α 2-α 3+2*v) s := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left a b),
        Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
    _ = _ := by
      rw [a03GCDDirichlet_commonAmplifier,
        a03_source_gcdDirichlet_eq_ratioEta ha' hb' (Nat.coprime_div_gcd_div_gcd hg)
          α u v s hu hv hs]
      ring

end Source

end
end SixthMoment
