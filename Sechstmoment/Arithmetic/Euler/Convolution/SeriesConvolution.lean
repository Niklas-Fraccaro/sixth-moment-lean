import Sechstmoment.Arithmetic.Euler.Convolution.FiniteConvolution

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalConvolution
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest
open scoped BigOperators
noncomputable section
open Classical

def pairMul (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ × ℕ := (p.1.1*p.2.1, p.1.2*p.2.2)

def pairConv (F G : ℕ × ℕ → ℂ) (q : ℕ × ℕ) : ℂ :=
  ∑ d ∈ q.1.divisors, ∑ e ∈ q.2.divisors, F (d,e) * G (q.1/d,q.2/e)

def divisorPairEquivFiber (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m.divisors × n.divisors) ≃ (pairMul ⁻¹' {(m,n)}) where
  toFun p := ⟨((p.1.val,p.2.val),(m/p.1.val,n/p.2.val)), Prod.ext
    (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors p.1.property))
    (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors p.2.property))⟩
  invFun b := (⟨b.val.1.1, Nat.mem_divisors.mpr ⟨⟨b.val.2.1,
      (congrArg Prod.fst b.property).symm⟩,hm⟩⟩,
    ⟨b.val.1.2, Nat.mem_divisors.mpr ⟨⟨b.val.2.2,
      (congrArg Prod.snd b.property).symm⟩,hn⟩⟩)
  left_inv p := rfl
  right_inv b := by
    rcases b with ⟨⟨⟨d,e⟩,⟨r,t⟩⟩,hb⟩
    have h : d*r=m ∧ e*t=n := Prod.mk.inj hb
    have hd : 0 < d := Nat.pos_of_ne_zero (by intro H; simp [H] at h; exact hm h.1.symm)
    have he : 0 < e := Nat.pos_of_ne_zero (by intro H; simp [H] at h; exact hn h.2.symm)
    apply Subtype.ext
    change ((d,e),(m/d,n/e)) = ((d,e),(r,t))
    rw [← h.1, ← h.2, Nat.mul_div_cancel_left r hd, Nat.mul_div_cancel_left t he]

theorem pairConv_fiber (F G : ℕ × ℕ → ℂ)
    (hFL : ∀ n, F (0,n) = 0) (hFR : ∀ m, F (m,0) = 0)
    (hGL : ∀ n, G (0,n) = 0) (hGR : ∀ m, G (m,0) = 0) (q : ℕ × ℕ) :
    pairConv F G q = ∑' b : pairMul ⁻¹' {q}, F b.val.1 * G b.val.2 := by
  rcases q with ⟨m,n⟩
  by_cases hm : m = 0
  · subst m
    have H : ∀ b : pairMul ⁻¹' {(0,n)}, F b.val.1 * G b.val.2 = 0 := by
      intro b
      have hb : b.val.1.1*b.val.2.1=0 := congrArg Prod.fst b.property
      rcases Nat.mul_eq_zero.mp hb with h | h
      · have H : F b.val.1 = 0 := by change F (b.val.1.1,b.val.1.2) = 0; rw [h,hFL]
        rw [H,zero_mul]
      · have H : G b.val.2 = 0 := by change G (b.val.2.1,b.val.2.2) = 0; rw [h,hGL]
        rw [H,mul_zero]
    simp [pairConv,H]
  by_cases hn : n = 0
  · subst n
    have H : ∀ b : pairMul ⁻¹' {(m,0)}, F b.val.1 * G b.val.2 = 0 := by
      intro b
      have hb : b.val.1.2*b.val.2.2=0 := congrArg Prod.snd b.property
      rcases Nat.mul_eq_zero.mp hb with h | h
      · have H : F b.val.1 = 0 := by change F (b.val.1.1,b.val.1.2) = 0; rw [h,hFR]
        rw [H,zero_mul]
      · have H : G b.val.2 = 0 := by change G (b.val.2.1,b.val.2.2) = 0; rw [h,hGR]
        rw [H,mul_zero]
    simp [pairConv,H]
  symm
  calc
    _ = ∑' p : m.divisors × n.divisors,
        F (p.1.val,p.2.val) * G (m/p.1.val,n/p.2.val) :=
      ((divisorPairEquivFiber m n hm hn).tsum_eq _).symm
    _ = _ := by
      rw [tsum_fintype, Fintype.sum_prod_type]
      unfold pairConv
      rw [← Finset.sum_coe_sort m.divisors]
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_coe_sort n.divisors (fun e => F (d.val,e) * G (m/d.val,n/e))

theorem pairConv_hasSum (F G : ℕ × ℕ → ℂ) (A B : ℂ)
    (hF : HasSum F A) (hG : HasSum G B)
    (hFL : ∀ n, F (0,n) = 0) (hFR : ∀ m, F (m,0) = 0)
    (hGL : ∀ n, G (0,n) = 0) (hGR : ∀ m, G (m,0) = 0) :
    HasSum (pairConv F G) (A*B) := by
  have H := (hF.mul hG (summable_mul_of_summable_norm hF.summable.norm hG.summable.norm)).tsum_fiberwise pairMul
  simpa only [← pairConv_fiber F G hFL hFR hGL hGR] using H

def pairWeight (u v : ℂ) (F : ℕ × ℕ → ℂ) (q : ℕ × ℕ) : ℂ :=
  F q * (q.1:ℂ)^(-u) * (q.2:ℂ)^(-v)

theorem divisor_cpow_split (m d : ℕ) (hd : d ∈ m.divisors) (z : ℂ) :
    (m:ℂ)^z = (d:ℂ)^z * ((m/d:ℕ):ℂ)^z := by
  have H := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  calc
    _ = ((d*(m/d):ℕ):ℂ)^z := congrArg (fun k : ℕ => (k:ℂ)^z) H.symm
    _ = _ := by rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

theorem pairWeight_convolution (u v : ℂ) (F G : ℕ × ℕ → ℂ) :
    pairWeight u v (pairConv F G) = pairConv (pairWeight u v F) (pairWeight u v G) := by
  funext q
  simp only [pairWeight,pairConv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  rw [divisor_cpow_split q.1 d hd (-u), divisor_cpow_split q.2 e he (-v)]
  ring

end
end Sechstmoment.Source.NoDPGlobalConvolution
