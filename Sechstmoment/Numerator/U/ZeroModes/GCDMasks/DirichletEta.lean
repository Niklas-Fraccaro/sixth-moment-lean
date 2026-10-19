import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.GCDDirichletEta

/-! Native `d=gcd(a*m,b*n)` indexing and the finite original amplifier
sum for the GCD-to-eta arithmetic join. -/

namespace Sechstmoment
open ArithmeticFunction Nat Complex
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 0

abbrev A03NativeGCDIndex (a b : ℕ) :=
  {x : ℕ × ℕ × ℕ // 0<x.1 ∧ 0<x.2.1 ∧ x.2.2=Nat.gcd (a*x.1) (b*x.2.1)}

def a03NativeGCDIndexEquiv (a b : ℕ) : A03NativeGCDIndex a b ≃
    ({m : ℕ // 0<m} × {n : ℕ // 0<n}) where
  toFun x := (⟨x.val.1,x.property.1⟩,⟨x.val.2.1,x.property.2.1⟩)
  invFun x := ⟨(x.1.val,x.2.val,Nat.gcd (a*x.1.val) (b*x.2.val)),
    x.1.property,x.2.property,rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext rfl x.property.2.2.symm)
  right_inv x := by apply Prod.ext <;> apply Subtype.ext <;> rfl

def a03NativeGCDDirichletTerm {a b : ℕ} (w z s : ℂ) (x : A03NativeGCDIndex a b) : ℂ :=
  (x.val.2.2:ℂ)^(1-s)*(x.val.1:ℂ)^(-(1+w))*(x.val.2.1:ℂ)^(-(1+z))

def a03NativeGCDDirichlet (a b : ℕ) (w z s : ℂ) : ℂ :=
  ∑' x : A03NativeGCDIndex a b, a03NativeGCDDirichletTerm w z s x

/-- The original positive `(m,n,d=gcd(a*m,b*n))` sum is the actual GCD
series, by an explicit equivalence rather than a reconstruction premise. -/
theorem a03NativeGCDDirichlet_eq (a b : ℕ) (w z s : ℂ) :
    a03NativeGCDDirichlet a b w z s=a03GCDDirichlet a b w z s := by
  unfold a03NativeGCDDirichlet
  rw [←(a03NativeGCDIndexEquiv a b).symm.tsum_eq,a03GCDDirichlet_eq_positiveSum]
  apply tsum_congr
  intro x
  exact (a03GCDDirichletTerm_apply a b w z s
    (Nat.ne_of_gt x.1.property) (Nat.ne_of_gt x.2.property)).symm

theorem a03NativeGCDDirichlet_norm_summable {a b : ℕ} (ha : 0<a) (hb : 0<b)
    {w z s : ℂ} (hw : 0<w.re) (hz : 0<z.re) (hs : 1<s.re) :
    Summable (fun x : A03NativeGCDIndex a b => ‖a03NativeGCDDirichletTerm w z s x‖) := by
  have hinj : Function.Injective (fun x : A03NativeGCDIndex a b => (x.val.1,x.val.2.1)) := by
    intro x y h
    apply (a03NativeGCDIndexEquiv a b).injective
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg (fun p : ℕ × ℕ => p.1) h
    · exact congrArg (fun p : ℕ × ℕ => p.2) h
  have hp := (a03GCDDirichlet_norm_summable (Nat.ne_of_gt ha) (Nat.ne_of_gt hb) hw hz hs).comp_injective hinj
  apply hp.congr
  intro x
  simp only [Function.comp_def,a03GCDDirichletTerm_apply a b w z s
    (Nat.ne_of_gt x.property.1) (Nat.ne_of_gt x.property.2.1),a03NativeGCDDirichletTerm,
    x.property.2.2]

namespace Source

def a03NativeAmplifierGCDDirichlet (N₁ N₂ : ℕ) (A B : ℕ→ℂ)
    (α : MomentShifts) (u v s : ℂ) : ℂ :=
  ∑ a∈Finset.Icc 1 N₁, ∑ b∈Finset.Icc 1 N₂,
    A a*B b*(a:ℂ)^(-(1-α 1+u))*(b:ℂ)^(-(1-α 3+v))*
      a03NativeGCDDirichlet a b (α 0-α 1+2*u) (α 2-α 3+2*v) s

/-- The native finite amplifier GCD expression is identified with the
actual eta arithmetic, retaining both original coefficient ranges. -/
theorem a03NativeAmplifierGCDDirichlet_eq_ratioEta (N₁ N₂ : ℕ) (A B : ℕ→ℂ)
    (α : MomentShifts) (u v s : ℂ)
    (hu : 0<(α 0-α 1+2*u).re) (hv : 0<(α 2-α 3+2*v).re) (hs : 1<s.re) :
    a03NativeAmplifierGCDDirichlet N₁ N₂ A B α u v s=
      ∑ a∈Finset.Icc 1 N₁, ∑ b∈Finset.Icc 1 N₂,
        A a*B b*(a:ℂ)^(-(1-α 1+u))*(b:ℂ)^(-(1-α 3+v))*
          ((Nat.gcd a b:ℂ)^(1-s)*
            a03GCDZetaQuotient (α 0-α 1+2*u) (α 2-α 3+2*v) s*
              a03ZeroModeRatioEtaPair α (a/Nat.gcd a b) (b/Nat.gcd a b) u v s) := by
  unfold a03NativeAmplifierGCDDirichlet
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [a03NativeGCDDirichlet_eq,a03_source_gcdDirichlet_eq_commonAmplifier_ratioEta
    (show 0<a from lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1)
    (show 0<b from lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb).1)
    α u v s hu hv hs]

end Source
end
end Sechstmoment
