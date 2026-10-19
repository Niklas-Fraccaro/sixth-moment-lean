import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.EtaMainFunction

/-! Entire dependence and vertical-strip bounds for the actual finite eta
arithmetic main-term sum. The bounds come from its divisor expansion. -/

namespace Sechstmoment.Source
open Complex
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 0

/-- Uniform boundedness on every finite closed vertical strip. -/
def A03VerticalStripBounded (f : ℂ → ℂ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, |s.re| ≤ R → ‖f s‖ ≤ C

private theorem a03VerticalStripBounded_const (c : ℂ) :
    A03VerticalStripBounded (fun _ : ℂ => c) := by
  intro R _
  exact ⟨‖c‖, norm_nonneg _, fun _ _ => le_rfl⟩

private theorem A03VerticalStripBounded.add {f g : ℂ → ℂ}
    (hf : A03VerticalStripBounded f) (hg : A03VerticalStripBounded g) :
    A03VerticalStripBounded (fun s => f s+g s) := by
  intro R hR
  obtain ⟨C,hC,hfC⟩ := hf R hR
  obtain ⟨D,hD,hgD⟩ := hg R hR
  refine ⟨C+D, by positivity, ?_⟩
  intro s hs
  exact (norm_add_le _ _).trans (add_le_add (hfC s hs) (hgD s hs))

private theorem A03VerticalStripBounded.sub {f g : ℂ → ℂ}
    (hf : A03VerticalStripBounded f) (hg : A03VerticalStripBounded g) :
    A03VerticalStripBounded (fun s => f s-g s) := by
  intro R hR
  obtain ⟨C,hC,hfC⟩ := hf R hR
  obtain ⟨D,hD,hgD⟩ := hg R hR
  refine ⟨C+D, by positivity, ?_⟩
  intro s hs
  exact (norm_sub_le _ _).trans (add_le_add (hfC s hs) (hgD s hs))

private theorem A03VerticalStripBounded.mul {f g : ℂ → ℂ}
    (hf : A03VerticalStripBounded f) (hg : A03VerticalStripBounded g) :
    A03VerticalStripBounded (fun s => f s*g s) := by
  intro R hR
  obtain ⟨C,hC,hfC⟩ := hf R hR
  obtain ⟨D,hD,hgD⟩ := hg R hR
  refine ⟨C*D, by positivity, ?_⟩
  intro s hs
  rw [norm_mul]
  exact mul_le_mul (hfC s hs) (hgD s hs) (norm_nonneg _) hC

private theorem A03VerticalStripBounded.sum {ι : Type*} (t : Finset ι)
    {f : ι → ℂ → ℂ} (hf : ∀ i ∈ t, A03VerticalStripBounded (f i)) :
    A03VerticalStripBounded (fun s => ∑ i ∈ t, f i s) := by
  classical
  revert hf
  induction t using Finset.induction_on with
  | empty => intro _; simpa using a03VerticalStripBounded_const 0
  | @insert i t hi ih =>
      intro hf
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self i t)).add
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem A03VerticalStripBounded.prod {ι : Type*} (t : Finset ι)
    {f : ι → ℂ → ℂ} (hf : ∀ i ∈ t, A03VerticalStripBounded (f i)) :
    A03VerticalStripBounded (fun s => ∏ i ∈ t, f i s) := by
  classical
  revert hf
  induction t using Finset.induction_on with
  | empty => intro _; simpa using a03VerticalStripBounded_const 1
  | @insert i t hi ih =>
      intro hf
      simpa only [Finset.prod_insert hi] using
        (hf i (Finset.mem_insert_self i t)).mul
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- A positive integer raised to a real-slope complex affine exponent is
uniformly bounded on finite vertical strips. -/
theorem a03NatCpowAffine_verticalStripBounded {n : ℕ} (hn : 0 < n)
    (c : ℂ) (k : ℝ) :
    A03VerticalStripBounded (fun s : ℂ => (n:ℂ)^(c+(k:ℂ)*s)) := by
  intro R _
  refine ⟨(n:ℝ)^(c.re+|k| *R), Real.rpow_nonneg (by positivity) _, ?_⟩
  intro s hs
  rw [Complex.norm_natCast_cpow_of_pos hn]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hmul : k*s.re ≤ |k| *R := by
    calc
      _ ≤ |k*s.re| := le_abs_self _
      _ = |k| *|s.re| := abs_mul _ _
      _ ≤ |k| *R := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  linarith

private theorem a03NatCpowAffine_differentiable {n : ℕ} (hn : 0 < n)
    (c : ℂ) (k : ℂ) :
    Differentiable ℂ (fun s : ℂ => (n:ℂ)^(c+k*s)) := by
  apply Differentiable.const_cpow (by fun_prop)
  exact Or.inl (Nat.cast_ne_zero.mpr hn.ne')

private theorem a03EtaCorrection_verticalStripBounded {p : ℕ} (hp : p.Prime)
    (c : ℂ) (k : ℝ) (y z : ℂ) :
    A03VerticalStripBounded (fun s : ℂ => bblrEtaCorrection p (c+(k:ℂ)*s) y z) := by
  have hpow : A03VerticalStripBounded (fun s : ℂ => (p:ℂ)^(-(1+(c+(k:ℂ)*s)))) := by
    convert a03NatCpowAffine_verticalStripBounded hp.pos (-(1+c)) (-k) using 1
    funext s
    congr 1
    push_cast
    ring
  unfold bblrEtaCorrection
  simpa only [div_eq_mul_inv] using
    (((a03VerticalStripBounded_const 1).sub hpow).mul
      (a03VerticalStripBounded_const (1-(p:ℂ)^(-(1+y))))).mul
        (a03VerticalStripBounded_const ((1-(p:ℂ)^(-(2+z)))⁻¹))

private theorem a03EtaCorrection_differentiable {p : ℕ} (hp : p.Prime)
    (c k y z : ℂ) :
    Differentiable ℂ (fun s : ℂ => bblrEtaCorrection p (c+k*s) y z) := by
  have hpow : Differentiable ℂ (fun s : ℂ => (p:ℂ)^(-(1+(c+k*s)))) := by
    convert a03NatCpowAffine_differentiable hp.pos (-(1+c)) (-k) using 1
    funext s
    congr 1
    ring
  unfold bblrEtaCorrection
  exact (((differentiable_const (1:ℂ)).sub hpow).mul_const _).div_const _

/-- The normalized eta coefficient is an explicit finite exponential
polynomial in the contour variable. -/
theorem a03NormalizedEtaArithmetic_divisor_sum (α β γ δ s : ℂ)
    {n : ℕ} (hn : n ≠ 0) :
    bblrNormalizedEtaArithmetic α β γ δ s n =
      (n:ℂ)^(β+s)*(∑ l ∈ n.divisors, (l:ℂ)^(-(β+γ+2*s))*
        ∏ p ∈ (n/l).primeFactors,
          bblrEtaCorrection p (α+γ+2*s) (γ-δ) (α-β+γ-δ)) := by
  rw [bblrNormalizedEtaArithmetic_apply α β γ δ s hn,
    bblrEtaArithmetic_apply α β γ δ 0 0 (β+δ+2*s) hn]
  simp only [mul_zero, add_zero]
  have h₁ : γ-δ+(β+δ+2*s)=β+γ+2*s := by ring
  have h₂ : α-β+γ-δ+(β+δ+2*s)=α+γ+2*s := by ring
  rw [h₁,h₂]

/-- Entire dependence is proved directly from the actual divisor sum. -/
theorem bblrNormalizedEtaArithmetic_differentiable (α β γ δ : ℂ)
    {n : ℕ} (hn : n ≠ 0) :
    Differentiable ℂ (fun s : ℂ => bblrNormalizedEtaArithmetic α β γ δ s n) := by
  simp_rw [a03NormalizedEtaArithmetic_divisor_sum α β γ δ _ hn]
  apply Differentiable.mul
  · convert a03NatCpowAffine_differentiable (Nat.pos_of_ne_zero hn) β 1 using 1
    simp
  · apply Differentiable.fun_sum
    intro l hl
    apply Differentiable.mul
    · convert a03NatCpowAffine_differentiable (Nat.pos_of_mem_divisors hl) (-(β+γ)) (-2) using 1
      funext s
      congr 1
      ring
    · apply Differentiable.fun_finsetProd
      intro p hp
      exact a03EtaCorrection_differentiable (Nat.prime_of_mem_primeFactors hp) (α+γ) 2 (γ-δ)
        (α-β+γ-δ)

/-- Uniform strip bounds are proved from finitely many positive-integer
powers; the correction denominator is independent of the contour variable. -/
theorem bblrNormalizedEtaArithmetic_verticalStripBounded (α β γ δ : ℂ)
    {n : ℕ} (hn : n ≠ 0) :
    A03VerticalStripBounded (fun s : ℂ => bblrNormalizedEtaArithmetic α β γ δ s n) := by
  simp_rw [a03NormalizedEtaArithmetic_divisor_sum α β γ δ _ hn]
  apply A03VerticalStripBounded.mul
  · convert a03NatCpowAffine_verticalStripBounded (Nat.pos_of_ne_zero hn) β 1 using 1
    simp
  · apply A03VerticalStripBounded.sum
    intro l hl
    apply A03VerticalStripBounded.mul
    · convert a03NatCpowAffine_verticalStripBounded (Nat.pos_of_mem_divisors hl) (-(β+γ)) (-2) using 1
      funext s
      congr 1
      norm_num
      ring
    · apply A03VerticalStripBounded.prod
      intro p hp
      simpa only [Complex.ofReal_ofNat] using
        a03EtaCorrection_verticalStripBounded (Nat.prime_of_mem_primeFactors hp)
          (α+γ) 2 (γ-δ) (α-β+γ-δ)

/-- The finite amplifier arithmetic factor is entire in `s`. -/
theorem a03EtaMainArithmetic_differentiable (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (α β γ δ : ℂ) :
    Differentiable ℂ (fun s : ℂ => a03EtaMainArithmetic N₁ N₂ a b α β γ δ s) := by
  unfold a03EtaMainArithmetic
  apply Differentiable.fun_sum
  intro g _
  apply Differentiable.fun_sum
  intro m hm
  apply Differentiable.fun_sum
  intro n hn
  by_cases hmn : m.Coprime n
  · have hd : Differentiable ℂ (fun s : ℂ =>
        a (g*m)*b (g*n)/((g*m*n:ℕ):ℂ)*
          bblrNormalizedEtaArithmetic α β γ δ s m*
          bblrNormalizedEtaArithmetic γ δ α β s n) :=
      ((differentiable_const _).mul
        (bblrNormalizedEtaArithmetic_differentiable α β γ δ (n := m)
          (by have := (Finset.mem_Icc.mp hm).1; omega))).mul
        (bblrNormalizedEtaArithmetic_differentiable γ δ α β (n := n)
          (by have := (Finset.mem_Icc.mp hn).1; omega))
    simpa only [ite_eq_left hmn] using hd
  · simpa only [ite_eq_right hmn] using
      (differentiable_const (0:ℂ) : Differentiable ℂ (fun _ : ℂ => (0:ℂ)))

/-- The finite amplifier factor is uniformly bounded on any finite strip. -/
theorem a03EtaMainArithmetic_verticalStripBounded (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (α β γ δ : ℂ) :
    A03VerticalStripBounded (fun s : ℂ => a03EtaMainArithmetic N₁ N₂ a b α β γ δ s) := by
  unfold a03EtaMainArithmetic
  apply A03VerticalStripBounded.sum
  intro g _
  apply A03VerticalStripBounded.sum
  intro m hm
  apply A03VerticalStripBounded.sum
  intro n hn
  by_cases hmn : m.Coprime n
  · simpa only [ite_eq_left hmn] using ((a03VerticalStripBounded_const _).mul
      (bblrNormalizedEtaArithmetic_verticalStripBounded α β γ δ (n := m)
        (by have := (Finset.mem_Icc.mp hm).1; omega))).mul
      (bblrNormalizedEtaArithmetic_verticalStripBounded γ δ α β (n := n)
        (by have := (Finset.mem_Icc.mp hn).1; omega))
  · simpa only [ite_eq_right hmn] using a03VerticalStripBounded_const (0:ℂ)

theorem a03EtaMainArithmetic_strip_bound (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (α β γ δ : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, |s.re| ≤ R →
      ‖a03EtaMainArithmetic N₁ N₂ a b α β γ δ s‖ ≤ C :=
  a03EtaMainArithmetic_verticalStripBounded N₁ N₂ a b α β γ δ R hR.le

end
end Sechstmoment.Source
