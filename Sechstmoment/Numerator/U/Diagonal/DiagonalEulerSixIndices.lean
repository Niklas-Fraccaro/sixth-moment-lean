import Mathlib.Topology.Algebra.InfiniteSum.Real
import Sechstmoment.Numerator.U.Diagonal.DiagonalMellinEuler


namespace Sechstmoment
open ArithmeticFunction Nat
open scoped BigOperators

set_option maxHeartbeats 0

abbrev PositiveTripleIndices (n : ℕ) :=
  {x : ℕ × ℕ × ℕ // x.1*(x.2.1*x.2.2) = n ∧ n ≠ 0}

abbrev NestedTripleDivisors (n : ℕ) :=
  (d : ↥n.divisorsAntidiagonal) × ↥d.val.2.divisorsAntidiagonal

def positiveTripleDivisorsEquiv (n : ℕ) : NestedTripleDivisors n ≃ PositiveTripleIndices n where
  toFun x := ⟨(x.1.val.1,x.2.val.1,x.2.val.2), by
    obtain ⟨hd,hn⟩ := Nat.mem_divisorsAntidiagonal.mp x.1.property
    obtain ⟨he,_⟩ := Nat.mem_divisorsAntidiagonal.mp x.2.property
    exact ⟨by simpa only [he] using hd, hn⟩⟩
  invFun x := ⟨⟨(x.val.1,x.val.2.1*x.val.2.2),
      Nat.mem_divisorsAntidiagonal.mpr x.property⟩,
    ⟨(x.val.2.1,x.val.2.2), Nat.mem_divisorsAntidiagonal.mpr
      ⟨rfl, by
        intro h
        change x.val.2.1*x.val.2.2=0 at h
        apply x.property.2
        rw [← x.property.1,h,mul_zero]⟩⟩⟩
  left_inv x := by
    rcases x with ⟨⟨⟨i,d⟩,hd⟩,⟨⟨j,k⟩,he⟩⟩
    have h := (Nat.mem_divisorsAntidiagonal.mp he).1
    change j*k=d at h
    subst d
    rfl
  right_inv x := rfl

noncomputable instance positiveTripleIndicesFintype (n : ℕ) : Fintype (PositiveTripleIndices n) :=
  Fintype.ofEquiv (NestedTripleDivisors n) (positiveTripleDivisorsEquiv n)

noncomputable def literalTripleDirichletTerm (a : Fin 3 → ℂ) (x : ℕ × ℕ × ℕ) : ℂ :=
  shiftedPowerArithmetic (a 0) x.1*shiftedPowerArithmetic (a 1) x.2.1*
    shiftedPowerArithmetic (a 2) x.2.2

theorem shiftedTripleArithmetic_eq_positiveTripleSum (a : Fin 3 → ℂ) (n : ℕ) :
    shiftedTripleArithmetic a n =
      ∑ x : PositiveTripleIndices n, literalTripleDirichletTerm a x.val := by
  rw [← (positiveTripleDivisorsEquiv n).sum_comp]
  rw [Fintype.sum_sigma]
  change shiftedTripleArithmetic a n = ∑ d : ↥n.divisorsAntidiagonal,
    ∑ e : ↥d.val.2.divisorsAntidiagonal,
      shiftedPowerArithmetic (a 0) d.val.1*shiftedPowerArithmetic (a 1) e.val.1*
        shiftedPowerArithmetic (a 2) e.val.2
  rw [shiftedTripleArithmetic_apply a n,
    ← Finset.sum_coe_sort n.divisorsAntidiagonal (fun d =>
      ∑ e ∈ d.2.divisorsAntidiagonal,
        shiftedPowerArithmetic (a 0) d.1*shiftedPowerArithmetic (a 1) e.1*
          shiftedPowerArithmetic (a 2) e.2)]
  apply Finset.sum_congr rfl
  intro d _
  exact (Finset.sum_coe_sort d.val.2.divisorsAntidiagonal (fun e =>
    shiftedPowerArithmetic (a 0) d.val.1*shiftedPowerArithmetic (a 1) e.1*
      shiftedPowerArithmetic (a 2) e.2)).symm

abbrev DiagonalSixIndices :=
  {x : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) //
    x.1.1*(x.1.2.1*x.1.2.2) = x.2.1*(x.2.2.1*x.2.2.2) ∧
    x.1.1*(x.1.2.1*x.1.2.2) ≠ 0}

abbrev DiagonalSixFibers :=
  (n : ℕ) × (PositiveTripleIndices n × PositiveTripleIndices n)

def diagonalSixFibersEquiv : DiagonalSixFibers ≃ DiagonalSixIndices where
  toFun x := ⟨(x.2.1.val,x.2.2.val),
    ⟨x.2.1.property.1.trans x.2.2.property.1.symm,
      by simpa only [x.2.1.property.1] using x.2.1.property.2⟩⟩
  invFun x := ⟨x.val.1.1*(x.val.1.2.1*x.val.1.2.2),
    ⟨⟨x.val.1,⟨rfl,x.property.2⟩⟩,
      ⟨x.val.2,⟨x.property.1.symm,x.property.2⟩⟩⟩⟩
  left_inv x := by
    rcases x with ⟨n,⟨⟨x,hx⟩,⟨y,hy⟩⟩⟩
    have hn := hx.1
    change x.1*(x.2.1*x.2.2)=n at hn
    subst n
    rfl
  right_inv x := rfl

noncomputable def literalDiagonalSixTerm (a b : Fin 3 → ℂ) (x : DiagonalSixIndices) : ℂ :=
  literalTripleDirichletTerm a x.val.1*literalTripleDirichletTerm b x.val.2*
    shiftedPowerArithmetic 1 (x.val.1.1*(x.val.1.2.1*x.val.1.2.2))

theorem literalDiagonalSixTerm_fiber_sum (a b : Fin 3 → ℂ) (n : ℕ) :
    (∑ x : PositiveTripleIndices n × PositiveTripleIndices n,
      literalDiagonalSixTerm a b (diagonalSixFibersEquiv ⟨n,x⟩)) =
        shiftedDiagonalArithmetic a b 1 n := by
  change (∑ x : PositiveTripleIndices n × PositiveTripleIndices n,
    literalTripleDirichletTerm a x.1.val*literalTripleDirichletTerm b x.2.val*
      shiftedPowerArithmetic 1 (x.1.val.1*(x.1.val.2.1*x.1.val.2.2))) = _
  simp_rw [show ∀ x : PositiveTripleIndices n, x.val.1*(x.val.2.1*x.val.2.2)=n from
    fun x => x.property.1]
  rw [Fintype.sum_prod_type]
  change (∑ x : PositiveTripleIndices n, ∑ y : PositiveTripleIndices n,
    literalTripleDirichletTerm a x.val*literalTripleDirichletTerm b y.val*
      shiftedPowerArithmetic 1 n) = _
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [← shiftedTripleArithmetic_eq_positiveTripleSum,
    ← shiftedTripleArithmetic_eq_positiveTripleSum]
  rfl

theorem shiftedPowerArithmetic_re_eq_norm (a : ℂ) (n : ℕ) :
    shiftedPowerArithmetic (a.re:ℂ) n = (‖shiftedPowerArithmetic a n‖:ℂ) := by
  by_cases hn : n=0
  · simp [hn]
  rw [shiftedPowerArithmetic_apply _ hn, shiftedPowerArithmetic_apply _ hn,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp only [Complex.neg_re, ← Complex.ofReal_neg]
  exact (Complex.ofReal_cpow (Nat.cast_nonneg n) (-a.re)).symm

theorem literalTripleDirichletTerm_re_eq_norm (a : Fin 3 → ℂ) (x : ℕ × ℕ × ℕ) :
    literalTripleDirichletTerm (fun i => ((a i).re:ℂ)) x =
      (‖literalTripleDirichletTerm a x‖:ℂ) := by
  simp only [literalTripleDirichletTerm, shiftedPowerArithmetic_re_eq_norm,
    norm_mul, Complex.ofReal_mul]

theorem literalDiagonalSixTerm_re_eq_norm (a b : Fin 3 → ℂ) (x : DiagonalSixIndices) :
    literalDiagonalSixTerm (fun i => ((a i).re:ℂ)) (fun i => ((b i).re:ℂ)) x =
      (‖literalDiagonalSixTerm a b x‖:ℂ) := by
  have h1 (n : ℕ) : shiftedPowerArithmetic 1 n = (‖shiftedPowerArithmetic 1 n‖:ℂ) := by
    simpa only [Complex.one_re, Complex.ofReal_one] using shiftedPowerArithmetic_re_eq_norm 1 n
  unfold literalDiagonalSixTerm
  conv_lhs => rw [literalTripleDirichletTerm_re_eq_norm,
    literalTripleDirichletTerm_re_eq_norm, h1]
  simp only [norm_mul, Complex.ofReal_mul]

theorem literalDiagonalSixTerm_fiber_norm_sum (a b : Fin 3 → ℂ) (n : ℕ) :
    (∑ x : PositiveTripleIndices n × PositiveTripleIndices n,
      ‖literalDiagonalSixTerm a b (diagonalSixFibersEquiv ⟨n,x⟩)‖) =
        ‖shiftedDiagonalArithmetic (fun i => ((a i).re:ℂ))
          (fun i => ((b i).re:ℂ)) 1 n‖ := by
  calc
    _ = ‖∑ x : PositiveTripleIndices n × PositiveTripleIndices n,
      (‖literalDiagonalSixTerm a b (diagonalSixFibersEquiv ⟨n,x⟩)‖:ℂ)‖ := by
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg]
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    _ = ‖∑ x : PositiveTripleIndices n × PositiveTripleIndices n,
      literalDiagonalSixTerm (fun i => ((a i).re:ℂ)) (fun i => ((b i).re:ℂ))
        (diagonalSixFibersEquiv ⟨n,x⟩)‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      exact (literalDiagonalSixTerm_re_eq_norm a b _).symm
    _ = _ := by rw [literalDiagonalSixTerm_fiber_sum]

theorem literalDiagonalSixTerm_norm_summable {δ : ℝ} (hδ : 0 < δ)
    {a b : Fin 3 → ℂ} (ha : ∀ i, δ ≤ (a i).re) (hb : ∀ i, δ ≤ (b i).re) :
    Summable (fun x : DiagonalSixIndices => ‖literalDiagonalSixTerm a b x‖) := by
  apply diagonalSixFibersEquiv.summable_iff.mp
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro n
    exact (hasSum_fintype _).summable
  · simpa only [tsum_fintype, literalDiagonalSixTerm_fiber_norm_sum] using
      shiftedDiagonalArithmetic_norm_summable hδ
        (a := fun i => ((a i).re:ℂ)) (b := fun i => ((b i).re:ℂ))
        (by simpa using ha) (by simpa using hb)

theorem literalDiagonalSixTerm_tsum_eq_diagonal {δ : ℝ} (hδ : 0 < δ)
    {a b : Fin 3 → ℂ} (ha : ∀ i, δ ≤ (a i).re) (hb : ∀ i, δ ≤ (b i).re) :
    (∑' x : DiagonalSixIndices, literalDiagonalSixTerm a b x) =
      ∑' n, shiftedDiagonalArithmetic a b 1 n := by
  have hs := (literalDiagonalSixTerm_norm_summable hδ ha hb).of_norm
  rw [← diagonalSixFibersEquiv.tsum_eq]
  have hsig := diagonalSixFibersEquiv.summable_iff.mpr hs
  change Summable (fun x : DiagonalSixFibers =>
    literalDiagonalSixTerm a b (diagonalSixFibersEquiv x)) at hsig
  rw [hsig.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  apply tsum_congr
  intro n
  rw [tsum_fintype, literalDiagonalSixTerm_fiber_sum]

theorem literalDiagonalSixTerm_eq_zetaProduct_mul_rest {δ : ℝ} (hδ : 0 < δ)
    {a b : Fin 3 → ℂ} (ha : ∀ i, δ ≤ (a i).re) (hb : ∀ i, δ ≤ (b i).re) :
    (∑' x : DiagonalSixIndices, literalDiagonalSixTerm a b x) =
      (∏ ij : Fin 3 × Fin 3, riemannZeta (1+a ij.1+b ij.2))*shiftedPolarEulerRest a b := by
  rw [literalDiagonalSixTerm_tsum_eq_diagonal hδ ha hb,
    shiftedDiagonalArithmetic_eq_zetaProduct_mul_rest hδ ha hb]

end Sechstmoment
