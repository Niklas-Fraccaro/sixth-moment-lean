import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import SixthMoment.Numerator.U.ZeroModes.Arithmetic.EtaArithmetic
import SixthMoment.Numerator.U.ZeroModes.Contour.RatioPoleRemoval
import SixthMoment.Zeta.Bounds.MellinZetaInverseDirichletBounds


namespace SixthMoment.Source
open Complex Real Set
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 0

private theorem a03Ratio_differentiableAt_div
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E→ℂ} {z : E} (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (hg0 : g z≠0) :
    DifferentiableAt ℂ (fun y => f y/g y) z := by
  convert hf.mul ((differentiableAt_inv hg0).comp z hg) using 1
  funext y
  exact div_eq_mul_inv _ _

private theorem a03Ratio_differentiableAt_finsetProd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [DecidableEq ι] (t : Finset ι) {f : ι→E→ℂ} {z : E}
    (hf : ∀ j∈t,DifferentiableAt ℂ (f j) z) :
    DifferentiableAt ℂ (fun y => ∏ j∈t,f j y) z := by
  exact (HasFDerivAt.finsetProd (fun j hj => (hf j hj).hasFDerivAt)).differentiableAt

def a03ZeroModeRatioEulerArgument (α : MomentShifts) (u v : ℂ) : ℂ :=
  2+α 0-α 1+α 2-α 3+2*u+2*v

def a03ZeroModeRatioEtaPair (α : MomentShifts) (a b : ℕ) (u v s : ℂ) : ℂ :=
  bblrEtaArithmetic (α 0) (α 1) (α 2) (α 3) u v s a*
    bblrEtaArithmetic (α 2) (α 3) (α 0) (α 1) v u s b

def a03ZeroModeRatioArithmeticNumerator (α : MomentShifts) (a b : ℕ)
    (u v s : ℂ) : ℂ :=
  a03ZeroModeRatioRemovedPair α u v*riemannZeta s*
    riemannZeta (a03ZeroModeRatioEulerArgument α u v-1+s)/
      riemannZeta (a03ZeroModeRatioEulerArgument α u v)*
        a03ZeroModeRatioEtaPair α a b u v s

theorem a03ZeroModeRatioEtaPair_actual_formula (α : MomentShifts)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) (u v s : ℂ) :
    a03ZeroModeRatioEtaPair α a b u v s=
      (∑ l∈a.divisors,(l:ℂ)^(-(α 2-α 3+2*v+s))*
        ∏ p∈(a/l).primeFactors,bblrEtaCorrection p
          (α 0-α 1+α 2-α 3+2*u+2*v+s)
          (α 2-α 3+2*v) (α 0-α 1+α 2-α 3+2*u+2*v))*
      (∑ k∈b.divisors,(k:ℂ)^(-(α 0-α 1+2*u+s))*
        ∏ p∈(b/k).primeFactors,bblrEtaCorrection p
          (α 2-α 3+α 0-α 1+2*v+2*u+s)
          (α 0-α 1+2*u) (α 2-α 3+α 0-α 1+2*v+2*u)) := by
  unfold a03ZeroModeRatioEtaPair
  rw [bblrEtaArithmetic_apply _ _ _ _ _ _ _ ha,
    bblrEtaArithmetic_apply _ _ _ _ _ _ _ hb]

theorem bblrEtaArithmetic_differentiableAt_comp_ratio (α β γ δ s : ℂ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (hn : n≠0) {U V : E→ℂ} {z : E}
    (hU : DifferentiableAt ℂ U z) (hV : DifferentiableAt ℂ V z)
    (hden : 1<(2+α-β+γ-δ+2*U z+2*V z).re) :
    DifferentiableAt ℂ (fun y => bblrEtaArithmetic α β γ δ (U y) (V y) s n) z := by
  simp_rw [bblrEtaArithmetic_apply α β γ δ _ _ s hn]
  apply DifferentiableAt.fun_sum
  intro l hl
  apply DifferentiableAt.mul
  · apply DifferentiableAt.const_cpow
      (((hV.const_mul 2).const_add (γ-δ)).add_const s).neg
    exact Or.inl (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hl).ne')
  · apply a03Ratio_differentiableAt_finsetProd
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    unfold bblrEtaCorrection
    apply a03Ratio_differentiableAt_div
    · apply DifferentiableAt.mul
      · apply DifferentiableAt.const_sub
        apply DifferentiableAt.const_cpow
        · exact (((((hU.const_mul 2).const_add (α-β+γ-δ)).add
            (hV.const_mul 2)).add_const s).const_add 1).neg
        · exact Or.inl (Nat.cast_ne_zero.mpr hp'.ne_zero)
      · apply DifferentiableAt.const_sub
        apply DifferentiableAt.const_cpow
        · exact ((((hV.const_mul 2).const_add (γ-δ)).const_add 1).neg)
        · exact Or.inl (Nat.cast_ne_zero.mpr hp'.ne_zero)
    · apply DifferentiableAt.const_sub
      apply DifferentiableAt.const_cpow
      · exact ((((hU.const_mul 2).const_add (α-β+γ-δ)).add
          (hV.const_mul 2)).const_add 2).neg
      · exact Or.inl (Nat.cast_ne_zero.mpr hp'.ne_zero)
    · apply Complex.one_sub_prime_cpow_ne_zero hp'
      convert hden using 1
      congr 1
      ring

theorem a03ZeroModeRatioEtaPair_differentiableAt_comp (α : MomentShifts)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : ℕ} (ha : a≠0) (hb : b≠0) (s : ℂ) {U V : E→ℂ} {z : E}
    (hU : DifferentiableAt ℂ U z) (hV : DifferentiableAt ℂ V z)
    (hden : 1<(a03ZeroModeRatioEulerArgument α (U z) (V z)).re) :
    DifferentiableAt ℂ (fun y => a03ZeroModeRatioEtaPair α a b (U y) (V y) s) z := by
  unfold a03ZeroModeRatioEtaPair
  apply DifferentiableAt.mul
  · exact bblrEtaArithmetic_differentiableAt_comp_ratio _ _ _ _ s ha hU hV hden
  · apply bblrEtaArithmetic_differentiableAt_comp_ratio _ _ _ _ s hb hV hU
    convert hden using 1
    unfold a03ZeroModeRatioEulerArgument
    congr 1
    ring

theorem a03ZeroModeRatioArithmeticNumerator_differentiableAt_comp (α : MomentShifts)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1≤s.re)
    {U V : E→ℂ} {z : E}
    (hU : DifferentiableAt ℂ U z) (hV : DifferentiableAt ℂ V z)
    (hden : 1<(a03ZeroModeRatioEulerArgument α (U z) (V z)).re) :
    DifferentiableAt ℂ
      (fun y => a03ZeroModeRatioArithmeticNumerator α a b (U y) (V y) s) z := by
  have hA : DifferentiableAt ℂ
      (fun y => a03ZeroModeRatioEulerArgument α (U y) (V y)) z :=
    ((hU.const_mul 2).const_add (2+α 0-α 1+α 2-α 3)).add (hV.const_mul 2)
  have hmiddle : a03ZeroModeRatioEulerArgument α (U z) (V z)-1+s≠1 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [add_re,sub_re,one_re] at hre
    linarith
  have hAone : a03ZeroModeRatioEulerArgument α (U z) (V z)≠1 := by
    intro he
    rw [he,one_re] at hden
    linarith
  unfold a03ZeroModeRatioArithmeticNumerator a03ZeroModeRatioRemovedPair
  apply DifferentiableAt.mul
  · apply a03Ratio_differentiableAt_div
    · exact (((a03ZeroModeRatioRemovedDifference_differentiable α 0).differentiableAt.comp z hU).mul
        ((a03ZeroModeRatioRemovedDifference_differentiable α 1).differentiableAt.comp z hV)).mul_const
          (riemannZeta s) |>.mul
            ((differentiableAt_riemannZeta hmiddle).comp z ((hA.sub_const 1).add_const s))
    · exact (differentiableAt_riemannZeta hAone).comp z hA
    · exact riemannZeta_ne_zero_of_one_lt_re hden
  · exact a03ZeroModeRatioEtaPair_differentiableAt_comp α ha hb s hU hV hden

theorem a03ZeroModeRatioArithmeticNumerator_eq (α : MomentShifts)
    (a b : ℕ) (s : ℂ) (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {u v : ℂ} (hu : u≠a03ZeroModeRatioRoot α 0) (hv : v≠a03ZeroModeRatioRoot α 1) :
    a03ZeroModeRatioArithmeticNumerator α a b u v s/(u*v)=
      (a03ZeroModeRatioWeight α u/u)*(a03ZeroModeRatioWeight α v/v)*
        (riemannZeta s*riemannZeta (1+α 0-α 1+α 2-α 3+2*u+2*v+s)*
          riemannZeta (1+α 0-α 1+2*u)*riemannZeta (1+α 2-α 3+2*v)/
            riemannZeta (2+α 0-α 1+α 2-α 3+2*u+2*v))*
              a03ZeroModeRatioEtaPair α a b u v s := by
  have hp := a03ZeroModeRatioRemovedPair_eq α hρ hu hv
  unfold a03ZeroModeRatioArithmeticNumerator a03ZeroModeRatioEulerArgument
  have he : 2+α 0-α 1+α 2-α 3+2*u+2*v-1+s=
      1+α 0-α 1+α 2-α 3+2*u+2*v+s := by ring
  rw [he]
  calc
    _ = (a03ZeroModeRatioRemovedPair α u v/(u*v))*
        (riemannZeta s*riemannZeta (1+α 0-α 1+α 2-α 3+2*u+2*v+s)/
          riemannZeta (2+α 0-α 1+α 2-α 3+2*u+2*v))*
            a03ZeroModeRatioEtaPair α a b u v s := by ring
    _ = _ := by rw [hp]; ring

end
end SixthMoment.Source
