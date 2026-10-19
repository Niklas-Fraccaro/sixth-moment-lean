import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.EtaMainFunction
import Sechstmoment.Numerator.U.ZeroModes.Ratio.PhysicalPowers

/-! Exact complex-power normalization after the actual positive common-X
Mellin evaluation. The original coefficients stay at g*a and g*b. -/
namespace Sechstmoment.Source
open Complex Real Set
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem a03PositiveStaticXMellin_normalization {P G A B : ℝ}
    (hP : 0<P) (hG : 0<G) (hA : 0<A) (hB : 0<B) (β δ s : ℂ) :
    (G:ℂ)^(-1+β+δ-s)*(A:ℂ)^(-1+β)*(B:ℂ)^(-1+δ)*
      ((P*G*Real.sqrt (A*B):ℝ):ℂ)^(s-β-δ)=
    (P:ℂ)^(s-β-δ)/((G*A*B:ℝ):ℂ)*
      (A:ℂ)^(β+(s-β-δ)/2)*(B:ℂ)^(δ+(s-β-δ)/2) := by
  have hc (r : ℝ) (hr : 0<r) (z : ℂ) : (r:ℂ)^z=exp ((Real.log r:ℂ)*z) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),←Complex.ofReal_log hr.le]
  have hY : 0<P*G*Real.sqrt (A*B) := by positivity
  have hlog : Real.log (P*G*Real.sqrt (A*B))=
      Real.log P+Real.log G+(Real.log A+Real.log B)/2 := by
    rw [Real.log_mul (mul_pos hP hG).ne' (Real.sqrt_pos.mpr (mul_pos hA hB)).ne',
      Real.log_mul hP.ne' hG.ne',Real.log_sqrt (mul_pos hA hB).le,Real.log_mul hA.ne' hB.ne']
  have hden : ((G*A*B:ℝ):ℂ)⁻¹=(G:ℂ)⁻¹*(A:ℂ)⁻¹*(B:ℂ)⁻¹ := by
    simp only [Complex.ofReal_mul,mul_inv_rev]
    ring
  rw [div_eq_mul_inv,hden,
    ←Complex.cpow_neg_one (G:ℂ),←Complex.cpow_neg_one (A:ℂ),←Complex.cpow_neg_one (B:ℂ)]
  simp_rw [hc G hG,hc A hA,hc B hB,hc P hP,hc _ hY]
  rw [hlog]
  push_cast
  repeat rw [←Complex.exp_add]
  congr 1
  ring

theorem a03ZeroModeStaticEtaXMellin_normalization (α : MomentShifts)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {P : ℝ} (hP : 0<P) (s : ℂ) :
    A (g*a)*B (g*b)*(g:ℂ)^(-1+α 1+α 3-s)*(a:ℂ)^(-1+α 1)*(b:ℂ)^(-1+α 3)*
      ((P*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)):ℝ):ℂ)^(s-α 1-α 3)*
        a03ZeroModeRatioEtaPair α a b 0 0 s=
    (P:ℂ)^(s-α 1-α 3)*(A (g*a)*B (g*b)/((g*a*b:ℕ):ℂ)*
      bblrNormalizedEtaArithmetic (α 0) (α 1) (α 2) (α 3) ((s-α 1-α 3)/2) a*
      bblrNormalizedEtaArithmetic (α 2) (α 3) (α 0) (α 1) ((s-α 1-α 3)/2) b) := by
  have hp := a03PositiveStaticXMellin_normalization (G:=(g:ℝ)) (A:=(a:ℝ)) (B:=(b:ℝ)) hP (by exact_mod_cast hg)
    (by exact_mod_cast ha) (by exact_mod_cast hb) (α 1) (α 3) s
  have he₁ : α 1+α 3+2*((s-α 1-α 3)/2)=s := by ring
  have he₂ : α 3+α 1+2*((s-α 1-α 3)/2)=s := by ring
  rw [bblrNormalizedEtaArithmetic_apply _ _ _ _ _ ha.ne',
    bblrNormalizedEtaArithmetic_apply _ _ _ _ _ hb.ne',he₁,he₂]
  unfold a03ZeroModeRatioEtaPair
  simp only [Complex.ofReal_natCast] at hp
  simp only [Nat.cast_mul]
  calc
    _=(A (g*a)*B (g*b))*
      ((g:ℂ)^(-1+α 1+α 3-s)*(a:ℂ)^(-1+α 1)*(b:ℂ)^(-1+α 3)*
        ((P*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)):ℝ):ℂ)^(s-α 1-α 3))*
          (bblrEtaArithmetic (α 0) (α 1) (α 2) (α 3) 0 0 s a*
            bblrEtaArithmetic (α 2) (α 3) (α 0) (α 1) 0 0 s b) := by ring
    _=_ := by rw [hp]; push_cast; ring

def a03ZeroModeStaticEtaXMellinArithmetic (N₁ N₂ : ℕ) (A B : ℕ→ℂ)
    (α : MomentShifts) (P : ℝ) (s : ℂ) : ℂ :=
  ∑ g∈Finset.Icc 1 (min N₁ N₂),∑ a∈Finset.Icc 1 (N₁/g),∑ b∈Finset.Icc 1 (N₂/g),
    if a.Coprime b then
      A (g*a)*B (g*b)*(g:ℂ)^(-1+α 1+α 3-s)*(a:ℂ)^(-1+α 1)*(b:ℂ)^(-1+α 3)*
        ((P*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)):ℝ):ℂ)^(s-α 1-α 3)*
          a03ZeroModeRatioEtaPair α a b 0 0 s else 0

/-- The finite coefficient array obtained from the literal common-X
Mellin scale is the existing M-arithmetic, with its original amplitudes. -/
theorem a03ZeroModeStaticEtaXMellinArithmetic_eq_MArithmetic (N₁ N₂ : ℕ)
    (A B : ℕ→ℂ) (α : MomentShifts) {P : ℝ} (hP : 0<P) (s : ℂ) :
    a03ZeroModeStaticEtaXMellinArithmetic N₁ N₂ A B α P s=
      (P:ℂ)^(s-α 1-α 3)*a03EtaMainArithmetic N₁ N₂ A B
        (α 0) (α 1) (α 2) (α 3) ((s-α 1-α 3)/2) := by
  unfold a03ZeroModeStaticEtaXMellinArithmetic a03EtaMainArithmetic
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs
  · exact a03ZeroModeStaticEtaXMellin_normalization α
      (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hg).1)
      (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1)
      (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb).1) A B hP s
  · exact (mul_zero _).symm

end
end Sechstmoment.Source
