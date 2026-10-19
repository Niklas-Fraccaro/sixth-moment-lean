import Sechstmoment.Numerator.U.Sources.FiniteAmplifierGCDReindex

/-! Literal four chamber labels and their original amplifier gcd factors.
The arithmetic terms are the ones already bounded against the source six
VStar diagonal terms. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_shiftedPairArithmetic_swap (a b : ℂ) :
    shiftedPairArithmetic a b=shiftedPairArithmetic b a := by
  unfold shiftedPairArithmetic
  exact mul_comm _ _

theorem a03BPrimeFactor_swap_first (p : ℕ) (a b c d : ℂ) (ν : ℕ) :
    bblrBPrimeFactor p a b c d ν=bblrBPrimeFactor p b a c d ν := by
  unfold bblrBPrimeFactor
  simp_rw [a03_shiftedPairArithmetic_swap a b]

theorem a03BPrimeFactor_swap_last (p : ℕ) (a b c d : ℂ) (ν : ℕ) :
    bblrBPrimeFactor p a b c d ν=bblrBPrimeFactor p a b d c ν := by
  unfold bblrBPrimeFactor
  simp_rw [a03_shiftedPairArithmetic_swap c d]

theorem a03BFactor_swap_first (a b c d : ℂ) (n : ℕ) :
    bblrBFactor a b c d n=bblrBFactor b a c d n := by
  unfold bblrBFactor
  simp_rw [a03BPrimeFactor_swap_first _ a b c d]

theorem a03BFactor_swap_last (a b c d : ℂ) (n : ℕ) :
    bblrBFactor a b c d n=bblrBFactor a b d c n := by
  unfold bblrBFactor
  simp_rw [a03BPrimeFactor_swap_last _ a b c d]

theorem a03AArithmetic_swap_first (a b c d : ℂ) :
    bblrAArithmetic a b c d=bblrAArithmetic b a c d := by
  unfold bblrAArithmetic
  rw [show 2+b+a+c+d=2+a+b+c+d by ring]
  ring

theorem a03AArithmetic_swap_last (a b c d : ℂ) :
    bblrAArithmetic a b c d=bblrAArithmetic a b d c := by
  unfold bblrAArithmetic
  rw [show 2+a+b+d+c=2+a+b+c+d by ring]
  ring

theorem a03ZArithmetic_swap_first (a b c d : ℂ) (m n : ℕ) :
    bblrZArithmetic a b c d m n=bblrZArithmetic b a c d m n := by
  unfold bblrZArithmetic
  rw [a03AArithmetic_swap_first a b c d,a03BFactor_swap_first a b c d,
    a03BFactor_swap_last c d a b]

theorem a03ZArithmetic_swap_last (a b c d : ℂ) (m n : ℕ) :
    bblrZArithmetic a b c d m n=bblrZArithmetic a b d c m n := by
  unfold bblrZArithmetic
  rw [a03AArithmetic_swap_last a b c d,a03BFactor_swap_last a b c d,
    a03BFactor_swap_first c d a b]

def a03CrossedChamberLabel (m n : Bool) : Fin 6 :=
  if m then (if n then 2 else 3) else (if n then 4 else 5)

def a03CrossedTuple (α : MomentShifts) : MomentShifts :=
  ![α 0,-α 3,α 2,-α 1]

theorem a03CrossedChamber_phase (m n : Bool) (α : MomentShifts) :
    -(a03ZeroModeChamberShifts m n α 1)-(a03ZeroModeChamberShifts m n α 3)=
      bblrSixPhaseExponents α (a03CrossedChamberLabel m n) := by
  cases m <;> cases n <;>
    simp [a03ZeroModeChamberShifts,a03ZeroModePairPermutation,a03CrossedChamberLabel,
      bblrSixPhaseExponents]

theorem a03CrossedChamber_ZArithmetic (m n : Bool) (α : MomentShifts) (a b : ℕ) :
    bblrZArithmetic (a03CrossedTuple (a03ZeroModeChamberShifts m n α) 0)
      (a03CrossedTuple (a03ZeroModeChamberShifts m n α) 1)
      (a03CrossedTuple (a03ZeroModeChamberShifts m n α) 2)
      (a03CrossedTuple (a03ZeroModeChamberShifts m n α) 3) a b=
    bblrZArithmetic (bblrSixShifts α (a03CrossedChamberLabel m n) 0)
      (bblrSixShifts α (a03CrossedChamberLabel m n) 1)
      (bblrSixShifts α (a03CrossedChamberLabel m n) 2)
      (bblrSixShifts α (a03CrossedChamberLabel m n) 3) a b := by
  cases m <;> cases n
  · rfl
  · exact a03ZArithmetic_swap_last _ _ _ _ a b
  · exact a03ZArithmetic_swap_first _ _ _ _ a b
  · change bblrZArithmetic (α 1) (-α 2) (α 3) (-α 0) a b=
      bblrZArithmetic (-α 2) (α 1) (-α 0) (α 3) a b
    rw [a03ZArithmetic_swap_first (α 1) (-α 2) (α 3) (-α 0),
      a03ZArithmetic_swap_last (-α 2) (α 1) (α 3) (-α 0)]

theorem a03CrossedChamber_nativeArithmetic (m n : Bool) (α : MomentShifts) (a b : ℕ) :
    a03DiagonalNativeArithmetic (a03CrossedTuple (a03ZeroModeChamberShifts m n α)) a b=
      a03DiagonalNativeArithmetic (bblrSixShifts α (a03CrossedChamberLabel m n)) a b := by
  unfold a03DiagonalNativeArithmetic
  rw [a03CrossedChamber_ZArithmetic]

theorem a03CrossedArithmeticSum_eq_native (N₁ N₂ : ℕ) (A B : ℕ→ℂ) (α : MomentShifts) :
    a03CrossedArithmeticSum N₁ N₂ A B α=
      ∑ m∈Finset.Icc 1 N₁,∑ n∈Finset.Icc 1 N₂,
        A m*B n*a03DiagonalNativeArithmetic (a03CrossedTuple α) m n := by
  unfold a03CrossedArithmeticSum
  rw [a03FiniteAmplifier_gcd_reindex]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  have hmexact := Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
  have hnexact := Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)
  rw [congrArg A hmexact,congrArg B hnexact]
  change A m*B n/(((Nat.gcd m n)*(m/Nat.gcd m n)*(n/Nat.gcd m n):ℕ):ℂ)*
      bblrZArithmetic (α 0) (-α 3) (α 2) (-α 1) (m/Nat.gcd m n) (n/Nat.gcd m n)=
    A m*B n*(((Nat.gcd m n:ℕ):ℂ)^(-1:ℂ)*
      (((m/Nat.gcd m n)*(n/Nat.gcd m n):ℕ):ℂ)^(-1:ℂ)*
      bblrZArithmetic (α 0) (-α 3) (α 2) (-α 1) (m/Nat.gcd m n) (n/Nat.gcd m n))
  simp only [Complex.cpow_neg_one,Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
  ring


def a03CrossedChamberArithmeticMoment (m n : Bool) (T a b : ℝ)
    (α : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  ∫ t : ℝ,(Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^
      (-(a03ZeroModeChamberShifts m n α 1)-(a03ZeroModeChamberShifts m n α 3))*
    a03CrossedArithmeticSum ⌊T^a⌋₊ ⌊T^b⌋₊
      (fun k : ℕ => (f (Real.log k/Real.log T):ℂ))
      (fun k : ℕ => (g (Real.log k/Real.log T):ℂ)) (a03ZeroModeChamberShifts m n α)

theorem a03CrossedChamberArithmeticMoment_eq_indexed (m n : Bool) (T a b : ℝ)
    (α : MomentShifts) (f g Φ : ℝ→ℝ) :
    a03CrossedChamberArithmeticMoment m n T a b α f g Φ=
      a03DiagonalArithmeticIndexedMainTerm (a03CrossedChamberLabel m n) T a b α f g Φ := by
  unfold a03CrossedChamberArithmeticMoment
  rw [a03CrossedChamber_phase,integral_mul_const,a03CrossedArithmeticSum_eq_native]
  simp_rw [a03CrossedChamber_nativeArithmetic,Finset.mul_sum]
  unfold a03DiagonalArithmeticIndexedMainTerm
  simp_rw [integral_mul_const]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem a03CrossedChamberArithmeticMoment_integrable {T : ℝ} (hT : 0<T)
    (m n : Bool) (a b : ℝ) (α : MomentShifts) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t : ℝ => (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^
      (-(a03ZeroModeChamberShifts m n α 1)-(a03ZeroModeChamberShifts m n α 3))*
      a03CrossedArithmeticSum ⌊T^a⌋₊ ⌊T^b⌋₊
        (fun k : ℕ => (f (Real.log k/Real.log T):ℂ))
        (fun k : ℕ => (g (Real.log k/Real.log T):ℂ)) (a03ZeroModeChamberShifts m n α)) :=
  (a03DyadicPhase_integrable hT Φ hΦ _).mul_const _

theorem a03ArithmeticSixMainTerms_eq_diagonal_and_chambers (T a b : ℝ)
    (α : MomentShifts) (f g Φ : ℝ→ℝ) :
    a03DiagonalArithmeticSixMainTerms T a b α f g Φ=
      a03DiagonalArithmeticIndexedMainTerm 0 T a b α f g Φ+
        a03DiagonalArithmeticIndexedMainTerm 1 T a b α f g Φ+
          ∑ m : Bool,∑ n : Bool,a03CrossedChamberArithmeticMoment m n T a b α f g Φ := by
  simp_rw [a03CrossedChamberArithmeticMoment_eq_indexed]
  simp only [Fintype.sum_bool,a03CrossedChamberLabel,Bool.false_eq_true,ite_false,ite_true]
  unfold a03DiagonalArithmeticSixMainTerms
  simp only [Fin.sum_univ_succ]
  norm_num
  ring

end
end Sechstmoment
