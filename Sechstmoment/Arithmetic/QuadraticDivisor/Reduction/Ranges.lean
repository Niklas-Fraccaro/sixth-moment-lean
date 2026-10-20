import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Sechstmoment.Arithmetic.QuadraticDivisor.Reduction.Shifts
import Std

namespace DivisorProof
open MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1600000

def extendedQuadraticBound (q : QuadraticScales) (j : Fin 7) : ℕ :=
  if j = 5 then max ⌊2*q.size j⌋₊ ⌊8*(q.A*q.M)+2*q.H⌋₊ else ⌊2*q.size j⌋₊

def extendedQuadraticIndexSet (q : QuadraticScales) : Finset (Fin 7 → ℕ) :=
  Fintype.piFinset fun j => Finset.Icc 1 (extendedQuadraticBound q j)

theorem quadraticIndexSet_subset_extended (q : QuadraticScales) :
    quadraticIndexSet q ⊆ extendedQuadraticIndexSet q := by
  intro n hn
  apply Fintype.mem_piFinset.mpr
  intro j
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn j)
  refine Finset.mem_Icc.mpr ⟨hlo, hhi.trans ?_⟩
  unfold extendedQuadraticBound
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem extendedQuadraticIndexSet_pos {q : QuadraticScales} {n : Fin 7 → ℕ}
    (hn : n ∈ extendedQuadraticIndexSet q) (j : Fin 7) : 0 < n j :=
  (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn j)).1

theorem extendedQuadraticIndexSet_upper {q : QuadraticScales}
    (h : ∀ j, 1 ≤ q.size j) {n : Fin 7 → ℕ}
    (hn : n ∈ extendedQuadraticIndexSet q) {j : Fin 7} (hj : j ≠ 5) :
    (n j : ℝ) ≤ 2*q.size j := by
  have hhi := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn j)).2
  simp only [extendedQuadraticBound, ite_eq_right hj] at hhi
  exact (show (n j : ℝ) ≤ (⌊2*q.size j⌋₊ : ℝ) by exact_mod_cast hhi).trans
    (Nat.floor_le (by linarith [h j]))

theorem dyadic_weight_argument_bounds {W : ℝ → ℝ} (hW : SmoothDyadicWeight W)
    {X x : ℝ} (hX : 0 < X) (hx : W (x/X) ≠ 0) : X ≤ x ∧ x ≤ 2*X := by
  have hs := hW.2 (subset_tsupport W hx)
  exact ⟨by simpa only [one_mul] using (le_div_iff₀ hX).mp hs.1,
    (div_le_iff₀ hX).mp hs.2⟩

theorem quadraticSummand_zero_on_extension (q : QuadraticScales)
    (h : ∀ j, 1 ≤ q.size j) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ)
    (h₄ : SmoothDyadicWeight (W 4)) {n : Fin 7 → ℕ}
    (hn : n ∈ extendedQuadraticIndexSet q) (hnot : n ∉ quadraticIndexSet q) :
    quadraticSummand q α β W n = 0 := by
  have hz : W 4 ((n 5 : ℝ)/q.N₂) = 0 := by
    by_contra hne
    have hN₂ : 0 < q.N₂ := lt_of_lt_of_le (by norm_num) (h 5)
    have hhi := (dyadic_weight_argument_bounds h₄ hN₂ hne).2
    apply hnot
    apply Fintype.mem_piFinset.mpr
    intro j
    refine Finset.mem_Icc.mpr ⟨extendedQuadraticIndexSet_pos hn j, ?_⟩
    apply (Nat.le_floor_iff (by linarith [h j] : 0 ≤ 2*q.size j)).mpr
    by_cases hj : j = 5
    · subst j
      exact hhi
    · exact extendedQuadraticIndexSet_upper h hn hj
  simp [quadraticSummand, hz]

theorem quadraticSum_eq_extended (positive : Bool) (q : QuadraticScales)
    (h : ∀ j, 1 ≤ q.size j) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ)
    (h₄ : SmoothDyadicWeight (W 4)) :
    signedQuadraticSum positive q α β W =
      ∑ n ∈ extendedQuadraticIndexSet q,
        if signedQuadraticRelation positive n then quadraticSummand q α β W n else 0 := by
  apply Finset.sum_subset (quadraticIndexSet_subset_extended q)
  intro n hn hnot
  rw [quadraticSummand_zero_on_extension q h α β W h₄ hn hnot]
  split_ifs <;> rfl

def extendedActiveIndexSet (positive : Bool) (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) : Finset (Fin 7 → ℕ) :=
  (extendedQuadraticIndexSet q).filter (fun n => signedQuadraticRelation positive n ∧
    quadraticPreWeight q α β W n ≠ 0)

def shiftRemovedExtendedSum (positive : Bool) (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) : ℂ :=
  ∑ n ∈ extendedActiveIndexSet positive q α β W, quadraticPreWeight q α β W n *
    (W 4 ((n 0 : ℝ)*n 2*n 3/((n 1 : ℝ)*n 4*q.N₂)) : ℂ)

theorem quadraticSum_eq_extended_active (positive : Bool) (q : QuadraticScales)
    (h : ∀ j, 1 ≤ q.size j) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ)
    (h₄ : SmoothDyadicWeight (W 4)) :
    signedQuadraticSum positive q α β W =
      ∑ n ∈ extendedActiveIndexSet positive q α β W,
        quadraticPreWeight q α β W n*(W 4 (n 5/q.N₂) : ℂ) := by
  rw [quadraticSum_eq_extended positive q h α β W h₄]
  unfold extendedActiveIndexSet
  rw [sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hrel : signedQuadraticRelation positive n
  · by_cases hw : quadraticPreWeight q α β W n = 0
    · simp only [hrel, hw, ne_eq, not_true_eq_false, and_false, ite_true, ite_false]
      change quadraticPreWeight q α β W n*(W 4 (n 5/q.N₂) : ℂ) = 0
      rw [hw, zero_mul]
    · simp only [hrel, hw, ne_eq, not_false_eq_true, and_self, ite_true]
      rfl
  · simp only [hrel, false_and, ite_false]

theorem actual_extended_weight_shift_error {ρ K b₀ b₁ : ℝ}
    (hρ : 0 < ρ) (hK : 1 ≤ K) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (positive : Bool) (q : QuadraticScales)
      (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
      (∀ j, 1 ≤ q.size j) → q.H ≤ K*q.mass → q.A*q.M ≤ K*q.B*q.N →
      (∀ n : ℕ, (n : ℝ) ∉ Icc q.B (2*q.B) → β n = 0) →
      (∀ n, ‖α n‖ ≤ 1) → (∀ n, ‖β n‖ ≤ 1) →
      (∀ i, SmoothDyadicWeight (W i)) → (∀ i x, ‖W i x‖ ≤ b₀) →
      (∀ x, ‖iteratedDeriv 1 (W 4) x‖ ≤ b₁) →
      ‖signedQuadraticSum positive q α β W-shiftRemovedExtendedSum positive q α β W‖ ≤
        C*q.mass^(2*ρ)*q.H^2 := by
  obtain ⟨C, hC, hc⟩ := summed_weight_shift_error (P := b₀^4) (b := b₁) hρ
    (by linarith : 0 ≤ K) (by positivity) hb₁
  refine ⟨C, hC, ?_⟩
  intro positive q α β W h hH hbalance hsupp hα hβ hW hWnorm hder
  let s := extendedActiveIndexSet positive q α β W
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hM₁ : 0 < q.M₁ := lt_of_lt_of_le (by norm_num) (h 2)
  have hM₂ : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hN₁ : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (h 4)
  have hN₂ : 0 < q.N₂ := lt_of_lt_of_le (by norm_num) (h 5)
  have hH0 : 0 ≤ q.H := zero_le_one.trans (h 6)
  have hQ := (poisson_scale_bounds q h).1
  have hU : 0 < q.A*q.M := by dsimp [QuadraticScales.M]; positivity
  have hV : 0 < q.B*q.N := by dsimp [QuadraticScales.N]; positivity
  have hN : 1 ≤ q.B*q.N := by
    dsimp [QuadraticScales.N]
    exact one_le_mul_of_one_le_of_one_le (h 1) (one_le_mul_of_one_le_of_one_le (h 4) (h 5))
  have hUQ : q.A*q.M ≤ q.mass := by
    rw [mass_eq_balanced_product]
    exact le_mul_of_one_le_right hU.le hN
  have hnset {n} (hn : n ∈ s) : n ∈ extendedQuadraticIndexSet q := (mem_filter.mp hn).1
  have hpos : ∀ n ∈ s, ∀ j, 0 < n j := fun n hn j =>
    extendedQuadraticIndexSet_pos (hnset hn) j
  have hrel : ∀ n ∈ s, signedQuadraticRelation positive n := fun _ hn =>
    (mem_filter.mp hn).2.1
  have hleft (n) (hn : n ∈ s) : (n 0 : ℝ)*n 2*n 3 ≤ 8*(q.A*q.M) := by
    have h₀ : (n 0 : ℝ) ≤ 2*q.A := extendedQuadraticIndexSet_upper h (hnset hn) (j := 0) (by decide)
    have h₂ : (n 2 : ℝ) ≤ 2*q.M₁ := extendedQuadraticIndexSet_upper h (hnset hn) (j := 2) (by decide)
    have h₃ : (n 3 : ℝ) ≤ 2*q.M₂ := extendedQuadraticIndexSet_upper h (hnset hn) (j := 3) (by decide)
    calc _ ≤ (2*q.A)*(2*q.M₁)*(2*q.M₂) := by gcongr
      _ = _ := by dsimp [QuadraticScales.M]; ring
  have hshift (n) (hn : n ∈ s) : (n 6 : ℝ) ≤ 2*q.H :=
    extendedQuadraticIndexSet_upper h (hnset hn) (j := 6) (by decide)
  have hden (n) (hn : n ∈ s) : q.B*q.N ≤ (n 1 : ℝ)*n 4*q.N₂ := by
    have hpre := (mem_filter.mp hn).2.2
    have hβne : β (n 1) ≠ 0 := by
      intro hz
      exact hpre (by simp [quadraticPreWeight, hz])
    have hβsupport : (n 1 : ℝ) ∈ Icc q.B (2*q.B) := by
      by_contra hn
      exact hβne (hsupp _ hn)
    have h₃ne : W 3 ((n 4 : ℝ)/q.N₁) ≠ 0 := by
      intro hz
      exact hpre (by simp [quadraticPreWeight, hz])
    have h₃support := (hW 3).2 (subset_tsupport (W 3) h₃ne)
    have h₄lower : q.N₁ ≤ (n 4 : ℝ) := by
      simpa only [one_mul] using (le_div_iff₀ hN₁).mp h₃support.1
    calc q.B*q.N = (q.B*q.N₁)*q.N₂ := by dsimp [QuadraticScales.N]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hβsupport.1 h₄lower hN₁.le (Nat.cast_nonneg _)) hN₂.le
  have hbound := hc s positive (q.A*q.M) q.H q.mass q.N₂ (q.B*q.N) (W 4)
    (quadraticPreWeight q α β W) hU hH0 (by linarith) hN₂ hV hUQ hH
    (by simpa only [mul_assoc] using hbalance) (hW 4) hder hpos hrel hleft hshift hden
    (fun n _ => quadraticPreWeight_norm_le q α β W hb₀ hα hβ hWnorm n)
  rw [quadraticSum_eq_extended_active positive q h α β W (hW 4),
    shiftRemovedExtendedSum, ← sum_sub_distrib]
  simpa only [s, mul_sub] using hbound


end
end DivisorProof



namespace DivisorProof
open Finset Classical
open scoped BigOperators
noncomputable section

def splitLeft (a d : ℕ) : ℕ := Nat.gcd a d
def splitRight (a d : ℕ) : ℕ := d / splitLeft a d
def splitCoefficient (a d : ℕ) : ℕ := a / splitLeft a d
def splitInner (a m d : ℕ) : ℕ := m / splitRight a d

theorem splitLeft_pos (a : ℕ) {d : ℕ} (hd : 0 < d) : 0 < splitLeft a d :=
  Nat.gcd_pos_of_pos_right a hd

theorem splitLeft_dvd (a d : ℕ) : splitLeft a d ∣ d := Nat.gcd_dvd_right a d

theorem split_factors_mul (a d : ℕ) : splitLeft a d * splitRight a d = d :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right a d)

theorem split_coefficient_mul (a d : ℕ) :
    splitLeft a d * splitCoefficient a d = a :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left a d)

theorem splitRight_pos (a : ℕ) {d : ℕ} (hd : 0 < d) : 0 < splitRight a d :=
  reduced_modulus_pos a d hd

theorem split_coprime (a : ℕ) {d : ℕ} (hd : 0 < d) :
    (splitCoefficient a d).Coprime (splitRight a d) :=
  reduced_coefficients_coprime a d hd

theorem splitRight_dvd_inner {a m d : ℕ} (hd : 0 < d) (hdiv : d ∣ a*m) :
    splitRight a d ∣ m := by
  have he : splitLeft a d * splitRight a d ∣
      splitLeft a d * (splitCoefficient a d*m) := by
    simpa only [← mul_assoc, split_factors_mul, split_coefficient_mul] using hdiv
  exact (split_coprime a hd).symm.dvd_of_dvd_mul_left
    (Nat.dvd_of_mul_dvd_mul_left (splitLeft_pos a hd) he)

theorem split_inner_mul {a m d : ℕ} (hd : 0 < d) (hdiv : d ∣ a*m) :
    splitRight a d * splitInner a m d = m :=
  Nat.mul_div_cancel' (splitRight_dvd_inner hd hdiv)

theorem split_product {a m d : ℕ} (hd : 0 < d) (hdiv : d ∣ a*m) :
    a*m = d*(splitCoefficient a d*splitInner a m d) := by
  calc a*m = (splitLeft a d*splitCoefficient a d)*
      (splitRight a d*splitInner a m d) := by
        rw [split_coefficient_mul, split_inner_mul hd hdiv]
    _ = (splitLeft a d*splitRight a d)*
        (splitCoefficient a d*splitInner a m d) := by ring
    _ = _ := by rw [split_factors_mul]

theorem split_factors_le (a : ℕ) {d : ℕ} (hd : 0 < d) :
    splitLeft a d ≤ d ∧ splitRight a d ≤ d := by
  exact ⟨Nat.le_of_dvd hd (splitLeft_dvd a d), Nat.div_le_self _ _⟩

theorem splitLeft_unique {a d e f r : ℕ} (ha : a = e*r) (hd : d = e*f)
    (hcop : r.Coprime f) : splitLeft a d = e := by
  simp only [splitLeft, ha, hd, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]

theorem split_decomposition_unique {a m d e f r v : ℕ} (hd : 0 < d)
    (ha : a = e*r) (hdf : d = e*f) (hm : m = f*v) (hcop : r.Coprime f) :
    splitLeft a d = e ∧ splitRight a d = f ∧
      splitCoefficient a d = r ∧ splitInner a m d = v := by
  have he : 0 < e := by nlinarith
  have hf : 0 < f := by nlinarith
  have hleft := splitLeft_unique ha hdf hcop
  have hright : splitRight a d = f := by
    unfold splitRight
    rw [hleft, hdf, Nat.mul_div_cancel_left _ he]
  refine ⟨hleft, hright, ?_, ?_⟩
  · unfold splitCoefficient
    rw [hleft, ha, Nat.mul_div_cancel_left _ he]
  · unfold splitInner
    rw [hright, hm, Nat.mul_div_cancel_left _ hf]

theorem split_residual_coprime {a m b n : ℕ} (hb : 0 < b*n) :
    let d := Nat.gcd (a*m) (b*n)
    (splitCoefficient a d*splitInner a m d).Coprime
      (splitCoefficient b d*splitInner b n d) := by
  dsimp only
  let d := Nat.gcd (a*m) (b*n)
  have hd : 0 < d := Nat.gcd_pos_of_pos_right _ hb
  have ha := split_product hd (Nat.gcd_dvd_left (a*m) (b*n))
  have hb' := split_product hd (Nat.gcd_dvd_right (a*m) (b*n))
  have hg : d = d*Nat.gcd (splitCoefficient a d*splitInner a m d)
      (splitCoefficient b d*splitInner b n d) := by
    change Nat.gcd (a*m) (b*n) = _
    rw [ha, hb', Nat.gcd_mul_left]
  change Nat.gcd _ _ = 1
  exact Nat.eq_of_mul_eq_mul_left hd (by simpa using hg.symm)

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1600000

def outerLeft (n : Fin 5 → ℕ) : ℕ := n 0*n 2
def outerRight (n : Fin 5 → ℕ) : ℕ := n 1*n 3
def outerGCD (n : Fin 5 → ℕ) : ℕ := Nat.gcd (outerLeft n) (outerRight n)
def signedShift (positive : Bool) (k : ℕ) : ℤ :=
  if positive then (k : ℤ) else -(k : ℤ)

def poissonOuterWeight (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) (n : Fin 5 → ℕ) : ℂ :=
  α (n 0)*β (n 1)*(W 0 ((outerGCD n : ℝ)*n 4/q.H) : ℂ)*
    (W 1 (n 2/q.M₁) : ℂ)*(W 3 (n 3/q.N₁) : ℂ)

def outerPoissonProfile (q : QuadraticScales) (W : Fin 5 → ℝ → ℝ)
    (n : Fin 5 → ℕ) : ℝ → ℂ :=
  poissonProfile (W 2) (W 4)
    ((outerRight n : ℝ)/((outerGCD n : ℝ)*q.M₂))
    ((outerLeft n : ℝ)/((outerGCD n : ℝ)*q.N₂))

def outerPoissonPhase (positive : Bool) (n : Fin 5 → ℕ) : ℝ :=
  (signedShift positive (n 4) : ℝ)*
    (inverseRepresentative (outerLeft n/outerGCD n) (outerRight n/outerGCD n) : ℝ)/
      ((outerRight n/outerGCD n : ℕ) : ℝ)

def outerFourierIntegrand (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (W : Fin 5 → ℝ → ℝ) (n : Fin 5 → ℕ) (x : ℝ) : ℂ :=
  outerPoissonProfile q W n x * finitePoissonKernel
    (poissonLength q ρ (outerGCD n : ℝ)) (outerPoissonPhase positive n) x

def shiftRemovedReducedSum (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) : ℂ :=
  ∑ n ∈ quadraticMainIndexSet q, poissonOuterWeight q α β W n *
    reducedEquationSum (W 2) (W 4) (outerLeft n) (outerRight n)
      q.M₂ q.N₂ (signedShift positive (n 4))

def finitePoissonNormalSum (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) : ℂ :=
  ∑ n ∈ quadraticMainIndexSet q, poissonOuterWeight q α β W n *
    ∫ x : ℝ in Ioi 0, outerFourierIntegrand positive q ρ W n x

theorem quadraticMainIndexSet_coordinate_bounds (q : QuadraticScales)
    (h : ∀ j, 1 ≤ q.size j) {n : Fin 5 → ℕ} (hn : n ∈ quadraticMainIndexSet q)
    (j : Fin 5) : 0 < n j ∧
      (n j : ℝ) ≤ 2*(![q.A,q.B,q.M₁,q.N₁,q.H] : Fin 5 → ℝ) j := by
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn j)
  have hs : 0 ≤ (![q.A,q.B,q.M₁,q.N₁,q.H] : Fin 5 → ℝ) j := by
    fin_cases j
    · exact zero_le_one.trans (h 0)
    · exact zero_le_one.trans (h 1)
    · exact zero_le_one.trans (h 2)
    · exact zero_le_one.trans (h 4)
    · exact zero_le_one.trans (h 6)
  exact ⟨hlo, (show (n j : ℝ) ≤ (⌊2*(![q.A,q.B,q.M₁,q.N₁,q.H] : Fin 5 → ℝ) j⌋₊ : ℝ)
    by exact_mod_cast hhi).trans (Nat.floor_le (by positivity))⟩

theorem outerRight_pos {q : QuadraticScales} {n : Fin 5 → ℕ}
    (hn : n ∈ quadraticMainIndexSet q) : 0 < outerRight n := by
  exact Nat.mul_pos (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn 1)).1
    (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn 3)).1

theorem outerGCD_pos {q : QuadraticScales} {n : Fin 5 → ℕ}
    (hn : n ∈ quadraticMainIndexSet q) : 0 < outerGCD n :=
  Nat.gcd_pos_of_pos_right _ (outerRight_pos hn)

theorem outerPoissonProfile_eq (q : QuadraticScales) (W : Fin 5 → ℝ → ℝ)
    (n : Fin 5 → ℕ) (x : ℝ) :
    outerPoissonProfile q W n x =
      (W 2 ((n 1 : ℝ)*n 3*x/((outerGCD n : ℝ)*q.M₂)) : ℂ)*
      (W 4 ((n 0 : ℝ)*n 2*x/((outerGCD n : ℝ)*q.N₂)) : ℂ) := by
  simp only [outerPoissonProfile,poissonProfile,outerLeft,outerRight,Nat.cast_mul,
    div_mul_eq_mul_div]

theorem zeroModeSummand_eq_outer (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) (n : Fin 5 → ℕ) :
    quadraticZeroModeSummand q α β W n =
      poissonOuterWeight q α β W n * ∫ x : ℝ in Ioi 0, outerPoissonProfile q W n x := by
  simp_rw [outerPoissonProfile_eq]
  rfl

theorem poissonOuterWeight_norm_le (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) {b₀ : ℝ} (hb₀ : 0 ≤ b₀)
    (hα : ∀ n, ‖α n‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1)
    (hW : ∀ i x, ‖W i x‖ ≤ b₀) (n : Fin 5 → ℕ) :
    ‖poissonOuterWeight q α β W n‖ ≤ b₀^3 := by
  unfold poissonOuterWeight
  simp only [norm_mul, Complex.norm_real]
  calc _ ≤ 1*1*b₀*b₀*b₀ := by
         gcongr
         · exact hα _
         · exact hβ _
         · exact hW _ _
         · exact hW _ _
         · exact hW _ _
    _ = _ := by ring

theorem outer_products_bounds {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ} (h : ∀ j, 1 ≤ q.size j)
    (hw : NormalizedWeightData bounds q α β W) {n : Fin 5 → ℕ}
    (hn : n ∈ quadraticMainIndexSet q) (hne : poissonOuterWeight q α β W n ≠ 0) :
    (outerLeft n : ℝ) ≤ 4*q.A*q.M₁ ∧
      q.B*q.N₁ ≤ (outerRight n : ℝ) ∧ (outerRight n : ℝ) ≤ 4*q.B*q.N₁ := by
  have hβne : β (n 1) ≠ 0 := by
    intro hz
    exact hne (by simp [poissonOuterWeight, hz])
  have hβlo : q.B ≤ (n 1 : ℝ) := by
    by_contra hh
    exact hβne (hw.beta_support _ (fun hc => hh hc.1))
  have h₃ne : W 3 ((n 3 : ℝ)/q.N₁) ≠ 0 := by
    intro hz
    exact hne (by simp [poissonOuterWeight, hz])
  have hN₁ : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (h 4)
  have hNlo := (dyadic_weight_argument_bounds (hw.smooth 3) hN₁ h₃ne).1
  have h₀ : (n 0 : ℝ) ≤ 2*q.A := (quadraticMainIndexSet_coordinate_bounds q h hn 0).2
  have h₁ : (n 1 : ℝ) ≤ 2*q.B := (quadraticMainIndexSet_coordinate_bounds q h hn 1).2
  have h₂ : (n 2 : ℝ) ≤ 2*q.M₁ := (quadraticMainIndexSet_coordinate_bounds q h hn 2).2
  have h₃ : (n 3 : ℝ) ≤ 2*q.N₁ := (quadraticMainIndexSet_coordinate_bounds q h hn 3).2
  simp only [outerLeft,outerRight,Nat.cast_mul]
  refine ⟨?_, mul_le_mul hβlo hNlo (by linarith) (Nat.cast_nonneg _), ?_⟩
  · calc _ ≤ (2*q.A)*(2*q.M₁) := by gcongr; linarith [h 0]
      _ = _ := by ring
  · calc _ ≤ (2*q.B)*(2*q.N₁) := by gcongr; linarith [h 1]
      _ = _ := by ring

def poissonRemainderConstant (bounds : ℕ → ℝ) (K ρ : ℝ) : ℝ :=
  2*profileFourierBound bounds (4*K) (truncationOrder ρ+2)*
    K^(truncationOrder ρ)*inverseSquareMass

theorem poissonRemainderConstant_nonneg {bounds : ℕ → ℝ} {K ρ : ℝ}
    (hb : ∀ j, 0 ≤ bounds j) (hK : 0 ≤ K) :
    0 ≤ poissonRemainderConstant bounds K ρ := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (profileFourierBound_nonneg hb (by positivity) _)) (pow_nonneg hK _))
    inverseSquareMass_nonneg

theorem summed_actual_poisson_error {K ρ : ℝ} (hK : 1 ≤ K) (hρ : 0 < ρ)
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (hH : q.H ≤ K*q.mass) (hbal₁ : q.A*q.M ≤ K*q.B*q.N)
    (hbal₂ : q.B*q.N ≤ K*q.A*q.M) (positive : Bool) :
    ‖(shiftRemovedReducedSum positive q α β W-quadraticZeroMode q α β W)-
        finitePoissonNormalSum positive q ρ α β W‖ ≤
      (32*K*(bounds 0)^3*poissonRemainderConstant bounds K ρ)/q.mass^7 := by
  let err := fun n : Fin 5 → ℕ => poissonOuterWeight q α β W n *
    ((reducedEquationSum (W 2) (W 4) (outerLeft n) (outerRight n)
      q.M₂ q.N₂ (signedShift positive (n 4)) -
        ∫ x : ℝ in Ioi 0, outerPoissonProfile q W n x) -
      ∫ x : ℝ in Ioi 0, outerFourierIntegrand positive q ρ W n x)
  have hC := poissonRemainderConstant_nonneg (ρ := ρ) (hw.bounds_nonneg) (by linarith : 0 ≤ K)
  have hb₀ := hw.bounds_nonneg 0
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have he (n) (hn : n ∈ quadraticMainIndexSet q) :
      ‖err n‖ ≤ ((bounds 0)^3*poissonRemainderConstant bounds K ρ)/q.mass^9 := by
    by_cases hz : poissonOuterWeight q α β W n = 0
    · simp only [err, hz, zero_mul, norm_zero]
      positivity
    · obtain ⟨hX,hY,hY'⟩ := outer_products_bounds h hw hn hz
      have hp := finite_poisson_actual_inner (hw.smooth 2) (hw.smooth 4) q h
        (outerLeft n) (outerRight n) (outerRight_pos hn) hK hρ hX hY hY' hbal₁ hbal₂
        (fun j x => hw.derivatives j 2 x) (fun j x => hw.derivatives j 4 x)
        (signedShift positive (n 4))
      change ‖_‖ ≤ poissonRemainderConstant bounds K ρ/q.mass^9 at hp
      change ‖poissonOuterWeight q α β W n * _‖ ≤ _
      rw [norm_mul]
      calc _ ≤ (bounds 0)^3*(poissonRemainderConstant bounds K ρ/q.mass^9) :=
          mul_le_mul (poissonOuterWeight_norm_le q α β W hb₀ hw.alpha_bound hw.beta_bound
            hw.weight_norm n) hp (norm_nonneg _) (by positivity)
        _ = _ := by ring
  have hs := sum_truncation_budget (quadraticMainIndexSet q) err
    (poisson_scale_bounds q h).1 (by positivity : 0 ≤ 32*K) (by positivity)
    (quadraticMainIndexSet_card_le_mass_sq q h hH) he
  convert hs using 1
  · congr 1
    unfold shiftRemovedReducedSum quadraticZeroMode finitePoissonNormalSum
    simp_rw [zeroModeSummand_eq_outer]
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    dsimp only [err]
    ring
  · ring

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def spatialIndexSet (M : ℝ) : Finset ℕ := Icc 1 ⌊2*M⌋₊

theorem reducedEquationSum_eq_finite {W₂ W₄ : ℝ → ℝ}
    (h₂ : SmoothDyadicWeight W₂) (A B : ℕ) {M N : ℝ} (hM : 0 < M) (k : ℤ) :
    reducedEquationSum W₂ W₄ A B M N k =
      ∑ m ∈ spatialIndexSet M, reducedEquationTerm W₂ W₄ A B M N k (m : ℤ) := by
  let s : Finset ℤ := (spatialIndexSet M).image (fun m : ℕ => (m : ℤ))
  have hout (m : ℤ) (hm : m ∉ s) : reducedEquationTerm W₂ W₄ A B M N k m = 0 := by
    have hz : W₂ ((m : ℝ)/M) = 0 := by
      by_contra hne
      obtain ⟨hlo,hhi⟩ := dyadic_weight_argument_bounds h₂ hM hne
      have hmp : (0 : ℝ) < m := hM.trans_le hlo
      have hmi : (0 : ℤ) < m := by exact_mod_cast hmp
      have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmi.le
      apply hm
      apply Finset.mem_image.mpr
      refine ⟨m.toNat, Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hmn⟩
      apply (Nat.le_floor_iff (by positivity : 0 ≤ 2*M)).mpr
      have hmreal : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast hmn
      rwa [hmreal]
    simp [reducedEquationTerm,hz]
  rw [reducedEquationSum, tsum_eq_sum hout]
  dsimp only [s]
  rw [sum_image]
  intro a _ b _ hab
  change (a : ℤ) = (b : ℤ) at hab
  exact_mod_cast hab

def poissonPairIndexSet (q : QuadraticScales) : Finset ((Fin 5 → ℕ) × ℕ) :=
  (quadraticMainIndexSet q) ×ˢ spatialIndexSet q.M₂

def poissonPairSummand (positive : Bool) (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) (p : (Fin 5 → ℕ) × ℕ) : ℂ :=
  poissonOuterWeight q α β W p.1 * reducedEquationTerm (W 2) (W 4)
    (outerLeft p.1) (outerRight p.1) q.M₂ q.N₂ (signedShift positive (p.1 4)) (p.2 : ℤ)

theorem shiftRemovedReducedSum_eq_pairs (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (h₂ : SmoothDyadicWeight (W 2))
    (hM : 0 < q.M₂) :
    shiftRemovedReducedSum positive q α β W =
      ∑ p ∈ poissonPairIndexSet q, poissonPairSummand positive q α β W p := by
  unfold shiftRemovedReducedSum poissonPairIndexSet
  rw [sum_product]
  apply sum_congr rfl
  intro n _
  rw [reducedEquationSum_eq_finite h₂ _ _ hM, mul_sum]
  rfl

theorem equation_partner_unique (A B : ℕ) (hB : 0 < B) (m k n n' : ℤ)
    (hn : (A : ℤ)*m-(B : ℤ)*n = k) (hn' : (A : ℤ)*m-(B : ℤ)*n' = k) : n = n' := by
  have hBz : (B : ℤ) ≠ 0 := by exact_mod_cast hB.ne'
  exact (mul_left_cancel₀ hBz) (by linarith)

theorem signedShift_mul (positive : Bool) (d k : ℕ) :
    signedShift positive (d*k) = (d : ℤ)*signedShift positive k := by
  cases positive <;> simp [signedShift]

theorem signedShift_natAbs (positive : Bool) (k : ℕ) :
    (signedShift positive k).natAbs = k := by
  cases positive <;> simp [signedShift]

def extendedToPair (n : Fin 7 → ℕ) : (Fin 5 → ℕ) × ℕ :=
  (![n 0,n 1,n 2,n 4,n 6/Nat.gcd (n 0*n 2) (n 1*n 4)], n 3)

theorem signed_relation_as_equation (positive : Bool) {n : Fin 7 → ℕ}
    (hrel : signedQuadraticRelation positive n) :
    ((n 0*n 2 : ℕ) : ℤ)*(n 3 : ℤ)-((n 1*n 4 : ℕ) : ℤ)*(n 5 : ℤ) =
      signedShift positive (n 6) := by
  simpa only [Nat.cast_mul,signedShift,signedQuadraticRelation] using hrel

theorem signed_relation_gcd_dvd (positive : Bool) {n : Fin 7 → ℕ}
    (hrel : signedQuadraticRelation positive n) : Nat.gcd (n 0*n 2) (n 1*n 4) ∣ n 6 := by
  exact gcd_dvd_signed_shift (n 0*n 2) (n 1*n 4) (n 6) (n 3) (n 5) positive
    (by simpa only [Nat.cast_mul,signedQuadraticRelation] using hrel)

theorem extendedToPair_mem (positive : Bool) {q : QuadraticScales}
    (_h : ∀ j, 1 ≤ q.size j) {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    {n : Fin 7 → ℕ} (hn : n ∈ extendedActiveIndexSet positive q α β W) :
    extendedToPair n ∈ poissonPairIndexSet q := by
  obtain ⟨hns,hrel,_hpre⟩ := mem_filter.mp hn
  have hpos := extendedQuadraticIndexSet_pos hns
  have hd : 0 < Nat.gcd (n 0*n 2) (n 1*n 4) :=
    Nat.gcd_pos_of_pos_right _ (Nat.mul_pos (hpos 1) (hpos 4))
  have hdiv := signed_relation_gcd_dvd positive hrel
  have hk : 0 < n 6/Nat.gcd (n 0*n 2) (n 1*n 4) :=
    Nat.div_pos (Nat.le_of_dvd (hpos 6) hdiv) hd
  apply mem_product.mpr
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro j
    fin_cases j
    · simpa [extendedToPair,extendedQuadraticBound,QuadraticScales.size] using
        (Fintype.mem_piFinset.mp hns) 0
    · simpa [extendedToPair,extendedQuadraticBound,QuadraticScales.size] using
        (Fintype.mem_piFinset.mp hns) 1
    · simpa [extendedToPair,extendedQuadraticBound,QuadraticScales.size] using
        (Fintype.mem_piFinset.mp hns) 2
    · simpa [extendedToPair,extendedQuadraticBound,QuadraticScales.size] using
        (Fintype.mem_piFinset.mp hns) 4
    · apply Finset.mem_Icc.mpr
      refine ⟨hk, (Nat.div_le_self _ _).trans ?_⟩
      have hh := (Fintype.mem_piFinset.mp hns) 6
      simpa [extendedQuadraticBound,QuadraticScales.size] using (Finset.mem_Icc.mp hh).2
  · have hm := (Fintype.mem_piFinset.mp hns) 3
    simpa [spatialIndexSet,extendedToPair,extendedQuadraticBound,QuadraticScales.size] using hm

theorem extendedToPair_summand (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) {n : Fin 7 → ℕ}
    (hrel : signedQuadraticRelation positive n) :
    quadraticPreWeight q α β W n *
      (W 4 ((n 0 : ℝ)*n 2*n 3/((n 1 : ℝ)*n 4*q.N₂)) : ℂ) =
        poissonPairSummand positive q α β W (extendedToPair n) := by
  let d := Nat.gcd (n 0*n 2) (n 1*n 4)
  have hdiv : d ∣ n 6 := signed_relation_gcd_dvd positive hrel
  have hdk : d*(n 6/d) = n 6 := Nat.mul_div_cancel' hdiv
  have heq : ((n 0*n 2 : ℕ) : ℤ)*(n 3 : ℤ)-((n 1*n 4 : ℕ) : ℤ)*(n 5 : ℤ) =
      (d : ℤ)*signedShift positive (n 6/d) := by
    rw [← signedShift_mul, hdk]
    exact signed_relation_as_equation positive hrel
  have hex : ∃ z : ℤ, ((n 0*n 2 : ℕ) : ℤ)*(n 3 : ℤ)-
      ((n 1*n 4 : ℕ) : ℤ)*z = (d : ℤ)*signedShift positive (n 6/d) := ⟨n 5,heq⟩
  dsimp only [poissonPairSummand,extendedToPair,reducedEquationTerm]
  change _ = _ * (if ∃ z : ℤ, ((n 0*n 2 : ℕ) : ℤ)*(n 3 : ℤ)-
    ((n 1*n 4 : ℕ) : ℤ)*z = (d : ℤ)*signedShift positive (n 6/d) then _ else _)
  rw [ite_eq_left hex]
  have hreal : (d : ℝ)*(n 6/d : ℕ) = (n 6 : ℝ) := by exact_mod_cast hdk
  dsimp only [quadraticPreWeight,poissonOuterWeight,outerGCD,outerLeft,outerRight]
  change _ = α (n 0)*β (n 1)*(W 0 ((d : ℝ)*(n 6/d : ℕ)/q.H) : ℂ)*
    (W 1 (n 2/q.M₁) : ℂ)*(W 3 (n 4/q.N₁) : ℂ)*_
  rw [hreal]
  dsimp
  push_cast
  ring

theorem extendedToPair_injective_on_solutions (positive : Bool)
    {n n' : Fin 7 → ℕ} (_hpos : ∀ j, 0 < n j) (hpos' : ∀ j, 0 < n' j)
    (hrel : signedQuadraticRelation positive n) (hrel' : signedQuadraticRelation positive n')
    (heq : extendedToPair n = extendedToPair n') : n = n' := by
  have h₀ : n 0 = n' 0 := congrArg (fun p => p.1 0) heq
  have h₁ : n 1 = n' 1 := congrArg (fun p => p.1 1) heq
  have h₂ : n 2 = n' 2 := congrArg (fun p => p.1 2) heq
  have h₃ : n 3 = n' 3 := congrArg Prod.snd heq
  have h₄ : n 4 = n' 4 := congrArg (fun p => p.1 3) heq
  have hk : n 6/Nat.gcd (n 0*n 2) (n 1*n 4) =
      n' 6/Nat.gcd (n' 0*n' 2) (n' 1*n' 4) := congrArg (fun p => p.1 4) heq
  have hd : Nat.gcd (n 0*n 2) (n 1*n 4) = Nat.gcd (n' 0*n' 2) (n' 1*n' 4) := by
    rw [h₀,h₁,h₂,h₄]
  have h₆ : n 6 = n' 6 := by
    calc n 6 = Nat.gcd (n 0*n 2) (n 1*n 4)*
        (n 6/Nat.gcd (n 0*n 2) (n 1*n 4)) :=
          (Nat.mul_div_cancel' (signed_relation_gcd_dvd positive hrel)).symm
      _ = Nat.gcd (n' 0*n' 2) (n' 1*n' 4)*
        (n' 6/Nat.gcd (n' 0*n' 2) (n' 1*n' 4)) := by rw [hk,hd]
      _ = n' 6 := Nat.mul_div_cancel' (signed_relation_gcd_dvd positive hrel')
  have h₅ : n 5 = n' 5 := by
    have he := signed_relation_as_equation positive hrel
    have he' := signed_relation_as_equation positive hrel'
    rw [h₀,h₁,h₂,h₃,h₄,h₆] at he
    have hz := equation_partner_unique (n' 0*n' 2) (n' 1*n' 4)
      (Nat.mul_pos (hpos' 1) (hpos' 4)) (n' 3) (signedShift positive (n' 6)) _ _ he he'
    exact_mod_cast hz
  funext j
  fin_cases j <;> assumption

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1600000

theorem continuous_finitePoissonKernel (L t : ℝ) :
    Continuous (finitePoissonKernel L t) := by
  unfold finitePoissonKernel
  apply continuous_finsetSum
  intro l _
  by_cases hl : l = 0
  · simp only [hl,ite_true]
    exact continuous_const
  · simp only [ite_eq_right hl]
    exact continuous_const.mul (continuous_ePhase.comp (continuous_const.mul continuous_id))

theorem outerFourierIntegrand_integrable {q : QuadraticScales}
    (h : ∀ j, 1 ≤ q.size j) {W : Fin 5 → ℝ → ℝ}
    (hW : ∀ i, SmoothDyadicWeight (W i)) {n : Fin 5 → ℕ}
    (hn : n ∈ quadraticMainIndexSet q) (positive : Bool) (ρ : ℝ) :
    Integrable (outerFourierIntegrand positive q ρ W n) := by
  have hY : (0 : ℝ) < outerRight n := by exact_mod_cast outerRight_pos hn
  have hd : (0 : ℝ) < outerGCD n := by exact_mod_cast outerGCD_pos hn
  have hM : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have ha : (outerRight n : ℝ)/((outerGCD n : ℝ)*q.M₂) ≠ 0 :=
    (div_pos hY (mul_pos hd hM)).ne'
  apply Continuous.integrable_of_hasCompactSupport
  · exact (poissonProfile_contDiff _ _ (hW 2) (hW 4)).continuous.mul
      (continuous_finitePoissonKernel _ _)
  · exact (poissonProfile_hasCompactSupport (W₄ := W 4) (hW 2) ha).mul_right

theorem outer_weight_shift_bound {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ} (h : ∀ j, 1 ≤ q.size j)
    (hw : NormalizedWeightData bounds q α β W) {n : Fin 5 → ℕ}
    (hne : poissonOuterWeight q α β W n ≠ 0) :
    (outerGCD n : ℝ)*n 4 ≤ 2*q.H := by
  have hH : 0 < q.H := lt_of_lt_of_le (by norm_num) (h 6)
  have h₀ne : W 0 ((outerGCD n : ℝ)*n 4/q.H) ≠ 0 := by
    intro hz
    exact hne (by simp [poissonOuterWeight,hz])
  exact (dyadic_weight_argument_bounds (hw.smooth 0) hH h₀ne).2

def gcdIndexSet (q : QuadraticScales) : Finset ℕ := Icc 1 ⌊2*q.H⌋₊

theorem outerGCD_mem_of_weight_ne_zero {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ} (h : ∀ j, 1 ≤ q.size j)
    (hw : NormalizedWeightData bounds q α β W) {n : Fin 5 → ℕ}
    (hn : n ∈ quadraticMainIndexSet q) (hne : poissonOuterWeight q α β W n ≠ 0) :
    outerGCD n ∈ gcdIndexSet q := by
  have hk : (1 : ℝ) ≤ n 4 := by
    exact_mod_cast (quadraticMainIndexSet_coordinate_bounds q h hn 4).1
  have hh := outer_weight_shift_bound h hw hne
  have hH : 1 ≤ q.H := h 6
  apply Finset.mem_Icc.mpr
  refine ⟨outerGCD_pos hn, (Nat.le_floor_iff (by linarith : 0 ≤ 2*q.H)).mpr ?_⟩
  calc (outerGCD n : ℝ) ≤ (outerGCD n : ℝ)*n 4 :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) hk
    _ ≤ 2*q.H := hh

def gcdBlockIntegrand (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (d : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ (quadraticMainIndexSet q).filter (fun n => outerGCD n = d),
    poissonOuterWeight q α β W n * outerFourierIntegrand positive q ρ W n x

theorem gcdBlockIntegrand_integrable {q : QuadraticScales}
    (h : ∀ j, 1 ≤ q.size j) {W : Fin 5 → ℝ → ℝ}
    (hW : ∀ i, SmoothDyadicWeight (W i)) (positive : Bool) (ρ : ℝ)
    (α β : ℕ → ℂ) (d : ℕ) : Integrable (gcdBlockIntegrand positive q ρ α β W d) := by
  apply integrable_finsetSum
  intro n hn
  exact (outerFourierIntegrand_integrable h hW (Finset.mem_filter.mp hn).1 positive ρ).const_mul _

theorem finitePoissonNormalSum_eq_gcd_integrals {bounds : ℕ → ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (positive : Bool) (ρ : ℝ) :
    finitePoissonNormalSum positive q ρ α β W =
      ∑ d ∈ gcdIndexSet q, ∫ x : ℝ in Ioi 0, gcdBlockIntegrand positive q ρ α β W d x := by
  have hi (d : ℕ) : (∫ x : ℝ in Ioi 0, gcdBlockIntegrand positive q ρ α β W d x) =
      ∑ n ∈ (quadraticMainIndexSet q).filter (fun n => outerGCD n = d),
        poissonOuterWeight q α β W n *
          ∫ x : ℝ in Ioi 0, outerFourierIntegrand positive q ρ W n x := by
    unfold gcdBlockIntegrand
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro n hn
      exact ((outerFourierIntegrand_integrable h hw.smooth (mem_filter.mp hn).1 positive ρ).const_mul _).integrableOn
  simp_rw [hi,Finset.sum_filter]
  rw [sum_comm]
  unfold finitePoissonNormalSum
  apply sum_congr rfl
  intro n hn
  by_cases hz : poissonOuterWeight q α β W n = 0
  · simp [hz]
  · have hd := outerGCD_mem_of_weight_ne_zero h hw hn hz
    simp [hd]

theorem finitePoissonKernel_zero_of_short {L : ℝ} (hL : 0 < L) (hshort : L ≤ 1/2)
    (t x : ℝ) : finitePoissonKernel L t x = 0 := by
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : l = 0
  · simp [hl]
  · simp only [ite_eq_right hl,sourceCutoff_zero_of_short hL hshort hl,
      Complex.ofReal_zero,zero_mul]

theorem gcdBlockIntegrand_zero_of_short {q : QuadraticScales}
    (h : ∀ j, 1 ≤ q.size j) (ρ : ℝ) {d : ℕ} (hd : 0 < d)
    (hshort : poissonLength q ρ d ≤ 1/2) (positive : Bool)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (x : ℝ) :
    gcdBlockIntegrand positive q ρ α β W d x = 0 := by
  apply sum_eq_zero
  intro n hn
  have hgd := (mem_filter.mp hn).2
  unfold outerFourierIntegrand
  rw [hgd,finitePoissonKernel_zero_of_short
    (poissonLength_pos q h ρ (by exact_mod_cast hd)) hshort]
  simp

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

theorem poissonPair_nonzero {positive : Bool} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ} {p : (Fin 5 → ℕ) × ℕ}
    (hne : poissonPairSummand positive q α β W p ≠ 0) :
    poissonOuterWeight q α β W p.1 ≠ 0 ∧ W 2 ((p.2 : ℝ)/q.M₂) ≠ 0 ∧
      ∃ z : ℤ, (outerLeft p.1 : ℤ)*(p.2 : ℤ)-(outerRight p.1 : ℤ)*z =
        (outerGCD p.1 : ℤ)*signedShift positive (p.1 4) := by
  have hc : poissonOuterWeight q α β W p.1 ≠ 0 := by
    intro hz
    exact hne (by simp [poissonPairSummand,hz])
  have h₂ : W 2 ((p.2 : ℝ)/q.M₂) ≠ 0 := by
    intro hz
    exact hne (by simp [poissonPairSummand,reducedEquationTerm,hz])
  refine ⟨hc,h₂,?_⟩
  by_contra hx
  change ¬ ∃ z : ℤ, (outerLeft p.1 : ℤ)*(p.2 : ℤ)-(outerRight p.1 : ℤ)*z =
    (Nat.gcd (outerLeft p.1) (outerRight p.1) : ℤ)*signedShift positive (p.1 4) at hx
  exact hne (by simp [poissonPairSummand,reducedEquationTerm,hx])

theorem pair_left_product_bounds {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ} (h : ∀ j, 1 ≤ q.size j)
    (hw : NormalizedWeightData bounds q α β W) {positive : Bool}
    {p : (Fin 5 → ℕ) × ℕ} (hp : p ∈ poissonPairIndexSet q)
    (hne : poissonPairSummand positive q α β W p ≠ 0) :
    q.A*q.M ≤ (outerLeft p.1 : ℝ)*p.2 ∧
      (outerLeft p.1 : ℝ)*p.2 ≤ 8*(q.A*q.M) := by
  obtain ⟨hn,hm⟩ := mem_product.mp hp
  obtain ⟨hc,h₂,_⟩ := poissonPair_nonzero hne
  have hαne : α (p.1 0) ≠ 0 := by
    intro hz
    exact hc (by simp [poissonOuterWeight,hz])
  have hαlo : q.A ≤ (p.1 0 : ℝ) := by
    by_contra hh
    exact hαne (hw.alpha_support _ (fun hh' => hh hh'.1))
  have h₁ne : W 1 ((p.1 2 : ℝ)/q.M₁) ≠ 0 := by
    intro hz
    exact hc (by simp [poissonOuterWeight,hz])
  have hM₁ : 0 < q.M₁ := lt_of_lt_of_le (by norm_num) (h 2)
  have hM₂ : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hMlo := (dyadic_weight_argument_bounds (hw.smooth 1) hM₁ h₁ne).1
  obtain ⟨hmlo,hmhi⟩ := dyadic_weight_argument_bounds (hw.smooth 2) hM₂ h₂
  have hleft := (outer_products_bounds h hw hn hc).1
  refine ⟨?_,?_⟩
  · simp only [QuadraticScales.M,outerLeft,Nat.cast_mul]
    calc q.A*(q.M₁*q.M₂) = (q.A*q.M₁)*q.M₂ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul hαlo hMlo hM₁.le (Nat.cast_nonneg _)) hmlo hM₂.le
        (by positivity)
  · calc (outerLeft p.1 : ℝ)*p.2 ≤ (4*q.A*q.M₁)*(2*q.M₂) :=
        mul_le_mul hleft hmhi (Nat.cast_nonneg _) (by linarith [h 0])
      _ = _ := by dsimp [QuadraticScales.M]; ring

theorem positive_partner_bounds (positive : Bool) (A B m h : ℕ) (hB : 0 < B)
    {U H : ℝ} (hsmall : 2*H < U)
    (hlo : U ≤ (A : ℝ)*m) (hhi : (A : ℝ)*m ≤ 8*U)
    (hh : (h : ℝ) ≤ 2*H) {z : ℤ}
    (heq : (A : ℤ)*(m : ℤ)-(B : ℤ)*z = signedShift positive h) :
    0 < z ∧ (z : ℝ) ≤ 8*U+2*H := by
  have hB₁ : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB₀ : (0 : ℝ) < B := by exact_mod_cast hB
  have hz : (0 : ℝ) < z := by
    have he : (A : ℝ)*(m : ℝ)-(B : ℝ)*(z : ℝ) =
        if positive then (h : ℝ) else -(h : ℝ) := by
      exact_mod_cast heq
    by_contra hnot
    have hprod : (B : ℝ)*(z : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB₀.le (not_lt.mp hnot)
    cases positive <;> simp only [Bool.false_eq_true,ite_false,ite_true] at he
    all_goals nlinarith [Nat.cast_nonneg (α := ℝ) h]
  refine ⟨by exact_mod_cast hz,?_⟩
  have hle : (z : ℝ) ≤ (B : ℝ)*(z : ℝ) := le_mul_of_one_le_left hz.le hB₁
  have he : (A : ℝ)*(m : ℝ)-(B : ℝ)*(z : ℝ) =
      if positive then (h : ℝ) else -(h : ℝ) := by exact_mod_cast heq
  cases positive <;> simp only [Bool.false_eq_true,ite_false,ite_true] at he
  all_goals nlinarith [Nat.cast_nonneg (α := ℝ) h]

def pairLift (p : (Fin 5 → ℕ) × ℕ) (z : ℕ) : Fin 7 → ℕ :=
  ![p.1 0,p.1 1,p.1 2,p.2,p.1 3,z,outerGCD p.1*p.1 4]

theorem extendedToPair_pairLift (p : (Fin 5 → ℕ) × ℕ) (z : ℕ)
    (hd : 0 < outerGCD p.1) : extendedToPair (pairLift p z) = p := by
  apply Prod.ext
  · funext j
    fin_cases j
    · rfl
    · rfl
    · rfl
    · rfl
    · change outerGCD p.1*p.1 4/outerGCD p.1 = p.1 4
      exact Nat.mul_div_cancel_left _ hd
  · rfl

theorem pairLift_relation (positive : Bool) {p : (Fin 5 → ℕ) × ℕ} {z : ℤ}
    (hz : 0 ≤ z) (heq : (outerLeft p.1 : ℤ)*(p.2 : ℤ)-(outerRight p.1 : ℤ)*z =
      (outerGCD p.1 : ℤ)*signedShift positive (p.1 4)) :
    signedQuadraticRelation positive (pairLift p z.toNat) := by
  have he : (outerLeft p.1 : ℤ)*(p.2 : ℤ)-(outerRight p.1 : ℤ)*z =
      signedShift positive (outerGCD p.1*p.1 4) := by
    rw [signedShift_mul]
    exact heq
  change (p.1 0 : ℤ)*p.1 2*p.2-(p.1 1 : ℤ)*p.1 3*(z.toNat : ℕ) = _
  simpa [outerLeft,outerRight,Int.toNat_of_nonneg hz,signedShift,pairLift] using he

theorem pairLift_preWeight (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) (p : (Fin 5 → ℕ) × ℕ) (z : ℕ) :
    quadraticPreWeight q α β W (pairLift p z) =
      poissonOuterWeight q α β W p.1*(W 2 ((p.2 : ℝ)/q.M₂) : ℂ) := by
  simp [quadraticPreWeight,pairLift,poissonOuterWeight,Nat.cast_mul]
  ring

theorem pairLift_mem_extended {q : QuadraticScales} (h : ∀ j, 1 ≤ q.size j)
    {p : (Fin 5 → ℕ) × ℕ} (hp : p ∈ poissonPairIndexSet q) {z : ℕ}
    (hz : 0 < z) (hzhi : (z : ℝ) ≤ 8*(q.A*q.M)+2*q.H)
    (hshift : (outerGCD p.1 : ℝ)*p.1 4 ≤ 2*q.H) :
    pairLift p z ∈ extendedQuadraticIndexSet q := by
  obtain ⟨hn,hm⟩ := Finset.mem_product.mp hp
  have hd := outerGCD_pos hn
  have hk := (quadraticMainIndexSet_coordinate_bounds q h hn 4).1
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
  have hM₁ : 0 < q.M₁ := lt_of_lt_of_le (by norm_num) (h 2)
  have hM₂ : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hH : 0 < q.H := lt_of_lt_of_le (by norm_num) (h 6)
  apply Fintype.mem_piFinset.mpr
  intro j
  fin_cases j
  · simpa [pairLift,extendedQuadraticBound,QuadraticScales.size] using
      Fintype.mem_piFinset.mp hn 0
  · simpa [pairLift,extendedQuadraticBound,QuadraticScales.size] using
      Fintype.mem_piFinset.mp hn 1
  · simpa [pairLift,extendedQuadraticBound,QuadraticScales.size] using
      Fintype.mem_piFinset.mp hn 2
  · simpa [pairLift,extendedQuadraticBound,QuadraticScales.size,spatialIndexSet] using hm
  · simpa [pairLift,extendedQuadraticBound,QuadraticScales.size] using
      Fintype.mem_piFinset.mp hn 3
  · apply Finset.mem_Icc.mpr
    refine ⟨hz,?_⟩
    change z ≤ max ⌊2*q.N₂⌋₊ ⌊8*(q.A*q.M)+2*q.H⌋₊
    exact le_max_of_le_right ((Nat.le_floor_iff
      (by dsimp [QuadraticScales.M]; positivity : 0 ≤ 8*(q.A*q.M)+2*q.H)).mpr hzhi)
  · apply Finset.mem_Icc.mpr
    refine ⟨Nat.mul_pos hd hk,?_⟩
    change outerGCD p.1*p.1 4 ≤ ⌊2*q.H⌋₊
    apply (Nat.le_floor_iff (by positivity : 0 ≤ 2*q.H)).mpr
    simpa only [Nat.cast_mul] using hshift

theorem poissonPair_has_lift {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ} (h : ∀ j, 1 ≤ q.size j)
    (hw : NormalizedWeightData bounds q α β W) (hsmall : 2*q.H < q.A*q.M)
    (positive : Bool) {p : (Fin 5 → ℕ) × ℕ} (hp : p ∈ poissonPairIndexSet q)
    (hne : poissonPairSummand positive q α β W p ≠ 0) :
    ∃ n ∈ extendedActiveIndexSet positive q α β W,
      quadraticPreWeight q α β W n *
        (W 4 ((n 0 : ℝ)*n 2*n 3/((n 1 : ℝ)*n 4*q.N₂)) : ℂ) ≠ 0 ∧
          extendedToPair n = p := by
  have hn := (Finset.mem_product.mp hp).1
  obtain ⟨hc,h₂,z,heq⟩ := poissonPair_nonzero hne
  obtain ⟨hlo,hhi⟩ := pair_left_product_bounds h hw hp hne
  have hshift := outer_weight_shift_bound h hw hc
  have he : (outerLeft p.1 : ℤ)*(p.2 : ℤ)-(outerRight p.1 : ℤ)*z =
      signedShift positive (outerGCD p.1*p.1 4) := by
    rw [signedShift_mul]
    exact heq
  have hh : ((outerGCD p.1*p.1 4 : ℕ) : ℝ) ≤ 2*q.H := by
    simpa only [Nat.cast_mul] using hshift
  obtain ⟨hz,hzhi⟩ := positive_partner_bounds positive (outerLeft p.1) (outerRight p.1)
    p.2 (outerGCD p.1*p.1 4) (outerRight_pos hn) hsmall hlo hhi hh he
  have hzcast : (z.toNat : ℝ) = (z : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hz.le
  have hmem := pairLift_mem_extended h hp (show 0 < z.toNat by omega)
    (by rwa [hzcast]) hshift
  have hrel := pairLift_relation positive hz.le heq
  have hpre : quadraticPreWeight q α β W (pairLift p z.toNat) ≠ 0 := by
    rw [pairLift_preWeight]
    exact mul_ne_zero hc (by exact_mod_cast h₂)
  have hmap := extendedToPair_pairLift p z.toNat (outerGCD_pos hn)
  refine ⟨pairLift p z.toNat, Finset.mem_filter.mpr ⟨hmem,hrel,hpre⟩,?_,hmap⟩
  rw [extendedToPair_summand positive q α β W hrel,hmap]
  exact hne

theorem shiftRemovedExtendedSum_eq_reduced {bounds : ℕ → ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (hsmall : 2*q.H < q.A*q.M) (positive : Bool) :
    shiftRemovedExtendedSum positive q α β W = shiftRemovedReducedSum positive q α β W := by
  rw [shiftRemovedReducedSum_eq_pairs positive q α β W (hw.smooth 2)
    (lt_of_lt_of_le (by norm_num) (h 3))]
  unfold shiftRemovedExtendedSum
  apply Finset.sum_bij_ne_zero (fun n _ _ => extendedToPair n)
  · intro n hn _
    exact extendedToPair_mem positive h hn
  · intro n hn _ n' hn' _ heq
    exact extendedToPair_injective_on_solutions positive
      (extendedQuadraticIndexSet_pos (mem_filter.mp hn).1)
      (extendedQuadraticIndexSet_pos (mem_filter.mp hn').1)
      (mem_filter.mp hn).2.1 (mem_filter.mp hn').2.1 heq
  · intro p hp hne
    obtain ⟨n,hn,hne',heq⟩ := poissonPair_has_lift h hw hsmall positive hp hne
    exact ⟨n,hn,hne',heq⟩
  · intro n hn _
    exact extendedToPair_summand positive q α β W (mem_filter.mp hn).2.1

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def normalFormError (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) : ℂ :=
  signedQuadraticDiscrepancy positive q α β W-
    ∑ d ∈ gcdIndexSet q, ∫ x : ℝ in Ioi 0, gcdBlockIntegrand positive q ρ α β W d x

theorem normalFormError_identity (positive : Bool) (q : QuadraticScales) (ρ : ℝ)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) :
    signedQuadraticDiscrepancy positive q α β W =
      (∑ d ∈ gcdIndexSet q, ∫ x : ℝ in Ioi 0, gcdBlockIntegrand positive q ρ α β W d x)+
        normalFormError positive q ρ α β W := by
  unfold normalFormError
  ring

theorem normalized_finite_poisson_normal_form {K ρ : ℝ} (hK : 1 ≤ K) (hρ : 0 < ρ)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ),
      (∀ j, 1 ≤ q.size j) → NormalizedWeightData bounds q α β W →
      q.H ≤ K*q.mass → q.A*q.M ≤ K*q.B*q.N → q.B*q.N ≤ K*q.A*q.M →
      2*q.H < q.A*q.M → ∀ positive : Bool,
        ‖normalFormError positive q ρ α β W‖ ≤ C*q.mass^(2*ρ)*q.H^2 := by
  obtain ⟨C₁,hC₁,hshift⟩ := actual_extended_weight_shift_error hρ hK (hb 0) (hb 1)
  let C₂ : ℝ := 32*K*(bounds 0)^3*poissonRemainderConstant bounds K ρ
  have hb₀ := hb 0
  have hK₀ : 0 ≤ K := by linarith
  have hC₂ : 0 ≤ C₂ := by
    have hc := poissonRemainderConstant_nonneg (ρ := ρ) hb (by linarith : 0 ≤ K)
    dsimp only [C₂]
    positivity
  refine ⟨C₁+C₂,add_nonneg hC₁ hC₂,?_⟩
  intro q α β W h hw hH hbal₁ hbal₂ hsmall positive
  have hQ := (poisson_scale_bounds q h).1
  have hQp : 0 < q.mass := lt_of_lt_of_le (by norm_num) hQ
  have hH₁ : 1 ≤ q.H := h 6
  have hshift' := hshift positive q α β W h hH hbal₁ hw.beta_support
    hw.alpha_bound hw.beta_bound hw.smooth hw.weight_norm (fun x => hw.derivatives 1 4 x)
  rw [shiftRemovedExtendedSum_eq_reduced h hw hsmall positive] at hshift'
  have htail := summed_actual_poisson_error hK hρ h hw hH hbal₁ hbal₂ positive
  change ‖_‖ ≤ C₂/q.mass^7 at htail
  have htail' : C₂/q.mass^7 ≤ C₂*q.mass^(2*ρ)*q.H^2 := by
    calc C₂/q.mass^7 ≤ C₂ := (div_le_iff₀ (pow_pos hQp 7)).mpr
          (le_mul_of_one_le_right hC₂ (one_le_pow₀ hQ))
      _ ≤ C₂*q.mass^(2*ρ) := le_mul_of_one_le_right hC₂
          (Real.one_le_rpow hQ (by linarith))
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hH₁)
  have hid : normalFormError positive q ρ α β W =
      (signedQuadraticSum positive q α β W-shiftRemovedReducedSum positive q α β W)+
        ((shiftRemovedReducedSum positive q α β W-quadraticZeroMode q α β W)-
          finitePoissonNormalSum positive q ρ α β W) := by
    rw [finitePoissonNormalSum_eq_gcd_integrals h hw]
    unfold normalFormError signedQuadraticDiscrepancy
    ring
  rw [hid]
  calc _ ≤ ‖signedQuadraticSum positive q α β W-shiftRemovedReducedSum positive q α β W‖+
      ‖(shiftRemovedReducedSum positive q α β W-quadraticZeroMode q α β W)-
        finitePoissonNormalSum positive q ρ α β W‖ := norm_add_le _ _
    _ ≤ C₁*q.mass^(2*ρ)*q.H^2+C₂*q.mass^(2*ρ)*q.H^2 :=
      add_le_add hshift' (htail.trans htail')
    _ = _ := by ring

theorem actual_normal_form_one_cutoff {q : QuadraticScales} (ρ : ℝ)
    (positive : Bool) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) :
    signedQuadraticDiscrepancy positive q α β W =
      (∑ d ∈ (gcdIndexSet q).filter (fun d : ℕ => (d : ℝ) ≤ gcdCutoff q ρ),
        ∫ x : ℝ in Ioi 0, gcdBlockIntegrand positive q ρ α β W d x)+
      (∑ d ∈ (gcdIndexSet q).filter (fun d : ℕ => gcdCutoff q ρ < (d : ℝ)),
        ∫ x : ℝ in Ioi 0, gcdBlockIntegrand positive q ρ α β W d x)+
      normalFormError positive q ρ α β W := by
  rw [normalFormError_identity positive q ρ α β W]
  rw [one_cutoff_partition (gcdIndexSet q) (gcdCutoff q ρ)]

end
end DivisorProof
