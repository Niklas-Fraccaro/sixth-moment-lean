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
import Sechstmoment.Arithmetic.QuadraticDivisor.Reduction.BlockSums
import Std

/-! ## Fourier Mass

Uniform L1 mass of the sampled Fourier coefficients.  Unlike a bound by a
fixed inverse-square series alone, the estimate here is uniform for every
positive sampling scale, including scales tending to zero.
-/
namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000

def cauchyEnvelope (r x : ℝ) : ℝ := (1+(r*x)^2)⁻¹

theorem cauchyEnvelope_nonneg (r x : ℝ) : 0 ≤ cauchyEnvelope r x := by
  unfold cauchyEnvelope
  positivity

theorem cauchyEnvelope_antitone {r : ℝ} (hr : 0 ≤ r) :
    AntitoneOn (cauchyEnvelope r) (Ici 0) := by
  intro x hx y hy hxy
  unfold cauchyEnvelope
  apply inv_anti₀ (by positivity : 0 < 1+(r*x)^2)
  have hprod : r*x ≤ r*y := mul_le_mul_of_nonneg_left hxy hr
  nlinarith [pow_le_pow_left₀ (mul_nonneg hr hx) hprod 2]

theorem cauchyEnvelope_summable_nat {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℕ => cauchyEnvelope r n) :=
  (cauchyEnvelope_antitone hr.le).summable_of_integrableOn_Ioi_zero
    (integrable_inv_one_add_mul_sq hr.ne').integrableOn
    (fun x _ => cauchyEnvelope_nonneg r x)

theorem cauchyEnvelope_summable_int {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℤ => cauchyEnvelope r n) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  refine ⟨cauchyEnvelope_summable_nat hr,?_⟩
  simpa [cauchyEnvelope] using cauchyEnvelope_summable_nat hr

theorem cauchyEnvelope_tsum_positive_le {r : ℝ} (hr : 0 < r) :
    (∑' n : ℕ+, cauchyEnvelope r n) ≤ Real.pi/r := by
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => cauchyEnvelope r n)]
  calc _ ≤ ∫ x : ℝ in Ioi 0, cauchyEnvelope r x :=
      (cauchyEnvelope_antitone hr.le).tsum_add_one_le_integral
        (integrable_inv_one_add_mul_sq hr.ne').integrableOn
        (fun x _ => cauchyEnvelope_nonneg r x)
    _ ≤ ∫ x : ℝ, cauchyEnvelope r x :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall (cauchyEnvelope_nonneg r))
        (integrable_inv_one_add_mul_sq hr.ne')
    _ = Real.pi/r := by simp [cauchyEnvelope,abs_of_pos hr]

/-- The sampled Cauchy envelope has mass at most `1+2π/r`. -/
theorem cauchyEnvelope_tsum_int_le {r : ℝ} (hr : 0 < r) :
    (∑' n : ℤ, cauchyEnvelope r n) ≤ 1+2*Real.pi/r := by
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (by
    intro n
    simp [cauchyEnvelope]) (cauchyEnvelope_summable_int hr)]
  have h := cauchyEnvelope_tsum_positive_le hr
  simp only [Int.cast_zero,Int.cast_natCast,nsmul_eq_mul] at *
  have hz : cauchyEnvelope r 0 = 1 := by simp [cauchyEnvelope]
  rw [hz]
  norm_num only [Nat.cast_ofNat]
  calc 1+2*(∑' n : ℕ+, cauchyEnvelope r n) ≤ 1+2*(Real.pi/r) := by gcongr
    _ = _ := by ring

theorem decay_square_le_cauchy (r : ℝ) (hr : 0 ≤ r) (l : ℤ) :
    1/(1+|(l:ℝ)| *r)^2 ≤ cauchyEnvelope r l := by
  have ht : 0 ≤ |(l:ℝ)| *r := mul_nonneg (abs_nonneg _) hr
  have hsq : 1+(r*(l:ℝ))^2 ≤ (1+|(l:ℝ)| *r)^2 := by
    have heq : (r*(l:ℝ))^2 = (|(l:ℝ)| *r)^2 := by
      rw [mul_pow,mul_pow,sq_abs]
      ring
    rw [heq]
    nlinarith
  unfold cauchyEnvelope
  rw [one_div]
  exact inv_anti₀ (by positivity) hsq

/-- The absolute Fourier mass needed in smooth completion (15). -/
theorem poissonCoefficient_absolute_mass {W₂ W₄ : ℝ → ℝ} {a b r K : ℝ}
    {bounds : ℕ → ℝ} (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (hr : 0 < r) (ha : 1 ≤ a*r) (hb : 0 ≤ b*r) (haK : a*r ≤ K) (hbK : b*r ≤ K)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j) :
    (∑' l : ℤ, ‖poissonCoefficient W₂ W₄ a b l‖) ≤
      (2+2*Real.pi)*profileFourierBound bounds K 2*(1+r) := by
  have hapos : 0 < a := by nlinarith
  have hb₀ : ∀ j, 0 ≤ bounds j := fun j => (norm_nonneg _).trans (hder₂ j 0)
  have hC : 0 ≤ profileFourierBound bounds K 2 :=
    profileFourierBound_nonneg hb₀ (by linarith) 2
  have hs := (cauchyEnvelope_summable_int hr).mul_left (r*profileFourierBound bounds K 2)
  have hm : ∀ l : ℤ, ‖poissonCoefficient W₂ W₄ a b l‖ ≤
      (r*profileFourierBound bounds K 2)*cauchyEnvelope r l := by
    intro l
    apply (poissonCoefficient_decay h₂ h₄ hr ha hb haK hbK hder₂ hder₄ 2 l).trans
    calc _ = (r*profileFourierBound bounds K 2)*(1/(1+|(l:ℝ)| *r)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (decay_square_le_cauchy r hr.le l) (by positivity)
  calc _ ≤ ∑' l : ℤ, (r*profileFourierBound bounds K 2)*cauchyEnvelope r l :=
      (poissonCoefficient_norm_summable h₂ h₄ hapos.ne').tsum_le_tsum hm hs
    _ = (r*profileFourierBound bounds K 2)*∑' l : ℤ, cauchyEnvelope r l := tsum_mul_left
    _ ≤ (r*profileFourierBound bounds K 2)*(1+2*Real.pi/r) :=
      mul_le_mul_of_nonneg_left (cauchyEnvelope_tsum_int_le hr) (by positivity)
    _ = profileFourierBound bounds K 2*(r+2*Real.pi) := by field_simp
    _ ≤ _ := by
      have hb : r+2*Real.pi ≤ (2+2*Real.pi)*(1+r) := by nlinarith [Real.pi_pos]
      calc _ ≤ profileFourierBound bounds K 2*((2+2*Real.pi)*(1+r)) :=
          mul_le_mul_of_nonneg_left hb hC
        _ = _ := by ring

end
end DivisorProof



/-! ## Weil Completion

Smooth completion for the actual two-weight profiles, derived from the
proved Estermann estimate with its explicit 2-adic factor.  Poisson, the finite residue sum, the interchange
with an absolutely convergent Fourier series, and the uniform Fourier L1
bound are all proved rather than included in the open input.
-/
namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

theorem ePhase_add (s t : ℝ) : ePhase (s+t) = ePhase s*ePhase t := by
  unfold ePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem profile_lattice_poisson {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) (ha : a ≠ 0)
    {c : ℕ} (hc : 0 < c) (x : ℕ) :
    (∑' j : ℤ, poissonProfile W₂ W₄ a b ((x:ℝ)+(c:ℝ)*j)) =
      ∑' l : ℤ, poissonCoefficient W₂ W₄ (a*c) (b*c) l*
        ePhase (-(l:ℝ)*((x:ℝ)/c)) := by
  have hcp : (0:ℝ) < c := by exact_mod_cast hc
  have heq (j : ℤ) : poissonProfile W₂ W₄ a b ((x:ℝ)+(c:ℝ)*j) =
      poissonProfile W₂ W₄ (a*c) (b*c) ((x:ℝ)/c+j) := by
    unfold poissonProfile
    congr 2 <;> field_simp
  simp_rw [heq]
  exact poisson_profile_identity h₂ h₄ (mul_ne_zero ha hcp.ne') _

/-- A smooth coprime sum, grouped into its finitely many residue classes. -/
def completedProfileSum (W₂ W₄ : ℝ → ℝ) (a b : ℝ) (c : ℕ) (k : ℤ) : ℂ :=
  ∑ x ∈ (range c).filter (fun x => x.Coprime c),
    ePhase ((k:ℝ)*(inverseRepresentative x c:ℝ)/(c:ℝ))*
      ∑' j : ℤ, poissonProfile W₂ W₄ a b ((x:ℝ)+(c:ℝ)*j)

/-- Exact completion; no unproved interchange of infinite integrand sums is used. -/
theorem completedProfileSum_identity {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) (ha : a ≠ 0)
    {c : ℕ} (hc : 0 < c) (k : ℤ) :
    completedProfileSum W₂ W₄ a b c k =
      ∑' l : ℤ, poissonCoefficient W₂ W₄ (a*c) (b*c) l*kloostermanSum c (-l) k := by
  have hcp : (0:ℝ) < c := by exact_mod_cast hc
  have hac : a*(c:ℝ) ≠ 0 := mul_ne_zero ha hcp.ne'
  unfold completedProfileSum
  simp_rw [profile_lattice_poisson h₂ h₄ ha hc,← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun (x : ℕ) _ =>
    (poissonSeries_summable h₂ h₄ hac ((x:ℝ)/c)).mul_left
      (ePhase ((k:ℝ)*(inverseRepresentative x c:ℝ)/(c:ℝ))))]
  apply tsum_congr
  intro l
  unfold kloostermanSum
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  calc _ = poissonCoefficient W₂ W₄ (a*c) (b*c) l*
      (ePhase ((k:ℝ)*(inverseRepresentative x c:ℝ)/(c:ℝ))*
        ePhase (-(l:ℝ)*((x:ℝ)/c))) := by ring
    _ = poissonCoefficient W₂ W₄ (a*c) (b*c) l*
      ePhase ((k:ℝ)*(inverseRepresentative x c:ℝ)/(c:ℝ)-(l:ℝ)*((x:ℝ)/c)) := by
        rw [← ePhase_add]
        congr 2
        ring
    _ = _ := by
      congr 2
      push_cast
      ring

/-- The direct norm consequence of the proved Estermann estimate for any
absolutely summable coefficient sequence. -/
theorem Estermann.completed_series_bound
    {c : ℕ} (hc : 0 < c) (k : ℤ) {F : ℤ → ℂ}
    (hF : Summable (fun l => ‖F l‖)) :
    ‖∑' l : ℤ, F l*kloostermanSum c (-l) k‖ ≤
      (twoAdicWeight c*(c.divisors.card:ℝ)*(c:ℝ)^(1/2:ℝ)*(Nat.gcd k.natAbs c:ℝ)^(1/2:ℝ))*
        ∑' l : ℤ, ‖F l‖ := by
  let B := twoAdicWeight c*(c.divisors.card:ℝ)*(c:ℝ)^(1/2:ℝ)*(Nat.gcd k.natAbs c:ℝ)^(1/2:ℝ)
  have hbound (l : ℤ) : ‖F l*kloostermanSum c (-l) k‖ ≤ ‖F l‖*B := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (Estermann.fixed_second_parameter hc (-l) k) (norm_nonneg _)
  calc _ ≤ ∑' l : ℤ, ‖F l‖*B := tsum_of_norm_bounded (hF.mul_right B).hasSum hbound
    _ = B*∑' l : ℤ, ‖F l‖ := by rw [tsum_mul_right,mul_comm]

/-- Smooth completion (15) for the two-weight profiles actually used in
the large-gcd argument. Its constant depends only on the fixed derivative
sequence and the normalized slope bound. -/
theorem Estermann.smooth_profile_completion
    {W₂ W₄ : ℝ → ℝ} {a b V K : ℝ} {bounds : ℕ → ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (hV : 0 < V) (ha : 1 ≤ a*V) (hb : 0 ≤ b*V) (haK : a*V ≤ K) (hbK : b*V ≤ K)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j)
    {c : ℕ} (hc : 0 < c) (k : ℤ) :
    ‖completedProfileSum W₂ W₄ a b c k‖ ≤
      ((2+2*Real.pi)*profileFourierBound bounds K 2)*
        twoAdicWeight c*(c.divisors.card:ℝ)*(c:ℝ)^(1/2:ℝ)*(Nat.gcd k.natAbs c:ℝ)^(1/2:ℝ)*
          (1+V/(c:ℝ)) := by
  have hcp : (0:ℝ) < c := by exact_mod_cast hc
  have hap : 0 < a := by nlinarith
  have hscale : (a*c)*(V/c) = a*V := by field_simp
  have hscale' : (b*c)*(V/c) = b*V := by field_simp
  have hmass := poissonCoefficient_absolute_mass h₂ h₄ (div_pos hV hcp)
    (hscale ▸ ha) (hscale' ▸ hb) (hscale ▸ haK) (hscale' ▸ hbK) hder₂ hder₄
  rw [completedProfileSum_identity h₂ h₄ hap.ne' hc]
  calc _ ≤ (twoAdicWeight c*(c.divisors.card:ℝ)*(c:ℝ)^(1/2:ℝ)*(Nat.gcd k.natAbs c:ℝ)^(1/2:ℝ))*
      (∑' l : ℤ, ‖poissonCoefficient W₂ W₄ (a*c) (b*c) l‖) :=
        Estermann.completed_series_bound hc k
          (poissonCoefficient_norm_summable h₂ h₄ (mul_pos hap hcp).ne')
    _ ≤ (twoAdicWeight c*(c.divisors.card:ℝ)*(c:ℝ)^(1/2:ℝ)*(Nat.gcd k.natAbs c:ℝ)^(1/2:ℝ))*
      ((2+2*Real.pi)*profileFourierBound bounds K 2*(1+V/(c:ℝ))) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end
end DivisorProof



/-! ## Weil Natural Sum

The completed smooth sum is identified with the literal finite positive
integer sum. In particular neither negative integers nor residue-class
tails are silently added to the divisor calculation.
-/
namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def coprimeProfileTerm (W₂ W₄ : ℝ → ℝ) (a b : ℝ) (c : ℕ) (k : ℤ) (m : ℕ) : ℂ :=
  if m.Coprime c then poissonProfile W₂ W₄ a b m*
    ePhase ((k:ℝ)*(inverseRepresentative m c:ℝ)/(c:ℝ)) else 0

theorem coprimeProfileTerm_hasFiniteSupport {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (ha : 0 < a) (c : ℕ) (k : ℤ) :
    Function.HasFiniteSupport (coprimeProfileTerm W₂ W₄ a b c k) := by
  apply (Finset.Icc 1 ⌊2/a⌋₊).finite_toSet.subset
  intro m hm
  have hW : W₂ (a*m) ≠ 0 := by
    intro hz
    exact hm (by simp [coprimeProfileTerm,poissonProfile,hz])
  have hs := h₂.2 (subset_tsupport _ hW)
  apply Finset.mem_Icc.mpr
  constructor
  · by_contra hh
    have hm₀ : m = 0 := by omega
    simp only [hm₀,Nat.cast_zero,mul_zero] at hs
    linarith [hs.1]
  · apply (Nat.le_floor_iff (by positivity : 0 ≤ 2/a)).mpr
    apply (le_div_iff₀ ha).mpr
    nlinarith [hs.2]

theorem profile_lattice_nonnegative {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (ha : 0 < a) {c : ℕ} (hc : 0 < c)
    {x : ℕ} (hx : x < c) :
    (∑' j : ℤ, poissonProfile W₂ W₄ a b ((x:ℝ)+(c:ℝ)*j)) =
      ∑' j : ℕ, poissonProfile W₂ W₄ a b ((x:ℝ)+(c:ℝ)*j) := by
  have hinj : Function.Injective (fun j : ℕ => (j:ℤ)) := by
    intro i j heq
    change (i:ℤ) = (j:ℤ) at heq
    exact_mod_cast heq
  have hs : Function.support (fun j : ℤ =>
      poissonProfile W₂ W₄ a b ((x:ℝ)+(c:ℝ)*j)) ⊆ Set.range (fun j : ℕ => (j:ℤ)) := by
    intro j hj
    have hjp : 0 ≤ j := by
      by_contra hh
      have hj' : (j:ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
      have hc' : (0:ℝ) < c := by exact_mod_cast hc
      have hx' : (x:ℝ) < c := by exact_mod_cast hx
      have hz : (x:ℝ)+(c:ℝ)*j ≤ 0 := by nlinarith
      exact hj (poissonProfile_zero_of_nonpos h₂ ha hz)
    exact ⟨j.toNat,Int.toNat_of_nonneg hjp⟩
  rw [← hinj.tsum_eq hs]
  simp only [Int.cast_natCast]

theorem inverseRepresentative_add_modulus (x c j : ℕ) :
    inverseRepresentative (x+c*j) c = inverseRepresentative x c := by
  unfold inverseRepresentative
  congr 1
  simp

theorem zmod_sum_vals {c : ℕ} [NeZero c] (F : ℕ → ℂ) :
    (∑ x : ZMod c, F x.val) = ∑ x ∈ range c, F x := by
  apply Finset.sum_bij (fun x _ => x.val)
  · intro x _
    exact mem_range.mpr (ZMod.val_lt x)
  · intro x _ y _ heq
    exact ZMod.val_injective c heq
  · intro x hx
    refine ⟨(x:ZMod c),mem_univ _,?_⟩
    exact ZMod.val_natCast_of_lt (mem_range.mp hx)
  · intro x _
    rfl

/-- Exact residue-class decomposition of the literal positive coprime sum. -/
theorem completedProfileSum_eq_natural_tsum {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (ha : 0 < a) {c : ℕ} (hc : 0 < c) (k : ℤ) :
    completedProfileSum W₂ W₄ a b c k = ∑' m : ℕ, coprimeProfileTerm W₂ W₄ a b c k m := by
  let _ : NeZero c := ⟨hc.ne'⟩
  have hs : Summable (coprimeProfileTerm W₂ W₄ a b c k) :=
    summable_of_hasFiniteSupport
      (coprimeProfileTerm_hasFiniteSupport (W₄ := W₄) (b := b) h₂ ha c k)
  let e := Nat.residueClassesEquiv c
  have hprod : Summable (fun z : ZMod c × ℕ =>
      coprimeProfileTerm W₂ W₄ a b c k (e.symm z)) := hs.comp_injective e.symm.injective
  have heq (z : ZMod c) (j : ℕ) :
      coprimeProfileTerm W₂ W₄ a b c k (e.symm (z,j)) =
      if z.val.Coprime c then ePhase ((k:ℝ)*(inverseRepresentative z.val c:ℝ)/(c:ℝ))*
        poissonProfile W₂ W₄ a b ((z.val:ℝ)+(c:ℝ)*j) else 0 := by
    change coprimeProfileTerm W₂ W₄ a b c k (z.val+c*j) = _
    unfold coprimeProfileTerm
    simp only [Nat.coprime_add_mul_left_left,inverseRepresentative_add_modulus]
    split_ifs
    · push_cast
      ring
    · rfl
  symm
  calc _ = ∑' z : ZMod c × ℕ, coprimeProfileTerm W₂ W₄ a b c k (e.symm z) :=
      (e.symm.tsum_eq _).symm
    _ = ∑' z : ZMod c, ∑' j : ℕ, coprimeProfileTerm W₂ W₄ a b c k (e.symm (z,j)) :=
      hprod.tsum_prod
    _ = ∑ z : ZMod c, if z.val.Coprime c then
      ePhase ((k:ℝ)*(inverseRepresentative z.val c:ℝ)/(c:ℝ))*
        ∑' j : ℤ, poissonProfile W₂ W₄ a b ((z.val:ℝ)+(c:ℝ)*j) else 0 := by
      rw [tsum_fintype]
      apply sum_congr rfl
      intro z _
      simp_rw [heq]
      by_cases hz : z.val.Coprime c
      · simp only [ite_eq_left hz,tsum_mul_left]
        exact (congrArg (fun w : ℂ => ePhase ((k:ℝ)*(inverseRepresentative z.val c:ℝ)/(c:ℝ))*w)
            (profile_lattice_nonnegative (W₄ := W₄) (b := b) h₂ ha hc (ZMod.val_lt z))).symm
      · simp [hz]
    _ = ∑ x ∈ range c, if x.Coprime c then
      ePhase ((k:ℝ)*(inverseRepresentative x c:ℝ)/(c:ℝ))*
        ∑' j : ℤ, poissonProfile W₂ W₄ a b ((x:ℝ)+(c:ℝ)*j) else 0 := zmod_sum_vals (c := c) (fun x : ℕ =>
      if x.Coprime c then ePhase ((k:ℝ)*(inverseRepresentative x c:ℝ)/(c:ℝ))*
        ∑' j : ℤ, poissonProfile W₂ W₄ a b ((x:ℝ)+(c:ℝ)*j) else 0)
    _ = _ := by rw [completedProfileSum,Finset.sum_filter]

/-- Smooth completion directly for a finite sum over positive integers. -/
theorem Estermann.finite_smooth_profile_completion
    {W₂ W₄ : ℝ → ℝ} {a b V K : ℝ} {bounds : ℕ → ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (hV : 0 < V) (ha : 1 ≤ a*V) (hb : 0 ≤ b*V) (haK : a*V ≤ K) (hbK : b*V ≤ K)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j)
    {c : ℕ} (hc : 0 < c) (k : ℤ) :
    ‖∑ m ∈ Icc 1 ⌊2/a⌋₊, coprimeProfileTerm W₂ W₄ a b c k m‖ ≤
      ((2+2*Real.pi)*profileFourierBound bounds K 2)*
        twoAdicWeight c*(c.divisors.card:ℝ)*(c:ℝ)^(1/2:ℝ)*(Nat.gcd k.natAbs c:ℝ)^(1/2:ℝ)*
          (1+V/(c:ℝ)) := by
  have hap : 0 < a := by nlinarith
  have hfin : (∑' m : ℕ, coprimeProfileTerm W₂ W₄ a b c k m) =
      ∑ m ∈ Icc 1 ⌊2/a⌋₊, coprimeProfileTerm W₂ W₄ a b c k m := by
    apply tsum_eq_sum
    intro m hm
    by_contra hne
    have hW : W₂ (a*m) ≠ 0 := by
      intro hz
      exact hne (by simp [coprimeProfileTerm,poissonProfile,hz])
    have hs := h₂.2 (subset_tsupport _ hW)
    apply hm
    refine Finset.mem_Icc.mpr ⟨?_,(Nat.le_floor_iff (by positivity : 0 ≤ 2/a)).mpr ?_⟩
    · by_contra hh
      have hm₀ : m = 0 := by omega
      simp only [hm₀,Nat.cast_zero,mul_zero] at hs
      linarith [hs.1]
    · apply (le_div_iff₀ hap).mpr
      nlinarith [hs.2]
  rw [← hfin,← completedProfileSum_eq_natural_tsum h₂ hap hc]
  exact Estermann.smooth_profile_completion h₂ h₄ hV ha hb haK hbK hder₂ hder₄ hc k

end
end DivisorProof



/-! ## Inverse Phases

Exact inverse phases and preservation of the averaged gcd factor in the
shortened-variable Weil calculation. Modulus one is included throughout.
-/
namespace DivisorProof
open Real Classical
noncomputable section
set_option maxHeartbeats 1600000

theorem ePhase_int (n : ℤ) : ePhase (n:ℝ) = 1 := by
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  unfold ePhase
  congr 1
  push_cast
  ring

theorem ePhase_div_eq_of_modEq {c : ℕ} (hc : 0 < c) {u v : ℤ}
    (huv : u ≡ v [ZMOD c]) : ePhase ((u:ℝ)/(c:ℝ)) = ePhase ((v:ℝ)/(c:ℝ)) := by
  have hcp : (0:ℝ) < c := by exact_mod_cast hc
  obtain ⟨j,hj⟩ := Int.modEq_iff_dvd.mp huv
  have hj' : (v:ℝ)-(u:ℝ) = (c:ℝ)*j := by exact_mod_cast hj
  have heq : (v:ℝ)/(c:ℝ) = (u:ℝ)/(c:ℝ)+(j:ℝ) := by
    apply (div_eq_iff hcp.ne').mpr
    field_simp
    nlinarith
  rw [heq,ePhase_add,ePhase_int,mul_one]

theorem inverseRepresentative_coprime {r c : ℕ} (hc : 0 < c) (hr : r.Coprime c) :
    (inverseRepresentative r c).Coprime c :=
  (ZMod.isUnit_iff_coprime _ _).mp
    (IsUnit.of_mul_eq_one (r:ZMod c) (inverseRepresentative_mul hc.ne' hr))

theorem inverseRepresentative_product {r v c : ℕ} (hc : 0 < c)
    (hr : r.Coprime c) (hv : v.Coprime c) :
    (inverseRepresentative (r*v) c : ZMod c) =
      (inverseRepresentative r c : ZMod c)*(inverseRepresentative v c : ZMod c) := by
  have hrv := inverseRepresentative_mul hc.ne' (hr.mul_left hv)
  have hr' := inverseRepresentative_mul hc.ne' hr
  have hv' := inverseRepresentative_mul hc.ne' hv
  have hinv : (r*v:ℕ) *
      ((inverseRepresentative r c : ZMod c)*(inverseRepresentative v c : ZMod c)) = 1 := by
    push_cast
    calc _ = ((inverseRepresentative r c : ZMod c)*(r:ZMod c))*
        ((inverseRepresentative v c : ZMod c)*(v:ZMod c)) := by ring
      _ = _ := by rw [hr',hv']; ring
  calc (inverseRepresentative (r*v) c : ZMod c) =
      (inverseRepresentative (r*v) c : ZMod c)*((r*v:ℕ)*
        ((inverseRepresentative r c : ZMod c)*(inverseRepresentative v c : ZMod c))) := by rw [hinv,mul_one]
    _ = ((inverseRepresentative (r*v) c : ZMod c)*(r*v:ℕ))*
        ((inverseRepresentative r c : ZMod c)*(inverseRepresentative v c : ZMod c)) := by ring
    _ = _ := by rw [hrv,one_mul]

/-- The phase in the actual shortened `v` sum is exactly a standard
incomplete Kloosterman phase with parameter `k * inverse(r)`. -/
theorem inverse_product_phase {r v c : ℕ} (hc : 0 < c)
    (hr : r.Coprime c) (hv : v.Coprime c) (k : ℤ) :
    ePhase ((k:ℝ)*(inverseRepresentative (r*v) c:ℝ)/(c:ℝ)) =
      ePhase ((k:ℝ)*(inverseRepresentative r c:ℝ)*(inverseRepresentative v c:ℝ)/(c:ℝ)) := by
  have hcon : k*(inverseRepresentative (r*v) c:ℤ) ≡
      (k*(inverseRepresentative r c:ℤ))*(inverseRepresentative v c:ℤ) [ZMOD c] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [inverseRepresentative_product hc hr hv]
    ring
  simpa only [Int.cast_mul,Int.cast_natCast] using ePhase_div_eq_of_modEq hc hcon

/-- Multiplying the frequency-shift parameter by the unit inverse of `r`
does not enlarge its gcd with the modulus. -/
theorem inverse_parameter_gcd {r c : ℕ} (hc : 0 < c) (hr : r.Coprime c) (k : ℤ) :
    Nat.gcd (k*(inverseRepresentative r c:ℤ)).natAbs c = Nat.gcd k.natAbs c := by
  rw [Int.natAbs_mul,Int.natAbs_natCast]
  exact (inverseRepresentative_coprime hc hr).gcd_mul_right_cancel k.natAbs

end
end DivisorProof



/-! ## Weil Inner

The incomplete Kloosterman estimate for the actual shortened variable:
the coprimality condition is `(rv,c)=1` and the phase is `inverse(rv)`.
Both are reduced to the complete Weil input by proved identities.
-/
namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000

def shortenedWeilTerm (W₂ W₄ : ℝ → ℝ) (a b : ℝ) (r c : ℕ) (k : ℤ) (v : ℕ) : ℂ :=
  if (r*v).Coprime c then poissonProfile W₂ W₄ a b v*
    ePhase ((k:ℝ)*(inverseRepresentative (r*v) c:ℝ)/(c:ℝ)) else 0

theorem shortenedWeilTerm_eq {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    {r c : ℕ} (hc : 0 < c) (hr : r.Coprime c) (k : ℤ) (v : ℕ) :
    shortenedWeilTerm W₂ W₄ a b r c k v =
      coprimeProfileTerm W₂ W₄ a b c (k*(inverseRepresentative r c:ℤ)) v := by
  unfold shortenedWeilTerm coprimeProfileTerm
  by_cases hv : v.Coprime c
  · rw [ite_eq_left (hr.mul_left hv),ite_eq_left hv,inverse_product_phase hc hr hv]
    push_cast
    rfl
  · have hrv : ¬ (r*v).Coprime c := fun h => hv h.coprime_mul_left
    rw [ite_eq_right hrv,ite_eq_right hv]

theorem shortenedWeilTerm_zero_of_not_coprime {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    {r c : ℕ} (hr : ¬ r.Coprime c) (k : ℤ) (v : ℕ) :
    shortenedWeilTerm W₂ W₄ a b r c k v = 0 := by
  simp [shortenedWeilTerm,Nat.coprime_mul_iff_left,hr]

/-- The central smooth `v`-sum estimate in §5.1, for either signed
frequency-shift product `k`, with its original gcd factor intact. -/
theorem Estermann.shortened_inner_bound
    {W₂ W₄ : ℝ → ℝ} {a b V K : ℝ} {bounds : ℕ → ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (hV : 0 < V) (ha : 1 ≤ a*V) (hb : 0 ≤ b*V) (haK : a*V ≤ K) (hbK : b*V ≤ K)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j)
    {r c : ℕ} (hc : 0 < c) (k : ℤ) :
    ‖∑ v ∈ Icc 1 ⌊2/a⌋₊, shortenedWeilTerm W₂ W₄ a b r c k v‖ ≤
      ((2+2*Real.pi)*profileFourierBound bounds K 2)*
        twoAdicWeight c*(c.divisors.card:ℝ)*(c:ℝ)^(1/2:ℝ)*(Nat.gcd k.natAbs c:ℝ)^(1/2:ℝ)*
          (1+V/(c:ℝ)) := by
  by_cases hr : r.Coprime c
  · simp_rw [shortenedWeilTerm_eq hc hr]
    have hbound := Estermann.finite_smooth_profile_completion h₂ h₄ hV ha hb haK hbK
      hder₂ hder₄ hc (k*(inverseRepresentative r c:ℤ))
    simpa only [inverse_parameter_gcd hc hr] using hbound
  · simp only [shortenedWeilTerm_zero_of_not_coprime hr,Finset.sum_const_zero,norm_zero]
    have hb' : ∀ j, 0 ≤ bounds j := fun j => (norm_nonneg _).trans (hder₂ j 0)
    have hconst := profileFourierBound_nonneg hb' (by linarith : 0 ≤ K) 2
    positivity

end
end DivisorProof
