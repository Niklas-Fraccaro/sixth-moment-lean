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
import SixthMoment.Arithmetic.QuadraticDivisor.Reduction.Basic
import Std


namespace DivisorProof
noncomputable section

theorem inverseRepresentative_mul {r c : ℕ} (hc : c ≠ 0) (hcop : r.Coprime c) :
    (inverseRepresentative r c : ZMod c)*(r : ZMod c) = 1 := by
  let _ : NeZero c := ⟨hc⟩
  unfold inverseRepresentative
  rw [ZMod.natCast_zmod_val, mul_comm, ZMod.coe_mul_inv_eq_one _ hcop]

theorem reduced_congruence_iff {r c : ℕ} (hc : c ≠ 0) (hcop : r.Coprime c)
    (m k : ℤ) :
    ((r : ℤ)*m ≡ k [ZMOD c]) ↔
      (m ≡ k*(inverseRepresentative r c : ℤ) [ZMOD c]) := by
  rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  have hinv := inverseRepresentative_mul hc hcop
  constructor
  · intro h
    calc (m : ZMod c) = ((inverseRepresentative r c : ZMod c)*(r : ZMod c))*m := by rw [hinv, one_mul]
      _ = (k : ZMod c)*(inverseRepresentative r c : ZMod c) := by rw [mul_assoc, h]; ring
  · intro h
    rw [h]
    calc (r : ZMod c)*((k : ZMod c)*(inverseRepresentative r c : ZMod c)) =
        ((inverseRepresentative r c : ZMod c)*(r : ZMod c))*k := by ring
      _ = _ := by rw [hinv, one_mul]

theorem reduced_equation_iff {r c : ℕ} (hc : c ≠ 0) (hcop : r.Coprime c)
    (m k : ℤ) :
    (∃ n : ℤ, (r : ℤ)*m - (c : ℤ)*n = k) ↔
      (m ≡ k*(inverseRepresentative r c : ℤ) [ZMOD c]) := by
  rw [← reduced_congruence_iff hc hcop, Int.modEq_iff_dvd]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    nlinarith
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    nlinarith

theorem reduced_modulus_pos (A B : ℕ) (hB : 0 < B) : 0 < B / Nat.gcd A B := by
  exact Nat.div_pos (Nat.le_of_dvd hB (Nat.gcd_dvd_right A B))
    (Nat.gcd_pos_of_pos_right A hB)

theorem reduced_coefficients_coprime (A B : ℕ) (hB : 0 < B) :
    (A / Nat.gcd A B).Coprime (B / Nat.gcd A B) :=
  Nat.gcd_div_gcd_div_gcd_of_pos_right hB

theorem divide_gcd_equation_iff (A B : ℕ) (hB : 0 < B) (m n k : ℤ) :
    (A : ℤ)*m - (B : ℤ)*n = (Nat.gcd A B : ℤ)*k ↔
      ((A / Nat.gcd A B : ℕ) : ℤ)*m - ((B / Nat.gcd A B : ℕ) : ℤ)*n = k := by
  let d := Nat.gcd A B
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.gcd_pos_of_pos_right A hB).ne'
  have hA : (A : ℤ) = (d : ℤ)*(A/d : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)).symm
  have hB' : (B : ℤ) = (d : ℤ)*(B/d : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right A B)).symm
  change (A : ℤ)*m - (B : ℤ)*n = (d : ℤ)*k ↔ _
  rw [hA, hB']
  simpa only [mul_sub, mul_assoc] using
    (mul_left_cancel_iff_of_pos (show (0 : ℤ) < d by exact_mod_cast Nat.gcd_pos_of_pos_right A hB)
      : (d : ℤ)*((A/d : ℕ)*m-(B/d : ℕ)*n) = d*k ↔ _)

theorem original_equation_iff (A B : ℕ) (hB : 0 < B) (m k : ℤ) :
    (∃ n : ℤ, (A : ℤ)*m - (B : ℤ)*n = (Nat.gcd A B : ℤ)*k) ↔
      (m ≡ k*(inverseRepresentative (A/Nat.gcd A B) (B/Nat.gcd A B) : ℤ)
        [ZMOD B/Nat.gcd A B]) := by
  simp_rw [divide_gcd_equation_iff A B hB]
  exact reduced_equation_iff (reduced_modulus_pos A B hB).ne'
    (reduced_coefficients_coprime A B hB) m k

theorem gcd_dvd_signed_shift (A B h : ℕ) (m n : ℤ) (positive : Bool)
    (heq : (A : ℤ)*m-(B : ℤ)*n = if positive then (h : ℤ) else -(h : ℤ)) :
    Nat.gcd A B ∣ h := by
  have hdA : (Nat.gcd A B : ℤ) ∣ (A : ℤ) := by exact_mod_cast Nat.gcd_dvd_left A B
  have hdB : (Nat.gcd A B : ℤ) ∣ (B : ℤ) := by exact_mod_cast Nat.gcd_dvd_right A B
  have hh := dvd_sub (dvd_mul_of_dvd_left hdA m) (dvd_mul_of_dvd_left hdB n)
  rw [heq] at hh
  cases positive <;> simp only [Bool.false_eq_true, ite_false, ite_true, dvd_neg] at hh
  all_goals exact_mod_cast hh

theorem residue_progression_iff (c : ℕ) (m s : ℤ) :
    (m ≡ s [ZMOD c]) ↔ ∃ j : ℤ, m = s+(c : ℤ)*j := by
  rw [Int.modEq_iff_dvd]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨-j, by nlinarith⟩
  · rintro ⟨j, rfl⟩
    exact ⟨-j, by ring⟩

theorem residue_progression_unique {c : ℕ} (hc : c ≠ 0) {m s j k : ℤ}
    (hj : m = s+(c : ℤ)*j) (hk : m = s+(c : ℤ)*k) : j = k := by
  have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast hc
  exact (mul_left_cancel₀ hc') (by linarith)

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set
open scoped BigOperators FourierTransform SchwartzMap ContDiff
noncomputable section
set_option maxHeartbeats 800000

@[simp] theorem ePhase_zero : ePhase 0 = 1 := by simp [ePhase]

theorem norm_ePhase (t : ℝ) : ‖ePhase t‖ = 1 := by
  rw [ePhase, Complex.norm_exp]
  simp

theorem continuous_ePhase : Continuous ePhase := by
  unfold ePhase
  fun_prop

theorem fourier_eq_ePhase (l : ℤ) (t : ℝ) :
    fourier l (t : UnitAddCircle) = ePhase ((l : ℝ)*t) := by
  rw [fourier_coe_apply]
  simp only [ePhase, Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_one, div_one]
  congr 1
  ring

def poissonProfile (W₂ W₄ : ℝ → ℝ) (a b : ℝ) (x : ℝ) : ℂ :=
  (W₂ (a*x) : ℂ)*(W₄ (b*x) : ℂ)

theorem SmoothDyadicWeight.hasCompactSupport {W : ℝ → ℝ} (hW : SmoothDyadicWeight W) :
    HasCompactSupport W :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport W) hW.2

theorem poissonProfile_hasCompactSupport {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (ha : a ≠ 0) :
    HasCompactSupport (poissonProfile W₂ W₄ a b) := by
  have h : HasCompactSupport (fun x : ℝ => W₂ (a*x)) := by
    simpa only [smul_eq_mul] using (SmoothDyadicWeight.hasCompactSupport h₂).comp_smul (c := a) ha
  have hc : HasCompactSupport (fun x : ℝ => (W₂ (a*x) : ℂ)) :=
    h.comp_left (g := Complex.ofReal) (by simp)
  exact hc.mul_right

theorem poissonProfile_contDiff {W₂ W₄ : ℝ → ℝ} (a b : ℝ)
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) :
    ContDiff ℝ ∞ (poissonProfile W₂ W₄ a b) := by
  apply ContDiff.mul
  · exact Complex.ofRealCLM.contDiff.comp (h₂.1.comp (contDiff_const.mul contDiff_id))
  · exact Complex.ofRealCLM.contDiff.comp (h₄.1.comp (contDiff_const.mul contDiff_id))

def poissonSchwartz {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) (ha : a ≠ 0) :
    𝓢(ℝ, ℂ) :=
  (poissonProfile_hasCompactSupport (W₄ := W₄) (b := b) h₂ ha).toSchwartzMap
    (poissonProfile_contDiff a b h₂ h₄)

def poissonCoefficient (W₂ W₄ : ℝ → ℝ) (a b : ℝ) (l : ℤ) : ℂ :=
  ∫ x : ℝ, poissonProfile W₂ W₄ a b x * ePhase ((l : ℝ)*x)

theorem poissonCoefficient_eq_fourier (W₂ W₄ : ℝ → ℝ) (a b : ℝ) (l : ℤ) :
    poissonCoefficient W₂ W₄ a b l = 𝓕 (poissonProfile W₂ W₄ a b) (-l) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ePhase, smul_eq_mul]
  push_cast
  ring_nf

theorem poisson_profile_identity {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) (ha : a ≠ 0) (t : ℝ) :
    (∑' n : ℤ, poissonProfile W₂ W₄ a b (t+n)) =
      ∑' l : ℤ, poissonCoefficient W₂ W₄ a b l * ePhase (-(l : ℝ)*t) := by
  let f := poissonSchwartz (a := a) (b := b) h₂ h₄ ha
  have hfcoe : (f : ℝ → ℂ) = poissonProfile W₂ W₄ a b := rfl
  have hp := f.tsum_eq_tsum_fourier t
  change (∑' n : ℤ, f (t+n)) = _
  rw [hp]
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro l
  simp only [Equiv.neg_apply, SchwartzMap.fourier_coe, hfcoe, Int.cast_neg]
  rw [poissonCoefficient_eq_fourier, fourier_eq_ePhase]
  simp only [Int.cast_neg]

theorem poissonProfile_zero_of_nonpos {W₂ W₄ : ℝ → ℝ} {a b x : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (ha : 0 < a) (hx : x ≤ 0) :
    poissonProfile W₂ W₄ a b x = 0 := by
  have hz : W₂ (a*x) = 0 := by
    by_contra hn
    have hs := h₂.2 (subset_tsupport W₂ hn)
    have hnpos : a*x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hx
    linarith [hs.1]
  simp only [poissonProfile, hz, Complex.ofReal_zero, zero_mul]

theorem poissonCoefficient_eq_positive_integral {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (ha : 0 < a) (l : ℤ) :
    poissonCoefficient W₂ W₄ a b l =
      ∫ x : ℝ in Ioi 0, poissonProfile W₂ W₄ a b x * ePhase ((l : ℝ)*x) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [poissonProfile_zero_of_nonpos h₂ ha (le_of_not_gt hx), zero_mul]

theorem poissonCoefficient_zero {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (ha : 0 < a) :
    poissonCoefficient W₂ W₄ a b 0 =
      ∫ x : ℝ in Ioi 0, (W₂ (a*x) : ℂ)*(W₄ (b*x) : ℂ) := by
  rw [poissonCoefficient_eq_positive_integral h₂ ha]
  simp only [Int.cast_zero, zero_mul, ePhase_zero, mul_one, poissonProfile]

theorem poissonCoefficient_integrable {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) (ha : a ≠ 0) (l : ℤ) :
    Integrable (fun x : ℝ => poissonProfile W₂ W₄ a b x*ePhase ((l : ℝ)*x)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (poissonProfile_contDiff a b h₂ h₄).continuous.mul
      (continuous_ePhase.comp (continuous_const.mul continuous_id))
  · exact (poissonProfile_hasCompactSupport (b := b) h₂ ha).mul_right

theorem poissonCoefficient_summable {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) (ha : a ≠ 0) :
    Summable (poissonCoefficient W₂ W₄ a b) := by
  let f := poissonSchwartz (a := a) (b := b) h₂ h₄ ha
  have hfcoe : (f : ℝ → ℂ) = poissonProfile W₂ W₄ a b := rfl
  have hs : Summable (fun n : ℤ => (𝓕 f) (n : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 f).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  have hn := hs.comp_injective (Equiv.neg ℤ).injective
  apply hn.congr
  intro l
  change (𝓕 f) ((-l : ℤ) : ℝ) = poissonCoefficient W₂ W₄ a b l
  rw [SchwartzMap.fourier_coe, hfcoe, poissonCoefficient_eq_fourier]
  simp only [Int.cast_neg]

theorem poissonCoefficient_norm_summable {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) (ha : a ≠ 0) :
    Summable (fun l : ℤ => ‖poissonCoefficient W₂ W₄ a b l‖) :=
  (poissonCoefficient_summable h₂ h₄ ha).norm

theorem poissonSeries_summable {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) (ha : a ≠ 0) (t : ℝ) :
    Summable (fun l : ℤ => poissonCoefficient W₂ W₄ a b l * ePhase (-(l : ℝ)*t)) := by
  apply summable_norm_iff.mp
  simpa only [norm_mul, norm_ePhase, mul_one] using poissonCoefficient_norm_summable h₂ h₄ ha

theorem poisson_profile_nonzero_identity {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) (ha : 0 < a) (t : ℝ) :
    (∑' n : ℤ, poissonProfile W₂ W₄ a b (t+n)) -
      (∫ x : ℝ in Ioi 0, (W₂ (a*x) : ℂ)*(W₄ (b*x) : ℂ)) =
      ∑' l : ℤ, if l = 0 then 0 else
        poissonCoefficient W₂ W₄ a b l * ePhase (-(l : ℝ)*t) := by
  rw [poisson_profile_identity h₂ h₄ ha.ne' t,
    (poissonSeries_summable h₂ h₄ ha.ne' t).tsum_eq_add_tsum_ite 0]
  simp only [Int.cast_zero, neg_zero, zero_mul, ePhase_zero, mul_one]
  rw [poissonCoefficient_zero h₂ ha]
  abel

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set Finset
open scoped BigOperators ContDiff FourierTransform SchwartzMap
noncomputable section
set_option maxHeartbeats 800000

def profileDerivativeBound (bounds : ℕ → ℝ) (K : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range (j+1), (j.choose i : ℝ)*(K^i*bounds i)*(K^(j-i)*bounds (j-i))

theorem profileDerivativeBound_nonneg {bounds : ℕ → ℝ} {K : ℝ}
    (hb : ∀ j, 0 ≤ bounds j) (hK : 0 ≤ K) (j : ℕ) :
    0 ≤ profileDerivativeBound bounds K j := by
  unfold profileDerivativeBound
  apply sum_nonneg
  intro i hi
  have hi0 := hb i
  have hji0 := hb (j-i)
  positivity

def realPoissonProfile (W₂ W₄ : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  fun x => W₂ (a*x)*W₄ (b*x)

theorem realPoissonProfile_contDiff {W₂ W₄ : ℝ → ℝ} (a b : ℝ)
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) :
    ContDiff ℝ ∞ (realPoissonProfile W₂ W₄ a b) :=
  (h₂.1.comp (contDiff_const.mul contDiff_id)).mul
    (h₄.1.comp (contDiff_const.mul contDiff_id))

theorem scaled_weight_derivative_bound {W : ℝ → ℝ} {a K : ℝ} {bounds : ℕ → ℝ}
    (hW : SmoothDyadicWeight W) (ha : 0 ≤ a) (haK : a ≤ K)
    (hb : ∀ j x, ‖iteratedDeriv j W x‖ ≤ bounds j) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (fun x => W (a*x)) x‖ ≤ K^j*bounds j := by
  rw [iteratedDeriv_comp_const_mul (hW.1.of_le (by exact_mod_cast le_top)) a]
  dsimp only
  rw [norm_mul, norm_pow, Real.norm_of_nonneg ha]
  exact mul_le_mul (pow_le_pow_left₀ ha haK j) (hb j (a*x))
    (norm_nonneg _) (pow_nonneg (ha.trans haK) j)

theorem realPoissonProfile_derivative_bound {W₂ W₄ : ℝ → ℝ} {a b K : ℝ}
    {bounds : ℕ → ℝ} (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haK : a ≤ K) (hbK : b ≤ K)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (realPoissonProfile W₂ W₄ a b) x‖ ≤ profileDerivativeBound bounds K j := by
  have hc₂ : ContDiff ℝ j (fun x : ℝ => W₂ (a*x)) :=
    (h₂.1.comp (contDiff_const.mul contDiff_id)).of_le (by exact_mod_cast le_top)
  have hc₄ : ContDiff ℝ j (fun x : ℝ => W₄ (b*x)) :=
    (h₄.1.comp (contDiff_const.mul contDiff_id)).of_le (by exact_mod_cast le_top)
  unfold realPoissonProfile
  rw [iteratedDeriv_fun_mul hc₂.contDiffAt hc₄.contDiffAt]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  have hK0 : 0 ≤ K := ha.trans haK
  have hbi : 0 ≤ bounds i := (norm_nonneg _).trans (hder₂ i 0)
  simp only [norm_mul, Real.norm_natCast]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (scaled_weight_derivative_bound h₂ ha haK hder₂ i x)
      (Nat.cast_nonneg _))
    (scaled_weight_derivative_bound h₄ hb hbK hder₄ (j-i) x)
    (norm_nonneg _) (by positivity)

theorem poissonProfile_norm_iteratedFDeriv {W₂ W₄ : ℝ → ℝ} (a b : ℝ)
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) (j : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ j (poissonProfile W₂ W₄ a b) x‖ =
      ‖iteratedDeriv j (realPoissonProfile W₂ W₄ a b) x‖ := by
  have heq : poissonProfile W₂ W₄ a b =
      Complex.ofRealLI ∘ realPoissonProfile W₂ W₄ a b := by
    funext y
    simp [poissonProfile, realPoissonProfile, Complex.ofReal_mul]
  rw [heq, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    (realPoissonProfile_contDiff a b h₂ h₄).contDiffAt (by exact_mod_cast le_top)]
  exact norm_iteratedFDeriv_eq_norm_iteratedDeriv

theorem poissonProfile_tsupport_subset {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (ha : 1 ≤ a) :
    tsupport (poissonProfile W₂ W₄ a b) ⊆ Icc 0 2 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hx₂ : W₂ (a*x) ≠ 0 := by
    intro heq
    apply hx
    simp [poissonProfile, heq]
  have hs := h₂.2 (subset_tsupport W₂ hx₂)
  have hap : 0 < a := by linarith
  have hxp : 0 ≤ x := by nlinarith [hs.1]
  exact ⟨hxp, by nlinarith [hs.2]⟩

theorem poissonProfile_derivative_integrable {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) (ha : a ≠ 0) (j : ℕ) :
    Integrable (iteratedFDeriv ℝ j (poissonProfile W₂ W₄ a b)) :=
  ((poissonProfile_contDiff a b h₂ h₄).continuous_iteratedFDeriv (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    ((poissonProfile_hasCompactSupport (W₄ := W₄) (b := b) h₂ ha).iteratedFDeriv j)

theorem poissonProfile_derivative_integral_le {W₂ W₄ : ℝ → ℝ} {a b K : ℝ}
    {bounds : ℕ → ℝ} (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (ha : 1 ≤ a) (hb : 0 ≤ b) (haK : a ≤ K) (hbK : b ≤ K)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j) (j : ℕ) :
    (∫ x : ℝ, ‖iteratedFDeriv ℝ j (poissonProfile W₂ W₄ a b) x‖) ≤
      2*profileDerivativeBound bounds K j := by
  have hap : 0 < a := by linarith
  have hbound (x : ℝ) : ‖iteratedFDeriv ℝ j (poissonProfile W₂ W₄ a b) x‖ ≤
      profileDerivativeBound bounds K j := by
    rw [poissonProfile_norm_iteratedFDeriv a b h₂ h₄]
    exact realPoissonProfile_derivative_bound h₂ h₄ hap.le hb haK hbK hder₂ hder₄ j x
  have hint := (poissonProfile_derivative_integrable (b := b) h₂ h₄ hap.ne' j).norm
  have hset : (∫ x : ℝ in Icc 0 2, ‖iteratedFDeriv ℝ j (poissonProfile W₂ W₄ a b) x‖) =
      ∫ x : ℝ, ‖iteratedFDeriv ℝ j (poissonProfile W₂ W₄ a b) x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hout : x ∉ tsupport (poissonProfile W₂ W₄ a b) :=
      fun hx' => hx (poissonProfile_tsupport_subset h₂ ha hx')
    have hfzero : iteratedFDeriv ℝ j (poissonProfile W₂ W₄ a b) x = 0 := by
      by_contra hn
      exact hout (support_iteratedFDeriv_subset j hn)
    exact norm_eq_zero.mpr hfzero
  rw [← hset]
  calc _ ≤ ∫ x : ℝ in Icc 0 2, profileDerivativeBound bounds K j :=
      setIntegral_mono_on hint.integrableOn (continuous_const.integrableOn_Icc)
        measurableSet_Icc (fun x _ => hbound x)
    _ = 2*profileDerivativeBound bounds K j := by simp [mul_comm]

theorem poissonProfile_fourier_moment_le {W₂ W₄ : ℝ → ℝ} {a b K : ℝ}
    {bounds : ℕ → ℝ} (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (ha : 1 ≤ a) (hb : 0 ≤ b) (haK : a ≤ K) (hbK : b ≤ K)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j) (J : ℕ) (w : ℝ) :
    ‖w‖^J*‖𝓕 (poissonProfile W₂ W₄ a b) w‖ ≤
      2^J * ∑ j ∈ range (J+1), 2*profileDerivativeBound bounds K j := by
  have hap : 0 < a := by linarith
  have hint : ∀ k n : ℕ, (k : ℕ∞) ≤ 0 → (n : ℕ∞) ≤ ⊤ →
      Integrable (fun x : ℝ => ‖x‖^k*‖iteratedFDeriv ℝ n (poissonProfile W₂ W₄ a b) x‖) := by
    intro k n hk _
    have hk0 : k = 0 := by exact_mod_cast (le_antisymm hk bot_le)
    subst k
    simpa only [pow_zero, one_mul] using
      (poissonProfile_derivative_integrable (b := b) h₂ h₄ hap.ne' n).norm
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (K := 0) (N := ⊤) (k := 0) (n := J)
    (poissonProfile_contDiff a b h₂ h₄) hint le_rfl le_top w
  simp only [norm_iteratedFDeriv_zero, pow_zero, Nat.cast_zero, zero_add, mul_zero, one_mul,
    range_one, sum_product, sum_singleton] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_le_sum fun j _ =>
    poissonProfile_derivative_integral_le h₂ h₄ ha hb haK hbK hder₂ hder₄ j

def profileFourierBound (bounds : ℕ → ℝ) (K : ℝ) (J : ℕ) : ℝ :=
  2^J * (2*profileDerivativeBound bounds K 0 +
    2^J * ∑ j ∈ range (J+1), 2*profileDerivativeBound bounds K j)

theorem profileFourierBound_nonneg {bounds : ℕ → ℝ} {K : ℝ}
    (hb : ∀ j, 0 ≤ bounds j) (hK : 0 ≤ K) (J : ℕ) :
    0 ≤ profileFourierBound bounds K J := by
  unfold profileFourierBound
  have hzero := profileDerivativeBound_nonneg hb hK 0
  have hsum : 0 ≤ ∑ j ∈ range (J+1), 2*profileDerivativeBound bounds K j :=
    sum_nonneg fun j _ => mul_nonneg (by norm_num) (profileDerivativeBound_nonneg hb hK j)
  positivity

theorem poissonProfile_fourier_decay {W₂ W₄ : ℝ → ℝ} {a b K : ℝ}
    {bounds : ℕ → ℝ} (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (ha : 1 ≤ a) (hb : 0 ≤ b) (haK : a ≤ K) (hbK : b ≤ K)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j) (J : ℕ) (w : ℝ) :
    ‖𝓕 (poissonProfile W₂ W₄ a b) w‖ ≤
      profileFourierBound bounds K J / (1+‖w‖)^J := by
  have hK : 0 ≤ K := (by linarith : (0 : ℝ) ≤ a).trans haK
  have hbounds (j : ℕ) : 0 ≤ bounds j := (norm_nonneg _).trans (hder₂ j 0)
  have hz := profileDerivativeBound_nonneg hbounds hK 0
  have hsum : 0 ≤ ∑ j ∈ range (J+1), 2*profileDerivativeBound bounds K j :=
    sum_nonneg fun j _ => mul_nonneg (by norm_num) (profileDerivativeBound_nonneg hbounds hK j)
  have hzero : ‖𝓕 (poissonProfile W₂ W₄ a b) w‖ ≤
      2*profileDerivativeBound bounds K 0 := by
    simpa only [pow_zero, one_mul, zero_add, range_one, sum_singleton] using
      poissonProfile_fourier_moment_le h₂ h₄ ha hb haK hbK hder₂ hder₄ 0 w
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+‖w‖) J)).mpr
  rw [mul_comm]
  by_cases hw : ‖w‖ ≤ 1
  · calc (1+‖w‖)^J*‖𝓕 (poissonProfile W₂ W₄ a b) w‖ ≤
        2^J*(2*profileDerivativeBound bounds K 0) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) J) hzero
            (norm_nonneg _) (by positivity)
      _ ≤ profileFourierBound bounds K J := by
        unfold profileFourierBound
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (mul_nonneg (by positivity) hsum)) (by positivity)
  · have hm := poissonProfile_fourier_moment_le h₂ h₄ ha hb haK hbK hder₂ hder₄ J w
    calc (1+‖w‖)^J*‖𝓕 (poissonProfile W₂ W₄ a b) w‖ ≤
        (2*‖w‖)^J*‖𝓕 (poissonProfile W₂ W₄ a b) w‖ := by
          gcongr
          linarith
      _ = 2^J*(‖w‖^J*‖𝓕 (poissonProfile W₂ W₄ a b) w‖) := by rw [mul_pow]; ring
      _ ≤ 2^J*(2^J*∑ j ∈ range (J+1), 2*profileDerivativeBound bounds K j) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ profileFourierBound bounds K J := by
        unfold profileFourierBound
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (mul_nonneg (by norm_num) hz)) (by positivity)

theorem poissonCoefficient_rescale (W₂ W₄ : ℝ → ℝ) (a b : ℝ)
    {r : ℝ} (hr : 0 < r) (l : ℤ) :
    poissonCoefficient W₂ W₄ a b l =
      (r : ℂ)*𝓕 (poissonProfile W₂ W₄ (a*r) (b*r)) (-(l : ℝ)*r) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h := Measure.integral_comp_mul_left
    (fun x : ℝ => poissonProfile W₂ W₄ a b x*ePhase ((l : ℝ)*x)) r
  have heq : (fun x : ℝ =>
      Complex.exp ((↑(-2*Real.pi*x*(-(l : ℝ)*r)) : ℂ)*Complex.I) •
        poissonProfile W₂ W₄ (a*r) (b*r) x) =
      (fun x : ℝ => poissonProfile W₂ W₄ a b (r*x)*ePhase ((l : ℝ)*(r*x))) := by
    funext x
    have hexp : Complex.exp ((↑(-2*Real.pi*x*(-(l : ℝ)*r)) : ℂ)*Complex.I) =
        ePhase ((l : ℝ)*(r*x)) := by
      unfold ePhase
      congr 1
      push_cast
      ring
    rw [hexp]
    simp only [poissonProfile, smul_eq_mul, mul_assoc]
    ring
  rw [heq]
  change poissonCoefficient W₂ W₄ a b l = (r : ℂ)*_
  rw [h, abs_of_pos (inv_pos.mpr hr), RCLike.real_smul_eq_coe_mul]
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  change poissonCoefficient W₂ W₄ a b l =
    (r : ℂ)*(((r⁻¹ : ℝ) : ℂ)*poissonCoefficient W₂ W₄ a b l)
  rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hrc, one_mul]

theorem poissonCoefficient_decay {W₂ W₄ : ℝ → ℝ} {a b r K : ℝ}
    {bounds : ℕ → ℝ} (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (hr : 0 < r) (ha : 1 ≤ a*r) (hb : 0 ≤ b*r) (haK : a*r ≤ K) (hbK : b*r ≤ K)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j) (J : ℕ) (l : ℤ) :
    ‖poissonCoefficient W₂ W₄ a b l‖ ≤
      r*profileFourierBound bounds K J / (1+|(l : ℝ)| * r)^J := by
  rw [poissonCoefficient_rescale W₂ W₄ a b hr l, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hr.le]
  have h := poissonProfile_fourier_decay h₂ h₄ ha hb haK hbK hder₂ hder₄ J (-(l : ℝ)*r)
  simpa only [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos hr, mul_div_assoc] using
    mul_le_mul_of_nonneg_left h hr.le

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set Classical
open scoped BigOperators FourierTransform
noncomputable section
set_option maxHeartbeats 800000

theorem residue_tsum_eq_progression (f : ℤ → ℂ) {c : ℕ} (hc : c ≠ 0) (s : ℤ) :
    (∑' m : ℤ, if m ≡ s [ZMOD c] then f m else 0) =
      ∑' j : ℤ, f (s+(c : ℤ)*j) := by
  have hinj : Function.Injective (fun j : ℤ => s+(c : ℤ)*j) := by
    intro j k heq
    exact (mul_left_cancel₀ (show (c : ℤ) ≠ 0 by exact_mod_cast hc)) (by linarith)
  have hs : Function.support (fun m : ℤ => if m ≡ s [ZMOD c] then f m else 0) ⊆
      Set.range (fun j : ℤ => s+(c : ℤ)*j) := by
    intro m hm
    have hcon : m ≡ s [ZMOD c] := by
      by_contra hn
      exact hm (by simp only [ite_eq_right hn])
    obtain ⟨j, hj⟩ := (residue_progression_iff c m s).mp hcon
    exact ⟨j, hj.symm⟩
  rw [← hinj.tsum_eq hs]
  apply tsum_congr
  intro j
  exact ite_eq_left ((residue_progression_iff c (s+(c : ℤ)*j) s).mpr ⟨j, rfl⟩)

theorem poisson_residue_identity {W₂ W₄ : ℝ → ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (r c : ℕ) (hc : 0 < c) {M N : ℝ} (hM : 0 < M) (_hN : 0 < N) (k : ℤ) :
    (∑' m : ℤ, if m ≡ k*(inverseRepresentative r c : ℤ) [ZMOD c] then
      (W₂ ((m : ℝ)/M) : ℂ)*(W₄ ((r : ℝ)*m/((c : ℝ)*N)) : ℂ) else 0) =
      ∑' l : ℤ, poissonCoefficient W₂ W₄ ((c : ℝ)/M) ((r : ℝ)/N) l *
        ePhase (-(l : ℝ)*((k : ℝ)*(inverseRepresentative r c : ℝ)/(c : ℝ))) := by
  rw [residue_tsum_eq_progression _ hc.ne']
  have hcp : (0 : ℝ) < c := by exact_mod_cast hc
  have heq (j : ℤ) :
      (W₂ (((k*(inverseRepresentative r c : ℤ)+(c : ℤ)*j : ℤ) : ℝ)/M) : ℂ)*
        (W₄ ((r : ℝ)*((k*(inverseRepresentative r c : ℤ)+(c : ℤ)*j : ℤ) : ℝ)/
          ((c : ℝ)*N)) : ℂ) =
      poissonProfile W₂ W₄ ((c : ℝ)/M) ((r : ℝ)/N)
        ((k : ℝ)*(inverseRepresentative r c : ℝ)/(c : ℝ)+j) := by
    unfold poissonProfile
    push_cast
    congr 2 <;> field_simp
  simp_rw [heq]
  exact poisson_profile_identity h₂ h₄ (div_pos hcp hM).ne' _

theorem poisson_original_equation_identity {W₂ W₄ : ℝ → ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (A B : ℕ) (hB : 0 < B) {M N : ℝ} (hM : 0 < M) (hN : 0 < N) (k : ℤ) :
    (∑' m : ℤ, if ∃ n : ℤ, (A : ℤ)*m-(B : ℤ)*n = (Nat.gcd A B : ℤ)*k then
      (W₂ ((m : ℝ)/M) : ℂ)*
        (W₄ (((A/Nat.gcd A B : ℕ) : ℝ)*m/(((B/Nat.gcd A B : ℕ) : ℝ)*N)) : ℂ)
      else 0) =
      ∑' l : ℤ, poissonCoefficient W₂ W₄ (((B/Nat.gcd A B : ℕ) : ℝ)/M)
        (((A/Nat.gcd A B : ℕ) : ℝ)/N) l *
        ePhase (-(l : ℝ)*((k : ℝ)*
          (inverseRepresentative (A/Nat.gcd A B) (B/Nat.gcd A B) : ℝ)/
            ((B/Nat.gcd A B : ℕ) : ℝ))) := by
  simp_rw [original_equation_iff A B hB]
  exact poisson_residue_identity h₂ h₄ _ _ (reduced_modulus_pos A B hB) hM hN k

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set Finset
open scoped BigOperators ContDiff FourierTransform
noncomputable section
set_option maxHeartbeats 800000

def inverseSquareMass : ℝ := ∑' l : ℤ, 1/(l : ℝ)^2

theorem inverseSquare_summable : Summable (fun l : ℤ => 1/(l : ℝ)^2) :=
  Real.summable_one_div_int_pow.mpr (by norm_num)

theorem inverseSquareMass_nonneg : 0 ≤ inverseSquareMass :=
  tsum_nonneg fun _ => div_nonneg zero_le_one (sq_nonneg _)

theorem scaled_decay_tail_le {C r L : ℝ} (hC : 0 ≤ C) (hr : 0 < r) (hL : 0 ≤ L)
    (J : ℕ) (l : ℤ) (hl : L < |(l : ℝ)|) :
    r*C/(1+|(l : ℝ)| * r)^(J+2) ≤
      (C/(r*(1+L*r)^J))*(1/(l : ℝ)^2) := by
  have hlp : 0 < |(l : ℝ)| := hL.trans_lt hl
  have hl0 : (l : ℝ) ≠ 0 := abs_pos.mp hlp
  have hu : 0 < 1+|(l : ℝ)| * r := by positivity
  have hv : 0 < 1+L*r := by positivity
  have hp : (1+L*r)^J ≤ (1+|(l : ℝ)| * r)^J :=
    pow_le_pow_left₀ hv.le (by nlinarith) J
  have hs : (|(l : ℝ)| * r)^2 ≤ (1+|(l : ℝ)| * r)^2 := by
    nlinarith [mul_pos hlp hr]
  have hd : (|(l : ℝ)| * r)^2*(1+L*r)^J ≤ (1+|(l : ℝ)| * r)^(J+2) := by
    rw [pow_add]
    exact (mul_le_mul hs hp (pow_nonneg hv.le J) (sq_nonneg _)).trans_eq (mul_comm _ _)
  calc _ ≤ r*C/((|(l : ℝ)| * r)^2*(1+L*r)^J) :=
      div_le_div_of_nonneg_left (mul_nonneg hr.le hC) (by positivity) hd
    _ = (C/(r*(1+L*r)^J))*(1/(l : ℝ)^2) := by
      rw [mul_pow, sq_abs]
      field_simp

theorem fourier_tail_bound {f : ℤ → ℂ} {C r L : ℝ}
    (hC : 0 ≤ C) (hr : 0 < r) (hL : 0 ≤ L) (J : ℕ)
    (hdecay : ∀ l, ‖f l‖ ≤ r*C/(1+|(l : ℝ)| * r)^(J+2)) :
    Summable (fun l : ℤ => if L < |(l : ℝ)| then f l else 0) ∧
      ‖∑' l : ℤ, if L < |(l : ℝ)| then f l else 0‖ ≤
        (C/(r*(1+L*r)^J))*inverseSquareMass := by
  have hc : 0 ≤ C/(r*(1+L*r)^J) := by positivity
  have hm := inverseSquare_summable.mul_left (C/(r*(1+L*r)^J))
  have hp (l : ℤ) : ‖(if L < |(l : ℝ)| then f l else 0 : ℂ)‖ ≤
      (C/(r*(1+L*r)^J))*(1/(l : ℝ)^2) := by
    split_ifs with hl
    · exact (hdecay l).trans (scaled_decay_tail_le hC hr hL J l hl)
    · simpa only [norm_zero] using mul_nonneg hc (div_nonneg zero_le_one (sq_nonneg _))
  have hn : Summable (fun l : ℤ => ‖(if L < |(l : ℝ)| then f l else 0 : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun l => norm_nonneg _) hp hm
  refine ⟨summable_norm_iff.mp hn, (norm_tsum_le_tsum_norm hn).trans ?_⟩
  calc _ ≤ ∑' l : ℤ, (C/(r*(1+L*r)^J))*(1/(l : ℝ)^2) :=
      hn.tsum_le_tsum hp hm
    _ = (C/(r*(1+L*r)^J))*inverseSquareMass := by rw [tsum_mul_left]; rfl

def frequencySet (L : ℝ) : Finset ℤ := Icc (-⌊L⌋) ⌊L⌋

theorem mem_frequencySet (L : ℝ) (l : ℤ) :
    l ∈ frequencySet L ↔ |(l : ℝ)| ≤ L := by
  have hn : -⌊L⌋ ≤ l ↔ -l ≤ ⌊L⌋ := by omega
  simp only [frequencySet, Finset.mem_Icc, hn, Int.le_floor, Int.cast_neg, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem fourier_split_finite {f : ℤ → ℂ} (hf : Summable f) (L : ℝ) :
    (∑' l : ℤ, f l) - (∑ l ∈ frequencySet L, f l) =
      ∑' l : ℤ, if L < |(l : ℝ)| then f l else 0 := by
  have hs : Summable (fun l : ℤ => if |(l : ℝ)| ≤ L then f l else 0) :=
    summable_of_ne_finset_zero (s := frequencySet L) fun l hl =>
      ite_eq_right (fun h => hl ((mem_frequencySet L l).mpr h))
  have ht : Summable (fun l : ℤ => if L < |(l : ℝ)| then f l else 0) := by
    apply (hf.indicator {l : ℤ | L < |(l : ℝ)|}).congr
    intro l
    by_cases hl : L < |(l : ℝ)| <;> simp [hl]
  have hlow : (∑' l : ℤ, if |(l : ℝ)| ≤ L then f l else 0) =
      ∑ l ∈ frequencySet L, f l := by
    rw [tsum_eq_sum (s := frequencySet L) (fun l hl =>
      ite_eq_right (fun h => hl ((mem_frequencySet L l).mpr h)))]
    apply sum_congr rfl
    intro l hl
    exact ite_eq_left ((mem_frequencySet L l).mp hl)
  have heq : f = (fun l : ℤ => (if |(l : ℝ)| ≤ L then f l else 0) +
      (if L < |(l : ℝ)| then f l else 0)) := by
    funext l
    by_cases h : |(l : ℝ)| ≤ L
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  calc (∑' l : ℤ, f l) - ∑ l ∈ frequencySet L, f l =
      ((∑' l : ℤ, if |(l : ℝ)| ≤ L then f l else 0) +
        ∑' l : ℤ, if L < |(l : ℝ)| then f l else 0) - ∑ l ∈ frequencySet L, f l := by
          congr 1
          conv_lhs => rw [heq]
          exact hs.tsum_add ht
    _ = _ := by rw [hlow]; abel

theorem fourier_truncation_bound {f : ℤ → ℂ} {C r L : ℝ}
    (hf : Summable f) (hC : 0 ≤ C) (hr : 0 < r) (hL : 0 ≤ L) (J : ℕ)
    (hdecay : ∀ l, ‖f l‖ ≤ r*C/(1+|(l : ℝ)| * r)^(J+2)) :
    ‖(∑' l : ℤ, f l) - ∑ l ∈ frequencySet L, f l‖ ≤
      (C/(r*(1+L*r)^J))*inverseSquareMass := by
  rw [fourier_split_finite hf]
  exact (fourier_tail_bound hC hr hL J hdecay).2

theorem cutoff_summable (χ : ℝ → ℝ) (f : ℤ → ℂ) {L : ℝ} (hL : 0 < L)
    (hχzero : ∀ x, 2 ≤ |x| → χ x = 0) :
    Summable (fun l : ℤ => (χ ((l : ℝ)/L) : ℂ)*f l) := by
  apply summable_of_ne_finset_zero (s := frequencySet (2*L))
  intro l hl
  have hlarge : 2*L < |(l : ℝ)| := not_le.mp (fun h => hl ((mem_frequencySet _ _).mpr h))
  have hx : 2 ≤ |(l : ℝ)/L| := by
    rw [abs_div, abs_of_pos hL]
    exact (le_div_iff₀ hL).mpr hlarge.le
  rw [hχzero _ hx, Complex.ofReal_zero, zero_mul]

theorem cutoff_tsum_eq_sum (χ : ℝ → ℝ) (f : ℤ → ℂ) {L : ℝ} (hL : 0 < L)
    (hχzero : ∀ x, 2 ≤ |x| → χ x = 0) :
    (∑' l : ℤ, (χ ((l : ℝ)/L) : ℂ)*f l) =
      ∑ l ∈ frequencySet (2*L), (χ ((l : ℝ)/L) : ℂ)*f l := by
  apply tsum_eq_sum
  intro l hl
  have hlarge : 2*L < |(l : ℝ)| := not_le.mp (fun h => hl ((mem_frequencySet _ _).mpr h))
  have hx : 2 ≤ |(l : ℝ)/L| := by
    rw [abs_div, abs_of_pos hL]
    exact (le_div_iff₀ hL).mpr hlarge.le
  rw [hχzero _ hx, Complex.ofReal_zero, zero_mul]

theorem smooth_cutoff_error_bound {f : ℤ → ℂ} {C r L : ℝ}
    (hf : Summable f) (hC : 0 ≤ C) (hr : 0 < r) (hL : 0 < L) (J : ℕ)
    (hdecay : ∀ l, ‖f l‖ ≤ r*C/(1+|(l : ℝ)| * r)^(J+2))
    (χ : ℝ → ℝ) (hχone : ∀ x, |x| ≤ 1 → χ x = 1)
    (hχzero : ∀ x, 2 ≤ |x| → χ x = 0) (hχnorm : ∀ x, |χ x| ≤ 1) :
    ‖(∑' l : ℤ, f l) -
      ∑ l ∈ frequencySet (2*L), (χ ((l : ℝ)/L) : ℂ)*f l‖ ≤
        ((2*C)/(r*(1+L*r)^J))*inverseSquareMass := by
  have hnorm (l : ℤ) : ‖(1-(χ ((l : ℝ)/L) : ℂ))*f l‖ ≤
      r*(2*C)/(1+|(l : ℝ)| * r)^(J+2) := by
    have hc : ‖(1 : ℂ)-(χ ((l : ℝ)/L) : ℂ)‖ ≤ 2 := by
      calc _ ≤ ‖(1 : ℂ)‖+‖(χ ((l : ℝ)/L) : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 := by
          simp only [norm_one, Complex.norm_real, Real.norm_eq_abs]
          linarith [hχnorm ((l : ℝ)/L)]
    calc _ ≤ 2*‖f l‖ := by rw [norm_mul]; exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ 2*(r*C/(1+|(l : ℝ)| * r)^(J+2)) := mul_le_mul_of_nonneg_left (hdecay l) (by norm_num)
      _ = _ := by ring
  have heq (l : ℤ) : f l-(χ ((l : ℝ)/L) : ℂ)*f l =
      if L < |(l : ℝ)| then (1-(χ ((l : ℝ)/L) : ℂ))*f l else 0 := by
    by_cases hl : L < |(l : ℝ)|
    · rw [ite_eq_left hl]; ring
    · have hx : |(l : ℝ)/L| ≤ 1 := by
        rw [abs_div, abs_of_pos hL]
        exact (div_le_iff₀ hL).mpr (by simpa only [one_mul] using not_lt.mp hl)
      rw [ite_eq_right hl, hχone _ hx, Complex.ofReal_one, one_mul, sub_self]
  rw [← cutoff_tsum_eq_sum χ f hL hχzero,
    ← hf.tsum_sub (cutoff_summable χ f hL hχzero)]
  simp_rw [heq]
  exact (fourier_tail_bound (by positivity) hr hL.le J hnorm).2

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 800000

def poissonRadius (q : QuadraticScales) (d : ℝ) : ℝ := d*q.M₂/(q.B*q.N₁)

def poissonLength (q : QuadraticScales) (ρ d : ℝ) : ℝ :=
  Real.sqrt q.mass/(d*q.M₂*q.N₂)*q.mass^(10*ρ)

theorem mass_eq_balanced_product (q : QuadraticScales) :
    q.mass = (q.A*q.M)*(q.B*q.N) := by
  dsimp [QuadraticScales.mass]
  ring

theorem poisson_scale_bounds (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j) :
    1 ≤ q.mass ∧ 1 ≤ q.B*q.N₁ ∧ q.B*q.N₁ ≤ q.mass ∧
      q.M₂ ≤ q.mass ∧ q.A*q.B*q.M₁*q.N₁ ≤ q.mass := by
  have hA : 1 ≤ q.A := h 0
  have hB : 1 ≤ q.B := h 1
  have hM₁ : 1 ≤ q.M₁ := h 2
  have hM₂ : 1 ≤ q.M₂ := h 3
  have hN₁ : 1 ≤ q.N₁ := h 4
  have hN₂ : 1 ≤ q.N₂ := h 5
  have hBN₁ := one_le_mul_of_one_le_of_one_le hB hN₁
  have hAM₁ := one_le_mul_of_one_le_of_one_le hA hM₁
  have hM₂N₂ := one_le_mul_of_one_le_of_one_le hM₂ hN₂
  have hAM₁M₂N₂ := one_le_mul_of_one_le_of_one_le hAM₁ hM₂N₂
  have hAB := one_le_mul_of_one_le_of_one_le hA hB
  have hABM₁N₁ := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hAB hM₁) hN₁
  have hQ : 1 ≤ q.mass := (product_AB_le_mass q h).1.trans (product_AB_le_mass q h).2
  refine ⟨hQ, hBN₁, ?_, ?_, ?_⟩
  · calc q.B*q.N₁ ≤ (q.B*q.N₁)*((q.A*q.M₁)*(q.M₂*q.N₂)) :=
        le_mul_of_one_le_right (by positivity) hAM₁M₂N₂
      _ = q.mass := by dsimp [QuadraticScales.mass, QuadraticScales.M, QuadraticScales.N]; ring
  · calc q.M₂ ≤ q.M₂*((q.A*q.B*q.M₁*q.N₁)*q.N₂) :=
        le_mul_of_one_le_right (by positivity)
          (one_le_mul_of_one_le_of_one_le hABM₁N₁ hN₂)
      _ = q.mass := by dsimp [QuadraticScales.mass, QuadraticScales.M, QuadraticScales.N]; ring
  · calc q.A*q.B*q.M₁*q.N₁ ≤ (q.A*q.B*q.M₁*q.N₁)*(q.M₂*q.N₂) :=
        le_mul_of_one_le_right (by positivity) hM₂N₂
      _ = q.mass := by dsimp [QuadraticScales.mass, QuadraticScales.M, QuadraticScales.N]; ring

theorem poissonRadius_pos (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    {d : ℝ} (hd : 0 < d) : 0 < poissonRadius q d := by
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hM₂ : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hN₁ : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (h 4)
  exact div_pos (mul_pos hd hM₂) (mul_pos hB hN₁)

theorem poissonRadius_lower (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    {d : ℝ} (hd : 1 ≤ d) : 1/q.mass ≤ poissonRadius q d := by
  obtain ⟨hQ, hBN, hBNQ, _, _⟩ := poisson_scale_bounds q h
  have hM₂ : 1 ≤ q.M₂ := h 3
  unfold poissonRadius
  calc 1/q.mass ≤ 1/(q.B*q.N₁) :=
      div_le_div_of_nonneg_left zero_le_one (by linarith) hBNQ
    _ ≤ d*q.M₂/(q.B*q.N₁) :=
      div_le_div_of_nonneg_right (one_le_mul_of_one_le_of_one_le hd hM₂) (by linarith)

theorem poissonRadius_upper (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    {d : ℝ} (hd : d ≤ 4*q.B*q.N₁) : poissonRadius q d ≤ 4*q.mass := by
  obtain ⟨_, hBN, _, hM₂Q, _⟩ := poisson_scale_bounds q h
  have hM₂ : 0 ≤ q.M₂ := (by norm_num : (0 : ℝ) ≤ 1).trans (h 3)
  calc poissonRadius q d ≤ (4*q.B*q.N₁)*q.M₂/(q.B*q.N₁) := by
        unfold poissonRadius
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hd hM₂) (by linarith)
    _ = 4*q.M₂ := by
      rw [show (4*q.B*q.N₁)*q.M₂ = (4*q.M₂)*(q.B*q.N₁) by ring,
        mul_div_cancel_right₀ _ (by linarith : q.B*q.N₁ ≠ 0)]
    _ ≤ 4*q.mass := mul_le_mul_of_nonneg_left hM₂Q (by norm_num)

theorem poissonLength_mul_radius (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    (ρ : ℝ) {d : ℝ} (hd : 0 < d) :
    poissonLength q ρ d * poissonRadius q d =
      Real.sqrt q.mass/(q.B*q.N)*q.mass^(10*ρ) := by
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hM₂ : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hN₁ : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (h 4)
  have hN₂ : 0 < q.N₂ := lt_of_lt_of_le (by norm_num) (h 5)
  unfold poissonLength poissonRadius QuadraticScales.N
  field_simp

theorem normalized_poisson_slopes (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    {X Y d K : ℝ} (hK : 1 ≤ K) (hd : 0 < d)
    (hX : 0 ≤ X) (hXupper : X ≤ 4*q.A*q.M₁)
    (hYlower : q.B*q.N₁ ≤ Y) (hYupper : Y ≤ 4*q.B*q.N₁)
    (hbalance : q.A*q.M ≤ K*q.B*q.N) :
    1 ≤ (Y/(d*q.M₂))*poissonRadius q d ∧
      0 ≤ (X/(d*q.N₂))*poissonRadius q d ∧
      (Y/(d*q.M₂))*poissonRadius q d ≤ 4*K ∧
      (X/(d*q.N₂))*poissonRadius q d ≤ 4*K := by
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hM₂ : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hN₁ : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (h 4)
  have hN₂ : 0 < q.N₂ := lt_of_lt_of_le (by norm_num) (h 5)
  have hid₂ : (Y/(d*q.M₂))*poissonRadius q d = Y/(q.B*q.N₁) := by
    unfold poissonRadius
    field_simp
  have hid₄ : (X/(d*q.N₂))*poissonRadius q d = (X*q.M₂)/(q.B*q.N) := by
    unfold poissonRadius QuadraticScales.N
    field_simp
  rw [hid₂, hid₄]
  have hBN : 0 < q.B*q.N := by dsimp [QuadraticScales.N]; positivity
  refine ⟨(one_le_div (by positivity)).mpr hYlower, div_nonneg (by positivity) hBN.le, ?_, ?_⟩
  · apply (div_le_iff₀ (mul_pos hB hN₁)).mpr
    calc Y ≤ 4*(q.B*q.N₁) := by nlinarith
      _ ≤ (4*K)*(q.B*q.N₁) := by nlinarith [mul_pos hB hN₁]
  · apply (div_le_iff₀ hBN).mpr
    calc X*q.M₂ ≤ (4*q.A*q.M₁)*q.M₂ := mul_le_mul_of_nonneg_right hXupper hM₂.le
      _ = 4*(q.A*q.M) := by dsimp [QuadraticScales.M]; ring
      _ ≤ 4*(K*q.B*q.N) := mul_le_mul_of_nonneg_left hbalance (by norm_num)
      _ = (4*K)*(q.B*q.N) := by ring

theorem poissonLength_pos (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    (ρ : ℝ) {d : ℝ} (hd : 0 < d) : 0 < poissonLength q ρ d := by
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q h).1
  have hM₂ : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hN₂ : 0 < q.N₂ := lt_of_lt_of_le (by norm_num) (h 5)
  exact mul_pos (div_pos (Real.sqrt_pos.mpr hQ) (by positivity)) (Real.rpow_pos_of_pos hQ _)

theorem balanced_sqrt_ratio_lower {u v K : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hK : 1 ≤ K) (hbalance : v ≤ K*u) :
    1/K ≤ Real.sqrt (u*v)/v := by
  have hKp : 0 < K := by linarith
  have hroot := Real.sq_sqrt (mul_pos hu hv).le
  have h₁ := mul_le_mul_of_nonneg_right hbalance (mul_nonneg hKp.le hv.le)
  have h₂ := mul_le_mul_of_nonneg_right hK (sq_nonneg v)
  have hs : v^2 ≤ (K*Real.sqrt (u*v))^2 := by
    rw [mul_pow, hroot]
    nlinarith
  have hlin : v ≤ K*Real.sqrt (u*v) :=
    (sq_le_sq₀ hv.le (mul_nonneg hKp.le (Real.sqrt_nonneg _))).mp hs
  apply (div_le_div_iff₀ hKp hv).mpr
  simpa only [one_mul, mul_one, mul_comm] using hlin

theorem poissonLength_mul_radius_lower (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    {K : ℝ} (hK : 1 ≤ K) (hbalance : q.B*q.N ≤ K*q.A*q.M)
    (ρ : ℝ) {d : ℝ} (hd : 0 < d) :
    q.mass^(10*ρ)/K ≤ poissonLength q ρ d * poissonRadius q d := by
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hM₁ : 0 < q.M₁ := lt_of_lt_of_le (by norm_num) (h 2)
  have hM₂ : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hN₁ : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (h 4)
  have hN₂ : 0 < q.N₂ := lt_of_lt_of_le (by norm_num) (h 5)
  have hu : 0 < q.A*q.M := by dsimp [QuadraticScales.M]; positivity
  have hv : 0 < q.B*q.N := by dsimp [QuadraticScales.N]; positivity
  have hb : q.B*q.N ≤ K*(q.A*q.M) := by simpa only [mul_assoc] using hbalance
  have hratio := balanced_sqrt_ratio_lower hu hv hK hb
  rw [← mass_eq_balanced_product q] at hratio
  rw [poissonLength_mul_radius q h ρ hd]
  calc q.mass^(10*ρ)/K = (1/K)*q.mass^(10*ρ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio
      (Real.rpow_nonneg (zero_le_one.trans (poisson_scale_bounds q h).1) _)

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set
open scoped BigOperators ContDiff
noncomputable section

def sourceBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

def sourceCutoff : ℝ → ℝ := sourceBump

theorem sourceCutoff_contDiff : ContDiff ℝ ∞ sourceCutoff := sourceBump.contDiff

theorem sourceCutoff_hasCompactSupport : HasCompactSupport sourceCutoff :=
  sourceBump.hasCompactSupport

theorem sourceCutoff_even (x : ℝ) : sourceCutoff (-x) = sourceCutoff x := sourceBump.neg x

theorem sourceCutoff_one (x : ℝ) (hx : |x| ≤ 1) : sourceCutoff x = 1 := by
  apply sourceBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, sourceBump] using hx

theorem sourceCutoff_zero (x : ℝ) (hx : 2 ≤ |x|) : sourceCutoff x = 0 := by
  apply sourceBump.zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, sourceBump] using hx

theorem sourceCutoff_nonneg (x : ℝ) : 0 ≤ sourceCutoff x := sourceBump.nonneg

theorem sourceCutoff_norm (x : ℝ) : |sourceCutoff x| ≤ 1 := by
  rw [abs_of_nonneg (sourceCutoff_nonneg x)]
  exact sourceBump.le_one

theorem sourceCutoff_zero_of_short {L : ℝ} (hL : 0 < L) (hshort : L ≤ 1/2)
    {l : ℤ} (hl : l ≠ 0) : sourceCutoff ((l : ℝ)/L) = 0 := by
  have hli : (1 : ℤ) ≤ |l| := by
    have hp : (0 : ℤ) < |l| := abs_pos.mpr hl
    omega
  have hlr : (1 : ℝ) ≤ |(l : ℝ)| := by exact_mod_cast hli
  apply sourceCutoff_zero
  rw [abs_div, abs_of_pos hL]
  exact (le_div_iff₀ hL).mpr (by linarith)

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 800000

def finitePoissonKernel (L t x : ℝ) : ℂ :=
  ∑ l ∈ frequencySet (2*L), if l = 0 then 0 else
    (sourceCutoff ((l : ℝ)/L) : ℂ)*ePhase (-(l : ℝ)*t)*ePhase ((l : ℝ)*x)

theorem finite_poisson_integral {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄) (ha : 0 < a)
    (L t : ℝ) :
    (∑ l ∈ frequencySet (2*L), (sourceCutoff ((l : ℝ)/L) : ℂ)*
      (if l = 0 then 0 else poissonCoefficient W₂ W₄ a b l*ePhase (-(l : ℝ)*t))) =
      ∫ x : ℝ in Ioi 0, poissonProfile W₂ W₄ a b x*finitePoissonKernel L t x := by
  let g : ℤ → ℝ → ℂ := fun l x => if l = 0 then 0 else
    ((sourceCutoff ((l : ℝ)/L) : ℂ)*ePhase (-(l : ℝ)*t))*
      (poissonProfile W₂ W₄ a b x*ePhase ((l : ℝ)*x))
  have hg (l : ℤ) : Integrable (g l) := by
    by_cases hl : l = 0
    · simp only [g, hl, ite_true]
      exact integrable_zero _ _ _
    · simpa only [g, ite_eq_right hl] using
        (poissonCoefficient_integrable h₂ h₄ ha.ne' l).const_mul
          ((sourceCutoff ((l : ℝ)/L) : ℂ)*ePhase (-(l : ℝ)*t))
  have hcoef (l : ℤ) : (sourceCutoff ((l : ℝ)/L) : ℂ)*
      (if l = 0 then 0 else poissonCoefficient W₂ W₄ a b l*ePhase (-(l : ℝ)*t)) =
      ∫ x : ℝ, g l x := by
    by_cases hl : l = 0
    · simp [hl, g]
    · simp only [g, ite_eq_right hl, integral_const_mul, poissonCoefficient]
      ring
  have hintegrand (x : ℝ) : (∑ l ∈ frequencySet (2*L), g l x) =
      poissonProfile W₂ W₄ a b x*finitePoissonKernel L t x := by
    unfold finitePoissonKernel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : l = 0 <;> simp only [g, hl, ite_true, ite_false, mul_zero]
    ring
  simp_rw [hcoef]
  rw [← integral_finsetSum _ (fun l _ => hg l)]
  simp_rw [hintegrand]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [poissonProfile_zero_of_nonpos h₂ ha (not_lt.mp hx), zero_mul]

theorem finite_poisson_profile {W₂ W₄ : ℝ → ℝ} {a b r K L : ℝ}
    {bounds : ℕ → ℝ} (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (hr : 0 < r) (hL : 0 < L) (ha : 1 ≤ a*r) (hb : 0 ≤ b*r)
    (haK : a*r ≤ K) (hbK : b*r ≤ K)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j) (J : ℕ) (t : ℝ) :
    ‖((∑' n : ℤ, poissonProfile W₂ W₄ a b (t+n)) -
        ∫ x : ℝ in Ioi 0, (W₂ (a*x) : ℂ)*(W₄ (b*x) : ℂ)) -
      ∫ x : ℝ in Ioi 0, poissonProfile W₂ W₄ a b x*finitePoissonKernel L t x‖ ≤
        ((2*profileFourierBound bounds K (J+2))/(r*(1+L*r)^J))*inverseSquareMass := by
  have hap : 0 < a := by nlinarith
  let f : ℤ → ℂ := fun l => if l = 0 then 0 else
    poissonCoefficient W₂ W₄ a b l*ePhase (-(l : ℝ)*t)
  have hf : Summable f := by
    apply ((poissonSeries_summable (b := b) h₂ h₄ hap.ne' t).indicator {l : ℤ | l ≠ 0}).congr
    intro l
    by_cases hl : l = 0 <;> simp [f, hl]
  have hC : 0 ≤ profileFourierBound bounds K (J+2) :=
    profileFourierBound_nonneg (fun j => (norm_nonneg _).trans (hder₂ j 0))
      (by nlinarith) _
  have hdecay (l : ℤ) : ‖f l‖ ≤
      r*profileFourierBound bounds K (J+2)/(1+|(l : ℝ)| * r)^(J+2) := by
    by_cases hl : l = 0
    · simp only [f, hl, ite_true, norm_zero]
      positivity
    · simp only [f, ite_eq_right hl, norm_mul, norm_ePhase, mul_one]
      exact poissonCoefficient_decay h₂ h₄ hr ha hb haK hbK hder₂ hder₄ _ _
  have hbound := smooth_cutoff_error_bound hf hC hr hL J hdecay sourceCutoff
    sourceCutoff_one sourceCutoff_zero sourceCutoff_norm
  rw [poisson_profile_nonzero_identity h₂ h₄ hap,
    ← finite_poisson_integral h₂ h₄ hap]
  exact hbound

end
end DivisorProof



namespace DivisorProof
open MeasureTheory Set Finset
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000

def truncationOrder (ρ : ℝ) : ℕ := ⌈1/ρ⌉₊

theorem truncationOrder_reserve {ρ : ℝ} (hρ : 0 < ρ) :
    1 ≤ ρ*(truncationOrder ρ : ℝ) := by
  have h := Nat.le_ceil (1/ρ)
  have hm := (div_le_iff₀ hρ).mp h
  simpa only [truncationOrder, mul_comm] using hm

theorem cutoff_power_reserve {Q K L r ρ : ℝ} (hQ : 1 ≤ Q) (hK : 0 < K)
    (hρ : 0 < ρ) (hprod : Q^(10*ρ)/K ≤ L*r) :
    Q^10 ≤ (K*(1+L*r))^(truncationOrder ρ) := by
  have hQp : 0 < Q := by linarith
  have he : (10 : ℝ) ≤ (10*ρ)*(truncationOrder ρ : ℝ) := by
    nlinarith [truncationOrder_reserve hρ]
  have hbase : Q^(10*ρ) ≤ K*(1+L*r) := by
    have hp := (div_le_iff₀ hK).mp hprod
    nlinarith
  calc Q^10 = Q^(10 : ℝ) := (Real.rpow_natCast Q 10).symm
    _ ≤ Q^((10*ρ)*(truncationOrder ρ : ℝ)) := Real.rpow_le_rpow_of_exponent_le hQ he
    _ = (Q^(10*ρ))^(truncationOrder ρ) := (Real.rpow_mul_natCast hQp.le _ _)
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hQp.le _) hbase _

theorem truncation_budget {Q K L r C Z : ℝ} (hQ : 1 ≤ Q) (_hK : 0 < K)
    (hr : 0 < r) (hL : 0 ≤ L) (hC : 0 ≤ C) (hZ : 0 ≤ Z)
    (hrlower : 1/Q ≤ r) (J : ℕ) (hcut : Q^10 ≤ (K*(1+L*r))^J) :
    (C/(r*(1+L*r)^J))*Z ≤ (C*K^J*Z)/Q^9 := by
  have hQp : 0 < Q := by linarith
  have hQr : 1 ≤ r*Q := (div_le_iff₀ hQp).mp hrlower
  have hv : 0 < 1+L*r := by positivity
  have hden : Q^9 ≤ K^J*(r*(1+L*r)^J) := by
    calc Q^9 ≤ (r*Q)*Q^9 := le_mul_of_one_le_left (by positivity) hQr
      _ = r*Q^10 := by ring
      _ ≤ r*((K*(1+L*r))^J) := mul_le_mul_of_nonneg_left hcut hr.le
      _ = K^J*(r*(1+L*r)^J) := by rw [mul_pow]; ring
  have hmain : C/(r*(1+L*r)^J) ≤ C*K^J/Q^9 := by
    apply (div_le_div_iff₀ (mul_pos hr (pow_pos hv J)) (pow_pos hQp 9)).mpr
    calc C*Q^9 ≤ C*(K^J*(r*(1+L*r)^J)) := mul_le_mul_of_nonneg_left hden hC
      _ = (C*K^J)*(r*(1+L*r)^J) := by ring
  calc _ ≤ (C*K^J/Q^9)*Z := mul_le_mul_of_nonneg_right hmain hZ
    _ = _ := by ring

theorem sum_truncation_budget {ι : Type*} (s : Finset ι) (error : ι → ℂ)
    {Q E C : ℝ} (hQ : 1 ≤ Q) (_hE : 0 ≤ E) (hC : 0 ≤ C)
    (hcard : (s.card : ℝ) ≤ E*Q^2)
    (herr : ∀ i ∈ s, ‖error i‖ ≤ C/Q^9) :
    ‖∑ i ∈ s, error i‖ ≤ E*C/Q^7 := by
  have hQp : 0 < Q := by linarith
  calc _ ≤ ∑ i ∈ s, ‖error i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, C/Q^9 := sum_le_sum herr
    _ = (s.card : ℝ)*(C/Q^9) := by simp
    _ ≤ (E*Q^2)*(C/Q^9) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = E*C/Q^7 := by field_simp

theorem finite_poisson_dyadic_remainder {W₂ W₄ : ℝ → ℝ} {bounds : ℕ → ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    {X Y d K ρ : ℝ} (hK : 1 ≤ K) (hρ : 0 < ρ) (hd : 1 ≤ d)
    (hX : 0 ≤ X) (hXupper : X ≤ 4*q.A*q.M₁)
    (hYlower : q.B*q.N₁ ≤ Y) (hYupper : Y ≤ 4*q.B*q.N₁)
    (hbalance₁ : q.A*q.M ≤ K*q.B*q.N) (hbalance₂ : q.B*q.N ≤ K*q.A*q.M)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j) (t : ℝ) :
    ‖((∑' n : ℤ, poissonProfile W₂ W₄ (Y/(d*q.M₂)) (X/(d*q.N₂)) (t+n)) -
        ∫ x : ℝ in Ioi 0, (W₂ ((Y/(d*q.M₂))*x) : ℂ)*(W₄ ((X/(d*q.N₂))*x) : ℂ)) -
      ∫ x : ℝ in Ioi 0, poissonProfile W₂ W₄ (Y/(d*q.M₂)) (X/(d*q.N₂)) x *
        finitePoissonKernel (poissonLength q ρ d) t x‖ ≤
      (2*profileFourierBound bounds (4*K) (truncationOrder ρ+2)*
        K^(truncationOrder ρ)*inverseSquareMass)/q.mass^9 := by
  have hdp : 0 < d := by linarith
  have hr := poissonRadius_pos q h hdp
  have hL := poissonLength_pos q h ρ hdp
  obtain ⟨hs₁, hs₂, hs₃, hs₄⟩ := normalized_poisson_slopes q h hK hdp
    hX hXupper hYlower hYupper hbalance₁
  have hfirst := finite_poisson_profile h₂ h₄ hr hL hs₁ hs₂ hs₃ hs₄ hder₂ hder₄
    (truncationOrder ρ) t
  apply hfirst.trans
  have hQ := (poisson_scale_bounds q h).1
  have hKp : 0 < K := by linarith
  have hC : 0 ≤ 2*profileFourierBound bounds (4*K) (truncationOrder ρ+2) :=
    mul_nonneg (by norm_num) (profileFourierBound_nonneg
      (fun j => (norm_nonneg _).trans (hder₂ j 0)) (by linarith) _)
  exact truncation_budget hQ hKp hr hL.le hC inverseSquareMass_nonneg
    (poissonRadius_lower q h hd) _
    (cutoff_power_reserve hQ hKp hρ (poissonLength_mul_radius_lower q h hK hbalance₂ ρ hdp))

end
end DivisorProof
