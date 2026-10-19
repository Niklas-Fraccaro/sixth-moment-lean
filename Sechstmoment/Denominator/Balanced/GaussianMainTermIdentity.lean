import Sechstmoment.Denominator.Balanced.GaussianOffDiagonal
import Sechstmoment.Denominator.Balanced.MomentDefinitions
import Sechstmoment.Denominator.Measures.DiagonalLaplaceTransform
import Sechstmoment.Zeta.AFE.Two.AbsoluteMass

/-! Exact finite expansion of the literal four-profile Gaussian main term,
its diagonal/off-diagonal partition, and its original D01 atomic measure.
These are identities of actual Dirichlet sums, without asymptotic premises. -/
namespace Sechstmoment
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1500000

def d02FourProfileFactor (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ) (j : Fin 4) (u : ℕ) : ℂ :=
  (ρ j (Real.log (u + 1 : ℝ) / Real.log T) : ℂ) /
    (u + 1 : ℂ) ^ (if j.val < 2 then criticalLinePoint t else 1 - criticalLinePoint t)

theorem d02BalancedAmplifier_finite_expansion {T : ℝ} (hT : 1 < T)
    (t : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) :
    d02BalancedAmplifier T t ρ =
      ∑ u ∈ d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊),
        ∏ j : Fin 4, d02FourProfileFactor T t ρ j (u j) := by
  have hf (j : Fin 4) :
      profileDirichletSum T (ρ j)
        (if j.val < 2 then criticalLinePoint t else 1 - criticalLinePoint t) =
      ∑ u ∈ Finset.range ⌊T ^ (a j)⌋₊, d02FourProfileFactor T t ρ j u :=
    profileDirichletSum_eq_finite hT (a j) (ρ j) (hcap j) _
  have he : d02BalancedAmplifier T t ρ =
      ∏ j : Fin 4, profileDirichletSum T (ρ j)
        (if j.val < 2 then criticalLinePoint t else 1 - criticalLinePoint t) := by
    simp [d02BalancedAmplifier, Fin.prod_univ_four]
  rw [he]
  simp_rw [hf]
  exact Finset.prod_univ_sum _ _

def d02GaussianPairTerm (α : Fin 2 → ℂ) (t : ℝ) (p : ℕ × ℕ) : ℂ :=
  d02PairDirichletCoefficient α p *
    Complex.exp (((-t * Real.log ((p.1 + 1 : ℝ) / (p.2 + 1 : ℝ)) : ℝ) : ℂ) * I) *
      (d02GaussianV0 (2 * Real.pi * d02PositivePairProduct p / t) : ℂ)

def d02SixJoin (x : (Fin 4 → ℕ) × (ℕ × ℕ)) : Fin 6 → ℕ :=
  ![x.1 0, x.1 1, x.1 2, x.1 3, x.2.1, x.2.2]

theorem d02SixJoin_injective : Function.Injective d02SixJoin := by
  intro x y h
  apply Prod.ext
  · funext j
    fin_cases j
    · simpa [d02SixJoin] using congrFun h (0 : Fin 6)
    · simpa [d02SixJoin] using congrFun h (1 : Fin 6)
    · simpa [d02SixJoin] using congrFun h (2 : Fin 6)
    · simpa [d02SixJoin] using congrFun h (3 : Fin 6)
  · apply Prod.ext
    · simpa [d02SixJoin] using congrFun h (4 : Fin 6)
    · simpa [d02SixJoin] using congrFun h (5 : Fin 6)

def d02SixAllJoinEquiv : ((Fin 4 → ℕ) × (ℕ × ℕ)) ≃ (Fin 6 → ℕ) where
  toFun := d02SixJoin
  invFun q := (fun j => q (j.castAdd 2), (q 4, q 5))
  left_inv x := by
    apply Prod.ext
    · funext j
      fin_cases j <;> simp [d02SixJoin, Fin.castAdd]
    · simp [d02SixJoin]
  right_inv q := by
    funext j
    fin_cases j <;> simp [d02SixJoin, Fin.castAdd]

def d02SixMainDomain (N : Fin 4 → ℕ) (P : Finset (ℕ × ℕ)) : Finset (Fin 6 → ℕ) :=
  ((d02PositiveBox N).product P).image d02SixJoin

theorem d02SixMainDomain_mem_iff (N : Fin 4 → ℕ) (P : Finset (ℕ × ℕ))
    (q : Fin 6 → ℕ) :
    q ∈ d02SixMainDomain N P ↔
      (fun j : Fin 4 => q (j.castAdd 2)) ∈ d02PositiveBox N ∧ (q 4, q 5) ∈ P := by
  change q ∈ d02SixMainDomain N P ↔
    (d02SixAllJoinEquiv.symm q).1 ∈ d02PositiveBox N ∧ (d02SixAllJoinEquiv.symm q).2 ∈ P
  constructor
  · intro hq
    obtain ⟨x, hx, he⟩ := Finset.mem_image.1 hq
    have hxe : d02SixAllJoinEquiv.symm q = x := by
      rw [← he]
      exact d02SixAllJoinEquiv.symm_apply_apply x
    rw [hxe]
    exact Finset.mem_product.1 hx
  · intro hq
    exact Finset.mem_image.2 ⟨d02SixAllJoinEquiv.symm q,
      Finset.mem_product.2 hq, d02SixAllJoinEquiv.apply_symm_apply q⟩

def d02SixLengthExponents (a : Fin 4 → ℝ) (δ : ℝ) : Fin 6 → ℝ :=
  ![a 0, a 1, a 2, a 3, 1 + δ, 1 + δ]

/-- The literal two-index product cutoff supplies both remaining individual
cutoffs, so the four-profile Gaussian expansion lies in the coefficient box
used in the proved integration-by-parts bound. -/
theorem d02SixMainDomain_subset_height_box {T δ : ℝ} (hT : 0 < T)
    (a : Fin 4 → ℝ) (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, d02PositivePairProduct p ≤ T ^ (1 + δ)) :
    d02SixMainDomain (fun j => ⌊T ^ (a j)⌋₊) P ⊆
      d02PositiveBox (fun j => ⌊T ^ (d02SixLengthExponents a δ j)⌋₊) := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
  have hx₁ := (Finset.mem_product.1 hx).1
  have hx₂ := (Finset.mem_product.1 hx).2
  have hp := hP x.2 hx₂
  have hm : (x.2.1 + 1 : ℝ) ≤ T ^ (1 + δ) := by
    unfold d02PositivePairProduct at hp
    have h₁ : (1 : ℝ) ≤ x.2.1 + 1 := by linarith [Nat.cast_nonneg (α := ℝ) x.2.1]
    have h₂ : (1 : ℝ) ≤ x.2.2 + 1 := by linarith [Nat.cast_nonneg (α := ℝ) x.2.2]
    nlinarith
  have hn : (x.2.2 + 1 : ℝ) ≤ T ^ (1 + δ) := by
    unfold d02PositivePairProduct at hp
    have h₁ : (1 : ℝ) ≤ x.2.1 + 1 := by linarith [Nat.cast_nonneg (α := ℝ) x.2.1]
    have h₂ : (1 : ℝ) ≤ x.2.2 + 1 := by linarith [Nat.cast_nonneg (α := ℝ) x.2.2]
    nlinarith
  have hm' : x.2.1 ∈ Finset.range ⌊T ^ (1 + δ)⌋₊ := by
    apply Finset.mem_range.2
    apply Nat.lt_of_succ_le
    apply (Nat.le_floor_iff (Real.rpow_nonneg hT.le _)).2
    exact_mod_cast hm
  have hn' : x.2.2 ∈ Finset.range ⌊T ^ (1 + δ)⌋₊ := by
    apply Finset.mem_range.2
    apply Nat.lt_of_succ_le
    apply (Nat.le_floor_iff (Real.rpow_nonneg hT.le _)).2
    exact_mod_cast hn
  apply Fintype.mem_piFinset.2
  intro j
  fin_cases j
  · simpa [d02SixJoin, d02SixLengthExponents] using Fintype.mem_piFinset.1 hx₁ (0 : Fin 4)
  · simpa [d02SixJoin, d02SixLengthExponents] using Fintype.mem_piFinset.1 hx₁ (1 : Fin 4)
  · simpa [d02SixJoin, d02SixLengthExponents] using Fintype.mem_piFinset.1 hx₁ (2 : Fin 4)
  · simpa [d02SixJoin, d02SixLengthExponents] using Fintype.mem_piFinset.1 hx₁ (3 : Fin 4)
  · simpa [d02SixJoin, d02SixLengthExponents] using hm'
  · simpa [d02SixJoin, d02SixLengthExponents] using hn'

theorem d02SixMainDomain_pair_product_bound (N : Fin 4 → ℕ)
    (P : Finset (ℕ × ℕ)) {X : ℝ}
    (hP : ∀ p ∈ P, d02PositivePairProduct p ≤ X)
    (q : Fin 6 → ℕ) (hq : q ∈ d02SixMainDomain N P) :
    (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) ≤ X := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
  have h := hP x.2 (Finset.mem_product.1 hx).2
  simpa [d02SixJoin, d02SixIndexM, d02SixIndexN, d02PositivePairProduct] using h

def d02SixRawGaussianTerm (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ) (α : Fin 2 → ℂ)
    (q : Fin 6 → ℕ) : ℂ :=
  (∏ j : Fin 4, d02FourProfileFactor T t ρ j (q (j.castAdd 2))) *
    d02GaussianPairTerm α t (q 4, q 5)

theorem d02SixRawGaussianTerm_join (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ) (α : Fin 2 → ℂ)
    (x : (Fin 4 → ℕ) × (ℕ × ℕ)) :
    d02SixRawGaussianTerm T t ρ α (d02SixJoin x) =
      (∏ j : Fin 4, d02FourProfileFactor T t ρ j (x.1 j)) * d02GaussianPairTerm α t x.2 := by
  have hj (j : Fin 4) : d02SixJoin x (j.castAdd 2) = x.1 j := by
    fin_cases j <;> simp [d02SixJoin]
  unfold d02SixRawGaussianTerm
  simp only [hj]
  simp [d02SixJoin]

/-- The four literal finite profiles times the truncated Gaussian pair series
are exactly the six-index sum, with every original factor retained. -/
theorem d02_four_profiles_gaussian_pair_finite_identity {T : ℝ} (hT : 1 < T)
    (t : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) (α : Fin 2 → ℂ) (P : Finset (ℕ × ℕ)) :
    d02BalancedAmplifier T t ρ * (∑ p ∈ P, d02GaussianPairTerm α t p) =
      ∑ q ∈ d02SixMainDomain (fun j => ⌊T ^ (a j)⌋₊) P,
        d02SixRawGaussianTerm T t ρ α q := by
  rw [d02BalancedAmplifier_finite_expansion hT t a ρ hcap, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  unfold d02SixMainDomain
  rw [Finset.sum_image (fun _ _ _ _ h => d02SixJoin_injective h)]
  apply Finset.sum_congr rfl
  intro x hx
  exact (d02SixRawGaussianTerm_join T t ρ α x).symm

theorem d02FourProfileProduct_zero_outside_box {T : ℝ} (hT : 1 < T)
    (t : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) (u : Fin 4 → ℕ)
    (hu : u ∉ d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊)) :
    (∏ j : Fin 4, d02FourProfileFactor T t ρ j (u j)) = 0 := by
  classical
  have hex : ∃ j : Fin 4, u j ∉ Finset.range ⌊T ^ (a j)⌋₊ := by
    simpa only [d02PositiveBox, Fintype.mem_piFinset, not_forall] using hu
  obtain ⟨j, hj⟩ := hex
  have hn : ⌊T ^ (a j)⌋₊ < u j + 1 := by
    have : ⌊T ^ (a j)⌋₊ ≤ u j := by simpa only [Finset.mem_range, not_lt] using hj
    omega
  have hp : T ^ (a j) < (u j + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_of_floor_lt hn
  have ha : a j < Real.log (u j + 1 : ℝ) / Real.log T :=
    (lt_div_iff₀ (Real.log_pos hT)).2
      (Real.lt_log_of_rpow_lt (zero_lt_one.trans hT) hp)
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [d02FourProfileFactor, hcap j _ ha]

/-- The Gaussian pair series is absolutely summable for every complex pair
of shifts at each positive time, by a positive Gaussian Mellin power. -/
theorem d02GaussianPairTerm_norm_summable (α : Fin 2 → ℂ) {t : ℝ} (ht : 0 < t) :
    Summable (fun p : ℕ × ℕ => ‖d02GaussianPairTerm α t p‖) := by
  let b : ℝ := 1 / 2 + min (α 0).re (α 1).re
  let A : ℝ := max 0 (2 - b)
  have hA : 0 ≤ A := le_max_left _ _
  have hbA : 1 < b + A := by
    have h := le_max_right 0 (2 - b)
    dsimp [A]
    linarith
  have hα : ∀ j : Fin 2, b - 1 / 2 ≤ (α j).re := by
    intro j
    fin_cases j
    · dsimp [b]; linarith [min_le_left (α 0).re (α 1).re]
    · dsimp [b]; linarith [min_le_right (α 0).re (α 1).re]
  have hY : 0 < t / (2 * Real.pi) := by positivity
  have hs := d02GaussianPairAbsoluteTerm_summable (d02PairDirichletCoefficient α)
    hY zero_le_one hA hbA (fun p => by
      simpa only [one_mul] using d02PairDirichletCoefficient_norm_le hα p)
  convert hs using 1
  funext p
  have he : ‖Complex.exp (((-t * Real.log ((p.1 + 1 : ℝ) / (p.2 + 1 : ℝ)) : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  unfold d02GaussianPairTerm d02GaussianPairAbsoluteTerm
  rw [norm_mul, norm_mul, he, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ d02GaussianV0
      (2 * Real.pi * d02PositivePairProduct p / t) from d02GaussianTail_nonneg _)]
  congr 2
  field_simp [ht.ne', Real.pi_ne_zero]

/-- The unrestricted literal Gaussian pair multiplied by the four finite
profiles is exactly the full six-index series. Absolute summability follows
from finite profile support and the derived Gaussian pair majorant. -/
theorem d02_four_profiles_gaussian_pair_full_identity {T : ℝ} (hT : 1 < T)
    {t : ℝ} (ht : 0 < t) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) (α : Fin 2 → ℂ) :
    d02BalancedAmplifier T t ρ * (∑' p : ℕ × ℕ, d02GaussianPairTerm α t p) =
      ∑' q : Fin 6 → ℕ, d02SixRawGaussianTerm T t ρ α q := by
  let F : (Fin 4 → ℕ) → ℂ := fun u => ∏ j : Fin 4, d02FourProfileFactor T t ρ j (u j)
  have hF : Summable (fun u => ‖F u‖) := by
    apply summable_of_ne_finset_zero (s := d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊))
    intro u hu
    rw [show F u = 0 from d02FourProfileProduct_zero_outside_box hT t a ρ hcap u hu, norm_zero]
  have hs : d02BalancedAmplifier T t ρ = ∑' u, F u := by
    rw [d02BalancedAmplifier_finite_expansion hT t a ρ hcap]
    exact (tsum_eq_sum (fun u hu =>
      d02FourProfileProduct_zero_outside_box hT t a ρ hcap u hu)).symm
  rw [hs, tsum_mul_tsum_of_summable_norm hF (d02GaussianPairTerm_norm_summable α ht)]
  rw [← d02SixAllJoinEquiv.tsum_eq (d02SixRawGaussianTerm T t ρ α)]
  apply tsum_congr
  intro x
  exact (d02SixRawGaussianTerm_join T t ρ α x).symm

theorem d02SixRawGaussianTerm_norm_summable {T : ℝ} (hT : 1 < T)
    {t : ℝ} (ht : 0 < t) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) (α : Fin 2 → ℂ) :
    Summable (fun q : Fin 6 → ℕ => ‖d02SixRawGaussianTerm T t ρ α q‖) := by
  let F : (Fin 4 → ℕ) → ℂ := fun u => ∏ j : Fin 4, d02FourProfileFactor T t ρ j (u j)
  have hF : Summable (fun u => ‖F u‖) := by
    apply summable_of_ne_finset_zero (s := d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊))
    intro u hu
    rw [show F u = 0 from d02FourProfileProduct_zero_outside_box hT t a ρ hcap u hu, norm_zero]
  apply (d02SixAllJoinEquiv.summable_iff).1
  convert hF.mul_norm (d02GaussianPairTerm_norm_summable α ht) using 1
  funext x
  change ‖d02SixRawGaussianTerm T t ρ α (d02SixJoin x)‖ = _
  rw [d02SixRawGaussianTerm_join]

def d02SixIsDiagonal (q : Fin 6 → ℕ) : Prop :=
  d02SixIndexH q * d02SixIndexM q = d02SixIndexK q * d02SixIndexN q

instance d02SixIsDiagonal_decidable (q : Fin 6 → ℕ) : Decidable (d02SixIsDiagonal q) :=
  inferInstanceAs (Decidable
    (d02SixIndexH q * d02SixIndexM q = d02SixIndexK q * d02SixIndexN q))

theorem d02_positive_dirichlet_phase_split {x : ℝ} (hx : 0 < x) (b : ℂ) (t : ℝ) :
    b / (x : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) =
      (b * (x : ℂ) ^ (-(1 / 2 : ℂ))) *
        Complex.exp (((-t * Real.log x : ℝ) : ℂ) * I) := by
  have hn : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  calc
    _ = b * Complex.exp (-((Real.log x : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I))) := by
      rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log hx.le,
        div_eq_mul_inv, ← Complex.exp_neg]
    _ = b * (Complex.exp ((Real.log x : ℂ) * (-(1 / 2 : ℂ))) *
        Complex.exp (((-t * Real.log x : ℝ) : ℂ) * I)) := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring
    _ = _ := by
      rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log hx.le]
      ring

theorem d02FourProfileFactor_phase_split (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (j : Fin 4) (u : ℕ) :
    d02FourProfileFactor T t ρ j u =
      ((ρ j (Real.log (u + 1 : ℝ) / Real.log T) : ℂ) * (u + 1 : ℂ) ^ (-(1 / 2 : ℂ))) *
        Complex.exp (((-(if j.val < 2 then t else -t) * Real.log (u + 1 : ℝ) : ℝ) : ℂ) * I) := by
  have hp : 0 < (u + 1 : ℝ) := by positivity
  have he : (u + 1 : ℂ) = ((u + 1 : ℝ) : ℂ) := by push_cast; rfl
  unfold d02FourProfileFactor
  rw [he]
  split_ifs with h
  · exact d02_positive_dirichlet_phase_split hp _ t
  · have hs : 1 - criticalLinePoint t = (1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I := by
      unfold criticalLinePoint
      push_cast
      ring
    rw [hs]
    exact d02_positive_dirichlet_phase_split hp _ (-t)

def d02SixProfileMultiplier (T : ℝ) (ρ : Fin 4 → ℝ → ℝ) (q : Fin 6 → ℕ) : ℂ :=
  ∏ j : Fin 4, (ρ j (Real.log (q (j.castAdd 2) + 1 : ℝ) / Real.log T) : ℂ)

def d02SixZetaShifts (σ : Fin 2 → ℂ) : Fin 6 → ℂ := ![0, 0, 0, 0, σ 0, σ 1]

theorem d02SixZetaShifts_norm_le (σ : Fin 2 → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hσ : ∀ j, ‖σ j‖ ≤ R) : ∀ j, ‖d02SixZetaShifts σ j‖ ≤ R := by
  intro j
  fin_cases j
  · simpa [d02SixZetaShifts] using hR
  · simpa [d02SixZetaShifts] using hR
  · simpa [d02SixZetaShifts] using hR
  · simpa [d02SixZetaShifts] using hR
  · simpa [d02SixZetaShifts] using hσ 0
  · simpa [d02SixZetaShifts] using hσ 1

/-- The raw six-factor Gaussian summand has exactly the integer logarithmic
frequency and coefficients used by the proved D02 integration-by-parts model. -/
theorem d02SixRawGaussianTerm_eq_phase_model (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (σ : Fin 2 → ℂ) (q : Fin 6 → ℕ) :
    d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q =
      (d02SixProfileMultiplier T ρ q * d02ShiftedSqrtCoefficient T (d02SixZetaShifts σ) q) *
        Complex.exp (((-t * Real.log (((d02SixIndexH q * d02SixIndexM q : ℕ) : ℝ) /
          ((d02SixIndexK q * d02SixIndexN q : ℕ) : ℝ)) : ℝ) : ℂ) * I) *
        (d02GaussianV0 (2 * Real.pi * (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) / t) : ℂ) := by
  have hp (j : Fin 6) : 0 < (q j + 1 : ℝ) := by positivity
  have hl : Real.log (((d02SixIndexH q * d02SixIndexM q : ℕ) : ℝ) /
      ((d02SixIndexK q * d02SixIndexN q : ℕ) : ℝ)) =
      Real.log (q 0 + 1 : ℝ) + Real.log (q 1 + 1 : ℝ) -
        Real.log (q 2 + 1 : ℝ) - Real.log (q 3 + 1 : ℝ) +
          Real.log ((q 4 + 1 : ℝ) / (q 5 + 1 : ℝ)) := by
    unfold d02SixIndexH d02SixIndexK d02SixIndexM d02SixIndexN
    push_cast
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (hp 4).ne', Real.log_mul (hp 0).ne' (hp 1).ne',
      Real.log_mul (by positivity) (hp 5).ne', Real.log_mul (hp 2).ne' (hp 3).ne',
      Real.log_div (hp 4).ne' (hp 5).ne']
    ring
  rw [hl]
  unfold d02SixRawGaussianTerm
  simp only [Fin.prod_univ_four]
  simp_rw [d02FourProfileFactor_phase_split]
  unfold d02GaussianPairTerm d02PairDirichletCoefficient d02SixProfileMultiplier
    d02ShiftedSqrtCoefficient d02SixZetaShifts d02SixIndexM d02SixIndexN d02PositivePairProduct
  simp only [Fin.prod_univ_four, Fin.prod_univ_six]
  norm_num [Fin.castAdd]
  rw [show 2 * Real.pi * ((q 4 + 1 : ℝ) * (q 5 + 1 : ℝ)) / t =
    2 * Real.pi * (q 4 + 1 : ℝ) * (q 5 + 1 : ℝ) / t by ring]
  have hexp : Complex.exp (-((t : ℂ) * (Real.log (q 0 + 1 : ℝ) : ℂ) * I)) *
      Complex.exp (-((t : ℂ) * (Real.log (q 1 + 1 : ℝ) : ℂ) * I)) *
      Complex.exp ((t : ℂ) * (Real.log (q 2 + 1 : ℝ) : ℂ) * I) *
      Complex.exp ((t : ℂ) * (Real.log (q 3 + 1 : ℝ) : ℂ) * I) *
      Complex.exp (-((t : ℂ) * (Real.log ((q 4 + 1 : ℝ) / (q 5 + 1 : ℝ)) : ℂ) * I)) =
      Complex.exp (-((t : ℂ) * ((Real.log (q 0 + 1 : ℝ) : ℂ) +
        (Real.log (q 1 + 1 : ℝ) : ℂ) - (Real.log (q 2 + 1 : ℝ) : ℂ) -
        (Real.log (q 3 + 1 : ℝ) : ℂ) +
        (Real.log ((q 4 + 1 : ℝ) / (q 5 + 1 : ℝ)) : ℂ)) * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [← hexp]
  push_cast
  ring

/-- Integrability of the literal compact time-profile Fourier integrand is
derived before interchanging any finite arithmetic sum and time integral. -/
theorem d02_profile_time_fourier_integrable {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc (1 : ℝ) 2)
    {T : ℝ} (hT : 0 < T) (ℓ : ℝ) :
    Integrable (fun t : ℝ => f (t / T) *
      Complex.exp (((ℓ * t : ℝ) : ℂ) * I)) := by
  let g : ℝ → ℂ := fun y => f y * Complex.exp (((ℓ * T * y : ℝ) : ℂ) * I)
  have hgc : Continuous g := by
    have hfc := hf.continuous
    dsimp [g]
    fun_prop
  have hfK : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  have hgK : HasCompactSupport g := hfK.mul_right
  have hi := (hgc.integrable_of_hasCompactSupport hgK).comp_div hT.ne'
  convert hi using 1
  funext t
  dsimp [g]
  congr 2
  push_cast
  field_simp [hT.ne', show (T : ℂ) ≠ 0 from Complex.ofReal_ne_zero.2 hT.ne']

def d02SixGaussianTimeProfile (Φ : ℝ → ℂ) (T : ℝ) (τ : ℂ)
    (q : Fin 6 → ℕ) : ℝ → ℂ :=
  a03ProfileProduct
    (a03ProfileProduct Φ (d02GaussianTimeAmplitude
      (2 * Real.pi * (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) / T)))
    (fun y : ℝ => (y : ℂ) ^ τ)

def d02SixGaussianFrequency (q : Fin 6 → ℕ) : ℝ :=
  -Real.log (((d02SixIndexH q * d02SixIndexM q : ℕ) : ℝ) /
    ((d02SixIndexK q * d02SixIndexN q : ℕ) : ℝ))

/-- The physical erfc summand, including an arbitrary complex power of
normalized time, is exactly the proved smooth Fourier integrand. -/
theorem d02SixRawGaussianTerm_time_phase_identity {T : ℝ} (hT : 0 < T)
    {Φ : ℝ → ℂ} (hs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (τ : ℂ)
    (q : Fin 6 → ℕ) (t : ℝ) :
    Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ *
        d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q =
      (d02SixProfileMultiplier T ρ q *
        d02ShiftedSqrtCoefficient T (d02SixZetaShifts σ) q) *
      (d02SixGaussianTimeProfile Φ T τ q (t / T) *
        Complex.exp (((d02SixGaussianFrequency q * t : ℝ) : ℂ) * I)) := by
  rw [d02SixRawGaussianTerm_eq_phase_model]
  have hX : 0 < 2 * Real.pi * (d02SixIndexM q : ℝ) *
      (d02SixIndexN q : ℝ) / T := by
    unfold d02SixIndexM d02SixIndexN
    positivity
  have hp := congrFun (d02GaussianProfile_eq_physical hs hX) (t / T)
  unfold d02SixGaussianTimeProfile a03ProfileProduct
  change Φ (t / T) * d02GaussianTimeAmplitude
    (2 * Real.pi * (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) / T) (t / T) = _ at hp
  rw [hp]
  have he : (2 * Real.pi * (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) / T) /
      (t / T) = 2 * Real.pi * (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) / t := by
    exact div_div_div_cancel_right₀ hT.ne' _ _
  rw [he]
  unfold d02SixGaussianFrequency
  rw [show -t * Real.log (((d02SixIndexH q * d02SixIndexM q : ℕ) : ℝ) /
      ((d02SixIndexK q * d02SixIndexN q : ℕ) : ℝ)) =
      -Real.log (((d02SixIndexH q * d02SixIndexM q : ℕ) : ℝ) /
        ((d02SixIndexK q * d02SixIndexN q : ℕ) : ℝ)) * t by ring]
  ring

theorem d02SixRawGaussianTerm_time_integrable {T : ℝ} (hT : 0 < T)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (τ : ℂ) (q : Fin 6 → ℕ) :
    Integrable (fun t : ℝ => Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ *
      d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q) := by
  obtain ⟨_D, _hD, hreg⟩ :=
    d02GaussianShiftedProfile_uniform_derivative_bounds hΦ hs (norm_nonneg τ)
  have hr := hreg
    (2 * Real.pi * (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) / T) τ le_rfl
  have hi := (d02_profile_time_fourier_integrable hr.1 hr.2.1 hT
    (d02SixGaussianFrequency q)).const_mul
      (d02SixProfileMultiplier T ρ q * d02ShiftedSqrtCoefficient T (d02SixZetaShifts σ) q)
  have he : (fun t : ℝ => Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ *
      d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q) =
      fun t : ℝ => (d02SixProfileMultiplier T ρ q *
        d02ShiftedSqrtCoefficient T (d02SixZetaShifts σ) q) *
        (d02SixGaussianTimeProfile Φ T τ q (t / T) *
          Complex.exp (((d02SixGaussianFrequency q * t : ℝ) : ℂ) * I)) := by
    funext t
    exact d02SixRawGaussianTerm_time_phase_identity hT hs ρ σ τ q t
  rw [he]
  exact hi

theorem d02SixRawGaussianTerm_finite_time_integrable {T : ℝ} (hT : 0 < T)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (τ : ℂ) (s : Finset (Fin 6 → ℕ)) :
    Integrable (fun t : ℝ => Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ *
      ∑ q ∈ s, d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q) := by
  have hi := integrable_finsetSum s (fun q _ =>
    d02SixRawGaussianTerm_time_integrable hT hΦ hs ρ σ τ q)
  convert hi using 1
  funext t
  rw [Finset.mul_sum]

/-- Exact time integration of the finite physical six-index Gaussian sum.
Smoothness and compact time support establish every required integrability
fact; no assumed cancellation or replacement estimate occurs. -/
theorem d02SixRawGaussianTerm_finite_time_integral {T : ℝ} (hT : 0 < T)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (τ : ℂ)
    (s : Finset (Fin 6 → ℕ)) :
    (∫ t : ℝ, Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ *
      ∑ q ∈ s, d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q) =
      ∑ q ∈ s, (d02SixProfileMultiplier T ρ q *
        d02ShiftedSqrtCoefficient T (d02SixZetaShifts σ) q) *
          a03ProfileTimeFourier (d02SixGaussianTimeProfile Φ T τ q) T
            (d02SixGaussianFrequency q) := by
  obtain ⟨_D, _hD, hreg⟩ :=
    d02GaussianShiftedProfile_uniform_derivative_bounds hΦ hs (norm_nonneg τ)
  have hi (q : Fin 6 → ℕ) : Integrable (fun t : ℝ =>
      (d02SixProfileMultiplier T ρ q *
        d02ShiftedSqrtCoefficient T (d02SixZetaShifts σ) q) *
      (d02SixGaussianTimeProfile Φ T τ q (t / T) *
        Complex.exp (((d02SixGaussianFrequency q * t : ℝ) : ℂ) * I))) := by
    have hr := hreg
      (2 * Real.pi * (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) / T) τ le_rfl
    exact (d02_profile_time_fourier_integrable hr.1 hr.2.1 hT
      (d02SixGaussianFrequency q)).const_mul _
  have he : (fun t : ℝ => Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ *
      ∑ q ∈ s, d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q) =
      fun t : ℝ => ∑ q ∈ s, (d02SixProfileMultiplier T ρ q *
        d02ShiftedSqrtCoefficient T (d02SixZetaShifts σ) q) *
      (d02SixGaussianTimeProfile Φ T τ q (t / T) *
        Complex.exp (((d02SixGaussianFrequency q * t : ℝ) : ℂ) * I)) := by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    exact d02SixRawGaussianTerm_time_phase_identity hT hs ρ σ τ q t
  rw [he, integral_finsetSum s (fun q _ => hi q)]
  apply Finset.sum_congr rfl
  intro q hq
  exact integral_const_mul _ _

/-- The four actual compactly supported profiles have a single coefficient
budget valid for every height and every positive arithmetic index. -/
theorem d02SixProfileMultiplier_uniform_bound (ρ : Fin 4 → ℝ → ℝ)
    (hc : ∀ j, Continuous (ρ j)) (hK : ∀ j, HasCompactSupport (ρ j)) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ T q, ‖d02SixProfileMultiplier T ρ q‖ ≤ F := by
  choose b hb using fun j => (hK j).exists_bound_of_continuous (hc j)
  have hb0 (j : Fin 4) : 0 ≤ b j := (norm_nonneg (ρ j 0)).trans (hb j 0)
  refine ⟨∏ j : Fin 4, b j, Finset.prod_nonneg (fun j _ => hb0 j), ?_⟩
  intro T q
  unfold d02SixProfileMultiplier
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => ?_)
  rw [Complex.norm_real]
  exact hb j _

/-- One power-saving constant is uniform over both actual normalized zeta
shifts and complex time powers, with the literal four profiles retained. -/
theorem d02_raw_gaussian_offDiagonal_time_integral_uniform_power_bound
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    (ρ : Fin 4 → ℝ → ℝ) (hρc : ∀ j, Continuous (ρ j))
    (hρK : ∀ j, HasCompactSupport (ρ j))
    (a : Fin 6 → ℝ) {δ R R' : ℝ}
    (hδ : δ < 1 - (a 0 + a 1 + a 2 + a 3)) (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (A : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℝ, 1 ≤ T → 1 ≤ Real.log T →
      ∀ (s : Finset (Fin 6 → ℕ)) (σ : Fin 2 → ℂ) (τ : ℂ),
      s ⊆ d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊) →
      (∀ j, ‖σ j‖ ≤ R) → ‖τ‖ ≤ R' →
      (∀ q ∈ s, d02SixIndexH q * d02SixIndexM q ≠ d02SixIndexK q * d02SixIndexN q ∧
        (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) ≤ T ^ (1 + δ)) →
      ‖∫ t : ℝ, Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ *
        ∑ q ∈ s, d02SixRawGaussianTerm T t ρ
          (fun j => σ j / (Real.log T : ℂ)) q‖ ≤ D * T ^ (-A) := by
  obtain ⟨F, hF, hFb⟩ := d02SixProfileMultiplier_uniform_bound ρ hρc hρK
  obtain ⟨D, hD, hDb⟩ := d02_gaussian_six_index_offDiagonal_uniform_power_bound
    hΦ hΦs a hδ hR hR' hF A
  refine ⟨D, hD, ?_⟩
  intro T hT hL s σ τ hs hσ hτ hcut
  have hσ6 : ∀ j, ‖d02SixZetaShifts σ j‖ ≤ R := by
    exact d02SixZetaShifts_norm_le σ hR hσ
  have hb := hDb T hT hL s (d02SixZetaShifts σ) (d02SixProfileMultiplier T ρ)
    (fun _ => τ) hs hσ6 (fun q _ => hFb T q) (fun _ _ => hτ) hcut
  rw [d02SixRawGaussianTerm_finite_time_integral (zero_lt_one.trans_le hT) hΦ hΦs]
  simpa only [d02SixGaussianTimeProfile, d02SixGaussianFrequency] using hb

/-- The actual four-profile finite Gaussian expansion has a uniform power
saving on its arithmetic off-diagonal. Its full six-coordinate cutoff and
frequency hypotheses are consequences of the literal pair-product cutoff. -/
theorem d02_four_profile_gaussian_finite_offDiagonal_uniform_power_bound
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    (ρ : Fin 4 → ℝ → ℝ) (hρc : ∀ j, Continuous (ρ j))
    (hρK : ∀ j, HasCompactSupport (ρ j))
    (a : Fin 4 → ℝ) {δ R R' : ℝ}
    (hδ : δ < 1 - ∑ j, a j) (hR : 0 ≤ R) (hR' : 0 ≤ R') (A : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T : ℝ, 1 ≤ T → 1 ≤ Real.log T →
      ∀ (P : Finset (ℕ × ℕ)) (σ : Fin 2 → ℂ) (τ : ℂ),
      (∀ p ∈ P, d02PositivePairProduct p ≤ T ^ (1 + δ)) →
      (∀ j, ‖σ j‖ ≤ R) → ‖τ‖ ≤ R' →
      ‖∫ t : ℝ, Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ *
        ∑ q ∈ (d02SixMainDomain (fun j => ⌊T ^ (a j)⌋₊) P).filter
          (fun q => ¬d02SixIsDiagonal q),
          d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q‖ ≤
        D * T ^ (-A) := by
  have hδ6 : δ < 1 - (d02SixLengthExponents a δ 0 + d02SixLengthExponents a δ 1 +
      d02SixLengthExponents a δ 2 + d02SixLengthExponents a δ 3) := by
    simpa [d02SixLengthExponents, Fin.sum_univ_four] using hδ
  obtain ⟨D, hD, hDb⟩ := d02_raw_gaussian_offDiagonal_time_integral_uniform_power_bound
    hΦ hΦs ρ hρc hρK (d02SixLengthExponents a δ) hδ6 hR hR' A
  refine ⟨D, hD, ?_⟩
  intro T hT hL P σ τ hP hσ hτ
  have hTp : 0 < T := zero_lt_one.trans_le hT
  refine hDb T hT hL
    ((d02SixMainDomain (fun j => ⌊T ^ (a j)⌋₊) P).filter
      (fun q => ¬d02SixIsDiagonal q)) σ τ ?_ hσ hτ ?_
  · exact (Finset.filter_subset ..).trans (d02SixMainDomain_subset_height_box hTp a P hP)
  · intro q hq
    have hmem := Finset.mem_filter.1 hq
    exact ⟨hmem.2, d02SixMainDomain_pair_product_bound _ P hP q hmem.1⟩

/-- The literal physical Gaussian six-index off-diagonal, rather than a
postulated oscillatory error, enjoys arbitrary power saving. Both normalized
zeta shifts and complex normalized-time powers vary in quantified norm boxes. -/
theorem d02_raw_gaussian_offDiagonal_time_integral_arbitrary_power_decay
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    (ρ : Fin 4 → ℝ → ℝ) (hρc : ∀ j, Continuous (ρ j))
    (hρK : ∀ j, HasCompactSupport (ρ j))
    (a : Fin 6 → ℝ) {δ R R' : ℝ}
    (hδ : δ < 1 - (a 0 + a 1 + a 2 + a 3)) (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (s : ℝ → Finset (Fin 6 → ℕ)) (σ : ℝ → Fin 2 → ℂ) (τ : ℝ → ℂ)
    (hs : ∀ᶠ T : ℝ in atTop, s T ⊆ d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊))
    (hσ : ∀ᶠ T : ℝ in atTop, ∀ j, ‖σ T j‖ ≤ R)
    (hτ : ∀ᶠ T : ℝ in atTop, ‖τ T‖ ≤ R')
    (hcut : ∀ᶠ T : ℝ in atTop, ∀ q ∈ s T,
      d02SixIndexH q * d02SixIndexM q ≠ d02SixIndexK q * d02SixIndexN q ∧
      (d02SixIndexM q : ℝ) * (d02SixIndexN q : ℝ) ≤ T ^ (1 + δ))
    (A : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ T : ℝ in atTop,
      ‖∫ t : ℝ, Φ (t / T) * ((t / T : ℝ) : ℂ) ^ (τ T) *
        ∑ q ∈ s T, d02SixRawGaussianTerm T t ρ
          (fun j => σ T j / (Real.log T : ℂ)) q‖ ≤ D * T ^ (-A) := by
  obtain ⟨F, hF, hFb⟩ := d02SixProfileMultiplier_uniform_bound ρ hρc hρK
  have hσ6 : ∀ᶠ T : ℝ in atTop, ∀ j, ‖d02SixZetaShifts (σ T) j‖ ≤ R := by
    exact hσ.mono (fun T hT => d02SixZetaShifts_norm_le (σ T) hR hT)
  obtain ⟨D, hD, hDb⟩ := d02_gaussian_six_index_offDiagonal_arbitrary_power_decay
    hΦ hΦs a hδ hR hR' hF s (fun T => d02SixZetaShifts (σ T))
    (fun T => d02SixProfileMultiplier T ρ) (fun T _ => τ T)
    hs hσ6 (Filter.Eventually.of_forall (fun T q _ => hFb T q))
    (hτ.mono (fun T hT q _ => hT)) hcut A
  refine ⟨D, hD, ?_⟩
  filter_upwards [hDb, eventually_gt_atTop (0 : ℝ)] with T hb hT
  rw [d02SixRawGaussianTerm_finite_time_integral hT hΦ hΦs]
  simpa only [d02SixGaussianTimeProfile, d02SixGaussianFrequency] using hb

/-- The physical arithmetic diagonal is selected by exactly Hm=Kn. -/
theorem d02SixMain_diagonal_add_offDiagonal (s : Finset (Fin 6 → ℕ)) (F : (Fin 6 → ℕ) → ℂ) :
    (∑ q ∈ s.filter d02SixIsDiagonal, F q) +
      (∑ q ∈ s.filter (fun q => ¬d02SixIsDiagonal q), F q) = ∑ q ∈ s, F q := by
  classical
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- The absolutely summable full six-index Gaussian series partitions at
exactly Hm=Kn, before any cutoff or time-asymptotic estimate is applied. -/
theorem d02SixMain_full_diagonal_add_offDiagonal {T : ℝ} (hT : 1 < T)
    {t : ℝ} (ht : 0 < t) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) (α : Fin 2 → ℂ) :
    (∑' q : {q : Fin 6 → ℕ // d02SixIsDiagonal q}, d02SixRawGaussianTerm T t ρ α q.val) +
      (∑' q : {q : Fin 6 → ℕ // ¬d02SixIsDiagonal q}, d02SixRawGaussianTerm T t ρ α q.val) =
        d02BalancedAmplifier T t ρ * (∑' p : ℕ × ℕ, d02GaussianPairTerm α t p) := by
  have hs := (d02SixRawGaussianTerm_norm_summable hT ht a ρ hcap α).of_norm
  calc
    _ = ∑' q : Fin 6 → ℕ, d02SixRawGaussianTerm T t ρ α q :=
      hs.tsum_subtype_add_tsum_subtype_compl {q | d02SixIsDiagonal q}
    _ = _ := (d02_four_profiles_gaussian_pair_full_identity hT ht a ρ hcap α).symm

/-- Localization to the actual positive dyadic time window makes the full
arithmetic partition an identity at every real time, including the exterior
where the Gaussian pair by itself need not be summable. -/
theorem d02SixMain_full_diagonal_add_offDiagonal_time_identity {T : ℝ} (hT : 1 < T)
    {Φ : ℝ → ℂ} (hΦs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    (t : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) (α : Fin 2 → ℂ) (τ : ℂ) :
    Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ * d02BalancedAmplifier T t ρ *
      (∑' p : ℕ × ℕ, d02GaussianPairTerm α t p) =
      (Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ) *
        ((∑' q : {q : Fin 6 → ℕ // d02SixIsDiagonal q},
          d02SixRawGaussianTerm T t ρ α q.val) +
         (∑' q : {q : Fin 6 → ℕ // ¬d02SixIsDiagonal q},
          d02SixRawGaussianTerm T t ρ α q.val)) := by
  by_cases hzero : Φ (t / T) = 0
  · simp [hzero]
  · have hTp : 0 < T := zero_lt_one.trans hT
    have hy : 1 ≤ t / T := (hΦs (subset_tsupport _ hzero)).1
    have ht : 0 < t := hTp.trans_le (by simpa using (le_div_iff₀ hTp).1 hy)
    rw [d02SixMain_full_diagonal_add_offDiagonal hT ht a ρ hcap]
    ring

abbrev D02PositiveDiagonal := {q : Fin 6 → ℕ // d02SixIsDiagonal q}

/-- Finite profile support removes the profile-box mask from the arithmetic
diagonal, retaining precisely the literal finite Gaussian pair cutoff. -/
theorem d02SixRawGaussianTerm_finite_diagonal_tsum_identity {T : ℝ} (hT : 1 < T)
    (t : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) (α : Fin 2 → ℂ) (P : Finset (ℕ × ℕ)) :
    (∑ q ∈ (d02SixMainDomain (fun j => ⌊T ^ (a j)⌋₊) P).filter d02SixIsDiagonal,
      d02SixRawGaussianTerm T t ρ α q) =
      ∑' q : D02PositiveDiagonal, if (q.val 4, q.val 5) ∈ P then
        d02SixRawGaussianTerm T t ρ α q.val else 0 := by
  classical
  let s := (d02SixMainDomain (fun j => ⌊T ^ (a j)⌋₊) P).subtype d02SixIsDiagonal
  symm
  calc
    _ = ∑ q ∈ s, if (q.val 4, q.val 5) ∈ P then d02SixRawGaussianTerm T t ρ α q.val else 0 := by
      apply tsum_eq_sum
      intro q hq
      by_cases hp : (q.val 4, q.val 5) ∈ P
      · rw [ite_eq_left hp]
        have hnot : q.val ∉ d02SixMainDomain (fun j => ⌊T ^ (a j)⌋₊) P := by
          intro h
          exact hq (Finset.mem_subtype.2 h)
        have hout : (fun j : Fin 4 => q.val (j.castAdd 2)) ∉
            d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊) := by
          intro h
          exact hnot ((d02SixMainDomain_mem_iff _ P q.val).2 ⟨h, hp⟩)
        have hz := d02FourProfileProduct_zero_outside_box hT t a ρ hcap
          (fun j : Fin 4 => q.val (j.castAdd 2)) hout
        simp only [d02SixRawGaussianTerm, hz, zero_mul]
      · rw [ite_eq_right hp]
    _ = ∑ q ∈ s, d02SixRawGaussianTerm T t ρ α q.val := by
      apply Finset.sum_congr rfl
      intro q hq
      have hp := ((d02SixMainDomain_mem_iff _ P q.val).1 (Finset.mem_subtype.1 hq)).2
      rw [ite_eq_left hp]
    _ = _ := Finset.sum_subtype_eq_sum_filter _

def d02DiagonalToD01 (q : D02PositiveDiagonal) : DiagonalSixIndices :=
  ⟨((q.val 4 + 1, q.val 0 + 1, q.val 1 + 1),
    (q.val 5 + 1, q.val 2 + 1, q.val 3 + 1)), by
      constructor
      · have h := q.property
        unfold d02SixIsDiagonal d02SixIndexH d02SixIndexK d02SixIndexM d02SixIndexN at h
        simpa only [mul_comm, mul_left_comm, mul_assoc] using h
      · positivity⟩

def d02DiagonalFromD01 (x : DiagonalSixIndices) : D02PositiveDiagonal :=
  ⟨![d01LeftIndices x 1 - 1, d01LeftIndices x 2 - 1,
      d01RightIndices x 1 - 1, d01RightIndices x 2 - 1,
      d01LeftIndices x 0 - 1, d01RightIndices x 0 - 1], by
    have hl (i : Fin 3) : d01LeftIndices x i - 1 + 1 = d01LeftIndices x i :=
      Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01LeftIndices_pos x i))
    have hr (i : Fin 3) : d01RightIndices x i - 1 + 1 = d01RightIndices x i :=
      Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01RightIndices_pos x i))
    change ((d01LeftIndices x 1 - 1 + 1) * (d01LeftIndices x 2 - 1 + 1)) *
        (d01LeftIndices x 0 - 1 + 1) =
      ((d01RightIndices x 1 - 1 + 1) * (d01RightIndices x 2 - 1 + 1)) *
        (d01RightIndices x 0 - 1 + 1)
    simp_rw [hl, hr]
    simpa [d01LeftIndices, d01RightIndices, mul_comm, mul_left_comm, mul_assoc] using x.property.1⟩

/-- An explicit bijection preserves the original position of the zeta index
as row/column zero and the four amplifier positions as rows/columns one and two. -/
def d02PositiveDiagonalEquiv : D02PositiveDiagonal ≃ DiagonalSixIndices where
  toFun := d02DiagonalToD01
  invFun := d02DiagonalFromD01
  left_inv q := by
    apply Subtype.ext
    funext j
    fin_cases j <;> simp [d02DiagonalToD01, d02DiagonalFromD01, d01LeftIndices, d01RightIndices]
  right_inv x := by
    apply Subtype.ext
    have hl (i : Fin 3) : d01LeftIndices x i - 1 + 1 = d01LeftIndices x i :=
      Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01LeftIndices_pos x i))
    have hr (i : Fin 3) : d01RightIndices x i - 1 + 1 = d01RightIndices x i :=
      Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01RightIndices_pos x i))
    change ((d01LeftIndices x 0 - 1 + 1, d01LeftIndices x 1 - 1 + 1, d01LeftIndices x 2 - 1 + 1),
      (d01RightIndices x 0 - 1 + 1, d01RightIndices x 1 - 1 + 1, d01RightIndices x 2 - 1 + 1)) = x.val
    simp_rw [hl, hr]
    rfl

theorem d02_positive_diagonal_tsum_reindex (F : (Fin 6 → ℕ) → ℂ) :
    (∑' q : D02PositiveDiagonal, F q.val) =
      ∑' x : DiagonalSixIndices, F (d02DiagonalFromD01 x).val := by
  simpa only [d02PositiveDiagonalEquiv, Equiv.coe_fn_symm_mk] using
    (d02PositiveDiagonalEquiv.symm.tsum_eq (fun q : D02PositiveDiagonal => F q.val)).symm

/-- The six half-powers on the arithmetic diagonal combine to the original
common-product denominator. -/
theorem d02_diagonal_half_coefficient (q : D02PositiveDiagonal) :
    (∏ j : Fin 6, (q.val j + 1 : ℂ) ^ (-(1 / 2 : ℂ))) =
      (d01CommonProduct (d02DiagonalToD01 q) : ℂ) ^ (-1 : ℂ) := by
  let N := d01CommonProduct (d02DiagonalToD01 q)
  have hn : (N : ℂ) ≠ 0 := by
    exact_mod_cast (d01CommonProduct_pos (d02DiagonalToD01 q)).ne'
  have htriple (a b c : ℕ) :
      ((a * (b * c) : ℕ) : ℂ) ^ (-(1 / 2 : ℂ)) =
        (a : ℂ) ^ (-(1 / 2 : ℂ)) * (b : ℂ) ^ (-(1 / 2 : ℂ)) *
          (c : ℂ) ^ (-(1 / 2 : ℂ)) := by
    have h₁ := Complex.natCast_mul_natCast_cpow a (b * c) (-(1 / 2 : ℂ))
    have h₂ := Complex.natCast_mul_natCast_cpow b c (-(1 / 2 : ℂ))
    simp only [← Nat.cast_mul] at h₁ h₂
    rw [h₁, h₂]
    ring
  have hl : (N : ℂ) ^ (-(1 / 2 : ℂ)) =
      (q.val 4 + 1 : ℂ) ^ (-(1 / 2 : ℂ)) *
        (q.val 0 + 1 : ℂ) ^ (-(1 / 2 : ℂ)) * (q.val 1 + 1 : ℂ) ^ (-(1 / 2 : ℂ)) := by
    change (((q.val 4 + 1) * ((q.val 0 + 1) * (q.val 1 + 1)) : ℕ) : ℂ) ^
      (-(1 / 2 : ℂ)) = _
    simpa only [Nat.cast_add, Nat.cast_one] using
      htriple (q.val 4 + 1) (q.val 0 + 1) (q.val 1 + 1)
  have hr : (N : ℂ) ^ (-(1 / 2 : ℂ)) =
      (q.val 5 + 1 : ℂ) ^ (-(1 / 2 : ℂ)) *
        (q.val 2 + 1 : ℂ) ^ (-(1 / 2 : ℂ)) * (q.val 3 + 1 : ℂ) ^ (-(1 / 2 : ℂ)) := by
    have hd := q.property
    unfold d02SixIsDiagonal d02SixIndexH d02SixIndexK d02SixIndexM d02SixIndexN at hd
    have hN : N = (q.val 5 + 1) * ((q.val 2 + 1) * (q.val 3 + 1)) := by
      simpa [N, d01CommonProduct, d02DiagonalToD01, mul_comm, mul_left_comm, mul_assoc] using hd
    rw [hN]
    simpa only [Nat.cast_add, Nat.cast_one] using
      htriple (q.val 5 + 1) (q.val 2 + 1) (q.val 3 + 1)
  calc
    _ = (N : ℂ) ^ (-(1 / 2 : ℂ)) * (N : ℂ) ^ (-(1 / 2 : ℂ)) := by
      rw [Fin.prod_univ_six]
      calc
        _ = ((q.val 4 + 1 : ℂ) ^ (-(1 / 2 : ℂ)) *
              (q.val 0 + 1 : ℂ) ^ (-(1 / 2 : ℂ)) *
              (q.val 1 + 1 : ℂ) ^ (-(1 / 2 : ℂ))) *
            ((q.val 5 + 1 : ℂ) ^ (-(1 / 2 : ℂ)) *
              (q.val 2 + 1 : ℂ) ^ (-(1 / 2 : ℂ)) *
              (q.val 3 + 1 : ℂ) ^ (-(1 / 2 : ℂ))) := by ring
        _ = _ := congrArg₂ (fun x y : ℂ => x * y) hl.symm hr.symm
    _ = (N : ℂ) ^ ((-(1 / 2 : ℂ)) + (-(1 / 2 : ℂ))) :=
      (Complex.cpow_add _ _ hn).symm
    _ = _ := by norm_num [N]

/-- The unshifted diagonal coefficient is literally 1/N for the common
positive product N used in the original D01 arithmetic measure. -/
theorem d02_diagonal_half_coefficient_eq_one_div (q : D02PositiveDiagonal) :
    (∏ j : Fin 6, (q.val j + 1 : ℂ) ^ (-(1 / 2 : ℂ))) =
      1 / (d01CommonProduct (d02DiagonalToD01 q) : ℂ) := by
  rw [d02_diagonal_half_coefficient, Complex.cpow_neg_one, one_div]

/-- The literal six-index coefficient on Hm=Kn is the original D01 shifted
arithmetic coefficient, including its common-product denominator. -/
theorem d02_diagonal_shifted_coefficient (T : ℝ) (σ : Fin 2 → ℂ)
    (q : D02PositiveDiagonal) :
    d02ShiftedSqrtCoefficient T (d02SixZetaShifts σ) q.val =
      literalDiagonalSixTerm ![σ 0 / (Real.log T : ℂ), 0, 0]
        ![σ 1 / (Real.log T : ℂ), 0, 0] (d02DiagonalToD01 q) := by
  have hs (j : Fin 6) (z : ℂ) :
      (q.val j + 1 : ℂ) ^ (-(1 / 2 : ℂ) - z) =
        (q.val j + 1 : ℂ) ^ (-(1 / 2 : ℂ)) * (q.val j + 1 : ℂ) ^ (-z) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by exact_mod_cast Nat.succ_ne_zero (q.val j))]
  have ht : literalDiagonalSixTerm ![σ 0 / (Real.log T : ℂ), 0, 0]
      ![σ 1 / (Real.log T : ℂ), 0, 0] (d02DiagonalToD01 q) =
      ((q.val 4 + 1 : ℂ) ^ (-(σ 0 / (Real.log T : ℂ))) *
        (q.val 5 + 1 : ℂ) ^ (-(σ 1 / (Real.log T : ℂ)))) *
          (d01CommonProduct (d02DiagonalToD01 q) : ℂ) ^ (-1 : ℂ) := by
    simp [literalDiagonalSixTerm, literalTripleDirichletTerm, d02DiagonalToD01,
      d01CommonProduct, shiftedPowerArithmetic]
  rw [ht, ← d02_diagonal_half_coefficient q]
  unfold d02ShiftedSqrtCoefficient d02SixZetaShifts
  simp only [Fin.prod_univ_six]
  norm_num
  rw [hs 4, hs 5]
  ring

/-- On the literal Hm=Kn diagonal the entire oscillatory factor is one,
leaving exactly the original D01 shifted arithmetic term and four profiles. -/
theorem d02SixRawGaussianTerm_diagonal_identity (T t : ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (q : D02PositiveDiagonal) :
    d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q.val =
      literalDiagonalSixTerm ![σ 0 / (Real.log T : ℂ), 0, 0]
        ![σ 1 / (Real.log T : ℂ), 0, 0] (d02DiagonalToD01 q) *
        d02SixProfileMultiplier T ρ q.val *
        (d02GaussianV0 (2 * Real.pi * (d02SixIndexM q.val : ℝ) *
          (d02SixIndexN q.val : ℝ) / t) : ℂ) := by
  have hn : ((d02SixIndexK q.val * d02SixIndexN q.val : ℕ) : ℝ) ≠ 0 := by
    unfold d02SixIndexK d02SixIndexN
    positivity
  have hd : (((d02SixIndexH q.val * d02SixIndexM q.val : ℕ) : ℝ) /
      ((d02SixIndexK q.val * d02SixIndexN q.val : ℕ) : ℝ)) = 1 := by
    rw [q.property, div_self hn]
  rw [d02SixRawGaussianTerm_eq_phase_model, hd, Real.log_one,
    mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    d02_diagonal_shifted_coefficient]
  ring

theorem d02SixProfileMultiplier_diagonal_logPoint_identity (T : ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (q : D02PositiveDiagonal) :
    d02SixProfileMultiplier T ρ q.val =
      (ρ 0 ((d01LogPoint (Real.log T) (d02DiagonalToD01 q)).1 1) : ℂ) *
      (ρ 1 ((d01LogPoint (Real.log T) (d02DiagonalToD01 q)).1 2) : ℂ) *
      (ρ 2 ((d01LogPoint (Real.log T) (d02DiagonalToD01 q)).2 1) : ℂ) *
      (ρ 3 ((d01LogPoint (Real.log T) (d02DiagonalToD01 q)).2 2) : ℂ) := by
  simp [d02SixProfileMultiplier, Fin.prod_univ_four, d01LogPoint,
    d01LeftIndices, d01RightIndices, d02DiagonalToD01, Fin.castAdd]

theorem d02SixRawGaussianTerm_fromD01_identity (T t : ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (x : DiagonalSixIndices) :
    d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ))
        (d02DiagonalFromD01 x).val =
      literalDiagonalSixTerm ![σ 0 / (Real.log T : ℂ), 0, 0]
        ![σ 1 / (Real.log T : ℂ), 0, 0] x *
        ((ρ 0 ((d01LogPoint (Real.log T) x).1 1) : ℂ) *
         (ρ 1 ((d01LogPoint (Real.log T) x).1 2) : ℂ) *
         (ρ 2 ((d01LogPoint (Real.log T) x).2 1) : ℂ) *
         (ρ 3 ((d01LogPoint (Real.log T) x).2 2) : ℂ)) *
        (d02GaussianV0 (2 * Real.pi *
          ((d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ)) / t) : ℂ) := by
  have he : d02DiagonalToD01 (d02DiagonalFromD01 x) = x :=
    d02PositiveDiagonalEquiv.apply_symm_apply x
  have hm : d02SixIndexM (d02DiagonalFromD01 x).val = d01LeftIndices x 0 := by
    simpa [d02SixIndexM, d02DiagonalFromD01] using
      Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01LeftIndices_pos x 0))
  have hn : d02SixIndexN (d02DiagonalFromD01 x).val = d01RightIndices x 0 := by
    simpa [d02SixIndexN, d02DiagonalFromD01] using
      Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01RightIndices_pos x 0))
  rw [d02SixRawGaussianTerm_diagonal_identity,
    d02SixProfileMultiplier_diagonal_logPoint_identity, he, hm, hn]
  rw [show 2 * Real.pi * (d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ) =
    2 * Real.pi * ((d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ)) by ring]

def d02GaussianDiagonalTest (L t : ℝ) (ρ : Fin 4 → ℝ → ℂ) (w : D01LogSpace → ℂ)
    (y : D01LogSpace) : ℂ :=
  w y * (ρ 0 (y.1 1) * ρ 1 (y.1 2) * ρ 2 (y.2 1) * ρ 3 (y.2 2)) *
    (d02GaussianV0 (2 * Real.pi * Real.exp (L * (y.1 0 + y.2 0)) / t) : ℂ)

theorem d02GaussianDiagonalTest_logPoint {L : ℝ} (hL : 0 < L) (t : ℝ)
    (ρ : Fin 4 → ℝ → ℂ) (w : D01LogSpace → ℂ) (x : DiagonalSixIndices) :
    d02GaussianDiagonalTest L t ρ w (d01LogPoint L x) =
      w (d01LogPoint L x) *
        (ρ 0 ((d01LogPoint L x).1 1) * ρ 1 ((d01LogPoint L x).1 2) *
          ρ 2 ((d01LogPoint L x).2 1) * ρ 3 ((d01LogPoint L x).2 2)) *
        (d02GaussianV0 (2 * Real.pi *
          ((d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ)) / t) : ℂ) := by
  have he : L * ((d01LogPoint L x).1 0 + (d01LogPoint L x).2 0) =
      Real.log (d01LeftIndices x 0 : ℝ) + Real.log (d01RightIndices x 0 : ℝ) := by
    dsimp [d01LogPoint]
    field_simp [hL.ne']
  unfold d02GaussianDiagonalTest
  rw [he, Real.exp_add, Real.exp_log (by exact_mod_cast d01LeftIndices_pos x 0),
    Real.exp_log (by exact_mod_cast d01RightIndices_pos x 0)]

/-- The literal Gaussian arithmetic diagonal has the original D01 mass
normalization L^-9/N, with no assumed measure or moment limit. -/
theorem d02GaussianDiagonal_measure_identity {L : ℝ} (hL : 0 < L) (t : ℝ)
    (ρ : Fin 4 → ℝ → ℂ) (w : D01LogSpace → ℂ) :
    (∫ y, d02GaussianDiagonalTest L t ρ w y ∂d01DiagonalMeasure L) =
      ∑' x : DiagonalSixIndices, d01AtomicWeight L x •
        (w (d01LogPoint L x) *
          (ρ 0 ((d01LogPoint L x).1 1) * ρ 1 ((d01LogPoint L x).1 2) *
            ρ 2 ((d01LogPoint L x).2 1) * ρ 3 ((d01LogPoint L x).2 2)) *
          (d02GaussianV0 (2 * Real.pi *
            ((d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ)) / t) : ℂ)) := by
  rw [d01DiagonalMeasure_integral hL.le]
  apply tsum_congr
  intro x
  rw [d02GaussianDiagonalTest_logPoint hL]

/-- The original shifted arithmetic six-index term, rather than an abstract
weight, is the Gaussian diagonal divided by L^9. -/
theorem d02GaussianDiagonal_shifted_measure_identity {L : ℝ} (hL : 0 < L) (t : ℝ)
    (ρ : Fin 4 → ℝ → ℂ) (a b : Fin 3 → ℂ) :
    (∫ y, d02GaussianDiagonalTest L t ρ (d01ComplexLaplaceWeight (a, b)) y
      ∂d01DiagonalMeasure L) =
      (∑' x : DiagonalSixIndices,
        literalDiagonalSixTerm (fun i => a i / (L : ℂ)) (fun j => b j / (L : ℂ)) x *
          (ρ 0 ((d01LogPoint L x).1 1) * ρ 1 ((d01LogPoint L x).1 2) *
            ρ 2 ((d01LogPoint L x).2 1) * ρ 3 ((d01LogPoint L x).2 2)) *
          (d02GaussianV0 (2 * Real.pi *
            ((d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ)) / t) : ℂ)) / (L : ℂ) ^ 9 := by
  rw [d02GaussianDiagonal_measure_identity hL, ← tsum_div_const]
  apply tsum_congr
  intro x
  rw [Complex.real_smul]
  have ha := d01Atomic_complexLaplace_identity L a b x
  calc
    _ = ((d01AtomicWeight L x : ℂ) * d01ComplexLaplaceWeight (a, b) (d01LogPoint L x)) *
        ((ρ 0 ((d01LogPoint L x).1 1) * ρ 1 ((d01LogPoint L x).1 2) *
          ρ 2 ((d01LogPoint L x).2 1) * ρ 3 ((d01LogPoint L x).2 2)) *
          (d02GaussianV0 (2 * Real.pi *
            ((d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ)) / t) : ℂ)) := by ring
    _ = _ := by rw [ha]; ring

theorem d02GaussianDiagonal_masked_shifted_measure_identity {L : ℝ}
    (hL : 0 < L) (t : ℝ) (ρ : Fin 4 → ℝ → ℂ) (a b : Fin 3 → ℂ)
    (M : D01LogSpace → ℂ) :
    (∫ y, M y * d02GaussianDiagonalTest L t ρ (d01ComplexLaplaceWeight (a, b)) y
      ∂d01DiagonalMeasure L) =
      (∑' x : DiagonalSixIndices,
        M (d01LogPoint L x) *
          literalDiagonalSixTerm (fun i => a i / (L : ℂ)) (fun j => b j / (L : ℂ)) x *
          (ρ 0 ((d01LogPoint L x).1 1) * ρ 1 ((d01LogPoint L x).1 2) *
            ρ 2 ((d01LogPoint L x).2 1) * ρ 3 ((d01LogPoint L x).2 2)) *
          (d02GaussianV0 (2 * Real.pi *
            ((d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ)) / t) : ℂ)) / (L : ℂ) ^ 9 := by
  rw [d01DiagonalMeasure_integral hL.le, ← tsum_div_const]
  apply tsum_congr
  intro x
  rw [Complex.real_smul, d02GaussianDiagonalTest_logPoint hL]
  have ha := d01Atomic_complexLaplace_identity L a b x
  calc
    _ = ((d01AtomicWeight L x : ℂ) * d01ComplexLaplaceWeight (a, b) (d01LogPoint L x)) *
        (M (d01LogPoint L x) *
          (ρ 0 ((d01LogPoint L x).1 1) * ρ 1 ((d01LogPoint L x).1 2) *
            ρ 2 ((d01LogPoint L x).2 1) * ρ 3 ((d01LogPoint L x).2 2)) *
          (d02GaussianV0 (2 * Real.pi *
            ((d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ)) / t) : ℂ)) := by ring
    _ = _ := by rw [ha]; ring

/-- Exact passage from the original six-factor physical diagonal to the D01
atomic measure. The explicit index bijection and coefficient denominator are
used here, so the measure limit can be applied to this actual arithmetic sum. -/
theorem d02SixRawGaussianDiagonal_measure_identity {T : ℝ} (hT : 1 < T)
    (t : ℝ) (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) :
    (∑' q : D02PositiveDiagonal,
      d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q.val) /
        (Real.log T : ℂ) ^ 9 =
      ∫ y, d02GaussianDiagonalTest (Real.log T) t (fun j x => (ρ j x : ℂ))
        (d01ComplexLaplaceWeight (![σ 0, 0, 0], ![σ 1, 0, 0])) y
        ∂d01DiagonalMeasure (Real.log T) := by
  have hL : 0 < Real.log T := Real.log_pos hT
  rw [d02_positive_diagonal_tsum_reindex,
    d02GaussianDiagonal_shifted_measure_identity hL]
  apply congrArg (fun z : ℂ => z / (Real.log T : ℂ) ^ 9)
  apply tsum_congr
  intro x
  have he : d02DiagonalToD01 (d02DiagonalFromD01 x) = x :=
    d02PositiveDiagonalEquiv.apply_symm_apply x
  have hl : d01LeftIndices x 0 - 1 + 1 = d01LeftIndices x 0 :=
    Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01LeftIndices_pos x 0))
  have hr : d01RightIndices x 0 - 1 + 1 = d01RightIndices x 0 :=
    Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01RightIndices_pos x 0))
  rw [d02SixRawGaussianTerm_diagonal_identity,
    d02SixProfileMultiplier_diagonal_logPoint_identity, he]
  have hshift₁ : (fun i : Fin 3 => (![σ 0, 0, 0] i) / (Real.log T : ℂ)) =
      ![σ 0 / (Real.log T : ℂ), 0, 0] := by funext i; fin_cases i <;> simp
  have hshift₂ : (fun i : Fin 3 => (![σ 1, 0, 0] i) / (Real.log T : ℂ)) =
      ![σ 1 / (Real.log T : ℂ), 0, 0] := by funext i; fin_cases i <;> simp
  rw [hshift₁, hshift₂]
  have hm : d02SixIndexM (d02DiagonalFromD01 x).val = d01LeftIndices x 0 := by
    simpa [d02SixIndexM, d02DiagonalFromD01] using hl
  have hn : d02SixIndexN (d02DiagonalFromD01 x).val = d01RightIndices x 0 := by
    simpa [d02SixIndexN, d02DiagonalFromD01] using hr
  rw [hm, hn, show 2 * Real.pi * (d01LeftIndices x 0 : ℝ) *
      (d01RightIndices x 0 : ℝ) =
      2 * Real.pi * ((d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ)) by ring]

/-- The normalized full physical-height arithmetic diagonal is the time
mean of its actual D01 Gaussian measure, for any time weight. This is the
exact identity needed before applying the independently proved temporal
Gaussian-to-sharp limit. -/
theorem d02SixRawGaussianDiagonal_time_mean_identity {T : ℝ} (hT : 1 < T)
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (Ψ : ℝ → ℂ) :
    (∫ t : ℝ, Ψ (t / T) *
      ∑' q : D02PositiveDiagonal,
        d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q.val) /
        ((T : ℂ) * (Real.log T : ℂ) ^ 9) =
      (∫ t : ℝ, Ψ (t / T) *
        (∫ y, d02GaussianDiagonalTest (Real.log T) t (fun j x => (ρ j x : ℂ))
          (d01ComplexLaplaceWeight (![σ 0, 0, 0], ![σ 1, 0, 0])) y
          ∂d01DiagonalMeasure (Real.log T))) / (T : ℂ) := by
  rw [show (T : ℂ) * (Real.log T : ℂ) ^ 9 =
    (Real.log T : ℂ) ^ 9 * (T : ℂ) by ring,
    div_mul_eq_div_div, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mul_div_assoc, d02SixRawGaussianDiagonal_measure_identity hT]

end
end Sechstmoment
