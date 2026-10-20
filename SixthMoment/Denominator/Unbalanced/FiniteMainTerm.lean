import Mathlib.Analysis.Normed.Group.FunctionSeries
import SixthMoment.Denominator.Balanced.ActualGaussianConnector
import SixthMoment.Denominator.Unbalanced.MomentDefinitions
import SixthMoment.Denominator.Unbalanced.OffDiagonal

namespace SixthMoment
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def d04OneSidedPairCoefficient (T : ℝ) (σ : Fin 2 → ℂ) (n : ℕ × ℕ) : ℂ :=
  Complex.exp ((-σ 0+σ 1)/2) *
    d04OneSidedRawSummand (T ^ (3 : ℕ))
      (d04NegativeZetaArguments T 0 σ 0) (d04NegativeZetaArguments T 0 σ 1) n

def d04ProfileBox (T : ℝ) (a : Fin 4 → ℝ) : Finset (Fin 4 → ℕ) :=
  d02PositiveBox (fun j => ⌊T ^ (a j)⌋₊)

def d04ProfileH (h : Fin 4 → ℕ) : ℕ := (h 0+1)*(h 1+1)*(h 2+1)
def d04ProfileK (h : Fin 4 → ℕ) : ℕ := h 3+1

def d04ProfileCoefficient (T : ℝ) (ρ : Fin 4 → ℝ → ℝ) (h : Fin 4 → ℕ) : ℂ :=
  ∏ j, (ρ j (Real.log (h j+1 : ℝ)/Real.log T) : ℂ) *
    (h j+1 : ℂ)^(-(1/2 : ℂ))

def d04ProfileArgument (t : ℝ) : Fin 4 → ℂ :=
  ![criticalLinePoint t,criticalLinePoint t,criticalLinePoint t,1-criticalLinePoint t]

def d04ProfileTerm (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ) (h : Fin 4 → ℕ) : ℂ :=
  ∏ j, (ρ j (Real.log (h j+1 : ℝ)/Real.log T) : ℂ) /
    (h j+1 : ℂ)^(d04ProfileArgument t j)

def d04OneSidedModelCoefficient (T : ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (σ : Fin 2 → ℂ) (h : Fin 4 → ℕ) (n : ℕ × ℕ) : ℂ :=
  d04ProfileCoefficient T ρ h * d04OneSidedPairCoefficient T σ n

def d04OneSidedModelFrequency (h : Fin 4 → ℕ) (n : ℕ × ℕ) : ℝ :=
  Real.log ((((n.1+1)*(n.2+1)*d04ProfileK h : ℕ) : ℝ)/(d04ProfileH h : ℝ))

def d04OneSidedModelDiagonal (h : Fin 4 → ℕ) (n : ℕ × ℕ) : Prop :=
  (n.1+1)*(n.2+1)*d04ProfileK h = d04ProfileH h

instance d04OneSidedModelDiagonal_decidable (h : Fin 4 → ℕ) (n : ℕ × ℕ) :
    Decidable (d04OneSidedModelDiagonal h n) := inferInstanceAs
      (Decidable ((n.1+1)*(n.2+1)*d04ProfileK h = d04ProfileH h))

theorem d04ProfileH_pos (h : Fin 4 → ℕ) : 0 < d04ProfileH h := by
  unfold d04ProfileH
  positivity

theorem d04ProfileK_pos (h : Fin 4 → ℕ) : 0 < d04ProfileK h := Nat.succ_pos _

theorem d04UnbalancedAmplifier_finite_expansion {T : ℝ} (hT : 1<T)
    (t : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) :
    d04UnbalancedAmplifier T t ρ = ∑ h∈d04ProfileBox T a,d04ProfileTerm T t ρ h := by
  have he : d04UnbalancedAmplifier T t ρ =
      ∏ j : Fin 4, profileDirichletSum T (ρ j) (d04ProfileArgument t j) := by
    simp [d04UnbalancedAmplifier,d04ProfileArgument,Fin.prod_univ_four]
  rw [he]
  simp_rw [profileDirichletSum_eq_finite hT _ _ (hcap _) _]
  unfold d04ProfileBox d02PositiveBox d04ProfileTerm
  exact Finset.prod_univ_sum _ _

theorem d04_positive_profile_factor_phase {x : ℝ} (hx : 0<x) (r : ℂ) (t : ℝ) :
    r/(x : ℂ)^(criticalLinePoint t)=
      (r*(x : ℂ)^(-(1/2 : ℂ)))*Complex.exp (((-t*Real.log x : ℝ) : ℂ)*I) := by
  have he := d02_positive_shifted_dirichlet_phase_split hx (0 : ℂ) t
  simp only [add_zero,sub_zero] at he
  rw [div_eq_mul_one_div, show criticalLinePoint t=(1/2 : ℂ)+(t : ℂ)*I by rfl, he]
  ring

theorem d04_negative_profile_factor_phase {x : ℝ} (hx : 0<x) (r : ℂ) (t : ℝ) :
    r/(x : ℂ)^(1-criticalLinePoint t)=
      (r*(x : ℂ)^(-(1/2 : ℂ)))*Complex.exp (((t*Real.log x : ℝ) : ℂ)*I) := by
  have he := d02_positive_shifted_dirichlet_phase_split hx (0 : ℂ) (-t)
  simp only [add_zero,sub_zero,neg_neg] at he
  have hs : 1-criticalLinePoint t=(1/2 : ℂ)+((-t : ℝ) : ℂ)*I := by
    unfold criticalLinePoint
    push_cast
    ring
  rw [div_eq_mul_one_div,hs,he]
  ring

theorem d04ProfileTerm_phase_identity (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (h : Fin 4 → ℕ) :
    d04ProfileTerm T t ρ h = d04ProfileCoefficient T ρ h *
      Complex.exp (((t*Real.log ((d04ProfileK h : ℝ)/(d04ProfileH h : ℝ)) : ℝ) : ℂ)*I) := by
  have hs (j : Fin 4) : (h j+1 : ℂ)=((h j+1 : ℝ) : ℂ) := by push_cast; rfl
  unfold d04ProfileTerm d04ProfileCoefficient
  simp only [Fin.prod_univ_four]
  change (((ρ 0 (Real.log (h 0+1 : ℝ)/Real.log T) : ℂ)/(h 0+1 : ℂ)^(criticalLinePoint t))*
    ((ρ 1 (Real.log (h 1+1 : ℝ)/Real.log T) : ℂ)/(h 1+1 : ℂ)^(criticalLinePoint t))*
    ((ρ 2 (Real.log (h 2+1 : ℝ)/Real.log T) : ℂ)/(h 2+1 : ℂ)^(criticalLinePoint t))*
    ((ρ 3 (Real.log (h 3+1 : ℝ)/Real.log T) : ℂ)/(h 3+1 : ℂ)^(1-criticalLinePoint t))) = _
  rw [hs 0,hs 1,hs 2,hs 3,
    d04_positive_profile_factor_phase (by positivity),
    d04_positive_profile_factor_phase (by positivity),
    d04_positive_profile_factor_phase (by positivity),
    d04_negative_profile_factor_phase (by positivity)]
  have hlog : Real.log ((d04ProfileK h : ℝ)/(d04ProfileH h : ℝ))=
      -Real.log (h 0+1 : ℝ)-Real.log (h 1+1 : ℝ)-Real.log (h 2+1 : ℝ)+
        Real.log (h 3+1 : ℝ) := by
    unfold d04ProfileH d04ProfileK
    push_cast
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity)]
    ring
  have he : Complex.exp (((-t*Real.log (h 0+1 : ℝ) : ℝ) : ℂ)*I)*
      Complex.exp (((-t*Real.log (h 1+1 : ℝ) : ℝ) : ℂ)*I)*
      Complex.exp (((-t*Real.log (h 2+1 : ℝ) : ℝ) : ℂ)*I)*
      Complex.exp (((t*Real.log (h 3+1 : ℝ) : ℝ) : ℂ)*I)=
      Complex.exp (((t*Real.log ((d04ProfileK h : ℝ)/(d04ProfileH h : ℝ)) : ℝ) : ℂ)*I) := by
    rw [← Complex.exp_add,← Complex.exp_add,← Complex.exp_add,hlog]
    congr 1
    push_cast
    ring
  rw [← he]
  ring

theorem d04ProfileH_cap {T : ℝ} (hT : 0 < T) (a : Fin 4 → ℝ)
    (h : Fin 4 → ℕ) (hh : h∈d04ProfileBox T a) :
    (d04ProfileH h : ℝ) ≤ T^(a 0+a 1+a 2) := by
  have hj (j : Fin 4) : (h j+1 : ℝ) ≤ T^(a j) := by
    have hn : h j+1 ≤ ⌊T^(a j)⌋₊ := Nat.succ_le_of_lt
      (Finset.mem_range.1 (Fintype.mem_piFinset.1 hh j))
    have hn' : (h j+1 : ℝ) ≤ (⌊T^(a j)⌋₊ : ℝ) := by exact_mod_cast hn
    exact hn'.trans (Nat.floor_le (Real.rpow_nonneg hT.le _))
  unfold d04ProfileH
  push_cast
  calc
    _ ≤ (T^(a 0)*T^(a 1))*T^(a 2) :=
      mul_le_mul (mul_le_mul (hj 0) (hj 1) (by positivity) (by positivity))
        (hj 2) (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hT, ← Real.rpow_add hT]

theorem d04ProfileCoefficient_mass_le {T F : ℝ} (hT : 0 < T) (hF : 0≤F)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ j x, |ρ j x|≤F) :
    (∑ h∈d04ProfileBox T a, ‖d04ProfileCoefficient T ρ h‖) ≤
      F^4*2^4*T^((∑ j,a j)/2) := by
  apply d02_restricted_height_coefficient_mass_le hT (pow_nonneg hF 4) a _ _
    (fun _ h => h)
  intro h hh
  unfold d04ProfileCoefficient d02ReciprocalSqrtWeight
  rw [norm_prod]
  calc
    _ ≤ ∏ j : Fin 4, F * (1/Real.sqrt (h j+1 : ℝ)) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j hj
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        show (h j+1 : ℂ)=((h j+1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
      norm_num
      have hp : (h j+1 : ℝ)^(-(1/2 : ℝ))=1/Real.sqrt (h j+1 : ℝ) := by
        rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
        exact inv_eq_one_div _
      rw [hp, ← one_div]
      exact mul_le_mul_of_nonneg_right (hρ j _) (by positivity)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem d04_negative_arguments_time_split (T t : ℝ) (σ : Fin 2 → ℂ) (j : Fin 2) :
    d04NegativeZetaArguments T t σ j=
      d04NegativeZetaArguments T 0 σ j-(t : ℂ)*I := by
  fin_cases j <;> simp [d04NegativeZetaArguments, criticalLinePoint] <;> ring

theorem d04_cpow_imaginary_time_split {x : ℝ} (hx : 0<x) (s : ℂ) (t : ℝ) :
    (x : ℂ)^(-(s-(t : ℂ)*I))=
      (x : ℂ)^(-s)*Complex.exp (((t*Real.log x : ℝ) : ℂ)*I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), ← Complex.exp_add,
    ← Complex.ofReal_log hx.le]
  congr 1
  push_cast
  ring

theorem d04OneSidedCenteredPair_phase_identity (T t : ℝ) (σ : Fin 2 → ℂ) :
    d04OneSidedCenteredPair T t σ = ∑' n : ℕ × ℕ,
      d04OneSidedPairCoefficient T σ n *
        Complex.exp (((t*Real.log ((n.1+1 : ℝ)*(n.2+1 : ℝ)) : ℝ) : ℂ)*I) := by
  unfold d04OneSidedCenteredPair d04OneSidedRawSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold d04OneSidedPairCoefficient d04OneSidedRawSummand
  rw [d04_negative_arguments_time_split T t σ 0,
    d04_negative_arguments_time_split T t σ 1,
    show (n.1+1 : ℂ)=((n.1+1 : ℝ) : ℂ) by push_cast; rfl,
    show (n.2+1 : ℂ)=((n.2+1 : ℝ) : ℂ) by push_cast; rfl,
    d04_cpow_imaginary_time_split (by positivity),
    d04_cpow_imaginary_time_split (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  have he : Complex.exp (((t*Real.log (n.1+1 : ℝ) : ℝ) : ℂ)*I)*
      Complex.exp (((t*Real.log (n.2+1 : ℝ) : ℝ) : ℂ)*I)=
      Complex.exp (((t*(Real.log (n.1+1 : ℝ)+Real.log (n.2+1 : ℝ)) : ℝ) : ℂ)*I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← he]
  ring

theorem d04_nonnegative_realPart_cpow_norm_le_one {x : ℝ} (hx : 1 ≤ x)
    (s : ℂ) (hs : 0 ≤ s.re) : ‖(x : ℂ) ^ (-s)‖ ≤ 1 := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hxp, Complex.neg_re]
  exact (Real.rpow_le_rpow_of_exponent_le hx (neg_nonpos.mpr hs)).trans_eq
    (Real.rpow_zero _)

theorem d04_negative_arguments_re_nonneg {T R : ℝ} (_hR : 0 ≤ R)
    (hL : 0 < Real.log T) (hRL : 2 * R ≤ Real.log T)
    (σ : Fin 2 → ℂ) (hσ : ∀ j, ‖σ j‖ ≤ R) (t : ℝ) (j : Fin 2) :
    0 ≤ (d04NegativeZetaArguments T t σ j).re := by
  have hre (k : Fin 2) : |(σ k).re| ≤ R := (Complex.abs_re_le_norm _).trans (hσ k)
  have hup (k : Fin 2) : (σ k).re / Real.log T ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hL).2
    linarith [le_abs_self ((σ k).re), hre k]
  have hlow (k : Fin 2) : -(1 / 2 : ℝ) ≤ (σ k).re / Real.log T := by
    apply (le_div_iff₀ hL).2
    linarith [neg_le_abs ((σ k).re), hre k]
  fin_cases j
  · change 0≤(1-criticalLinePoint t-σ 0/(Real.log T : ℂ)).re
    simp only [Complex.sub_re,Complex.one_re,criticalLinePoint_re,Complex.div_ofReal_re]
    linarith [hup 0]
  · change 0≤(1-criticalLinePoint t+σ 1/(Real.log T : ℂ)).re
    simp only [Complex.add_re,Complex.sub_re,Complex.one_re,criticalLinePoint_re,Complex.div_ofReal_re]
    linarith [hlow 1]

theorem d04_oneSided_pair_coefficient_norm_le {T R : ℝ} (_hT : 0 < T)
    (hR : 0 ≤ R) (hL : 0 < Real.log T) (hRL : 2 * R ≤ Real.log T)
    (σ : Fin 2 → ℂ) (hσ : ∀ j, ‖σ j‖ ≤ R) (n : ℕ × ℕ) :
    ‖d04OneSidedPairCoefficient T σ n‖ ≤ Real.exp R * d04ExponentialPairWeight T n := by
  have hcenter : ‖Complex.exp ((-σ 0+σ 1)/2)‖ ≤ Real.exp R := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.2
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.neg_re]
    have h0 := (Complex.abs_re_le_norm (σ 0)).trans (hσ 0)
    have h1 := (Complex.abs_re_le_norm (σ 1)).trans (hσ 1)
    linarith [neg_le_abs ((σ 0).re), le_abs_self ((σ 1).re)]
  have hm := d04_nonnegative_realPart_cpow_norm_le_one
    (show (1 : ℝ) ≤ n.1+1 by linarith [Nat.cast_nonneg (α := ℝ) n.1])
    (d04NegativeZetaArguments T 0 σ 0)
    (d04_negative_arguments_re_nonneg hR hL hRL σ hσ 0 0)
  have hn := d04_nonnegative_realPart_cpow_norm_le_one
    (show (1 : ℝ) ≤ n.2+1 by linarith [Nat.cast_nonneg (α := ℝ) n.2])
    (d04NegativeZetaArguments T 0 σ 1)
    (d04_negative_arguments_re_nonneg hR hL hRL σ hσ 0 1)
  have hm' : ‖(n.1+1 : ℂ)^(-d04NegativeZetaArguments T 0 σ 0)‖ ≤ 1 := by
    convert hm using 1
    push_cast
    rfl
  have hn' : ‖(n.2+1 : ℂ)^(-d04NegativeZetaArguments T 0 σ 1)‖ ≤ 1 := by
    convert hn using 1
    push_cast
    rfl
  unfold d04OneSidedPairCoefficient d04OneSidedRawSummand
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp R * ((1 * 1) * d04ExponentialPairWeight T n) := by
      apply mul_le_mul hcenter _ (by positivity) (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hm' hn' (norm_nonneg _) zero_le_one) (Real.exp_pos _).le
    _ = _ := by ring

theorem d04ProfileCoefficient_zero_outside_box {T : ℝ} (hT : 1<T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (h : Fin 4 → ℕ)
    (hh : h∉d04ProfileBox T a) : d04ProfileCoefficient T ρ h=0 := by
  have hn : ¬∀ j : Fin 4,h j∈Finset.range ⌊T^(a j)⌋₊ := by
    intro hj
    exact hh (Fintype.mem_piFinset.2 hj)
  push Not at hn
  obtain ⟨j,hj⟩ := hn
  have hn' : ⌊T^(a j)⌋₊<h j+1 := by
    have : ⌊T^(a j)⌋₊≤h j := by simpa only [Finset.mem_range,not_lt] using hj
    omega
  have hp : T^(a j)<(h j+1 : ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using Nat.lt_of_floor_lt hn'
  have ha : a j<Real.log (h j+1 : ℝ)/Real.log T :=
    (lt_div_iff₀ (Real.log_pos hT)).2
      (Real.lt_log_of_rpow_lt (zero_lt_one.trans hT) hp)
  unfold d04ProfileCoefficient
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hcap j _ ha]

theorem d04_oneSided_model_coefficient_norm_summable {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hL : 0<Real.log T) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : Fin 2 → ℂ) (hσ : ∀ j,‖σ j‖≤R) :
    Summable (fun u : (Fin 4 → ℕ) × (ℕ × ℕ) =>
      ‖d04OneSidedModelCoefficient T ρ σ u.1 u.2‖) := by
  have hp : Summable (fun h => ‖d04ProfileCoefficient T ρ h‖) := by
    apply summable_of_ne_finset_zero (s:=d04ProfileBox T a)
    intro h hh
    rw [d04ProfileCoefficient_zero_outside_box hT a ρ hcap h hh,norm_zero]
  have hs := (d04_exponential_coefficient_mass hT.le (Real.exp_pos R).le
    (d04OneSidedPairCoefficient T σ)
    (d04_oneSided_pair_coefficient_norm_le (zero_lt_one.trans hT) hR hL hRL σ hσ)).1
  exact hp.mul_norm hs

theorem d04_oneSided_integral_tsum {ι : Type*} [Countable ι]
    (F : ℝ → ℂ) (hF : Integrable F) (c : ι → ℂ) (ℓ : ι → ℝ)
    (hc : Summable (fun i => ‖c i‖)) :
    (∫ t : ℝ, F t * ∑' i, c i * Complex.exp (((ℓ i * t : ℝ) : ℂ) * I)) =
      ∑' i, c i * ∫ t : ℝ, F t * Complex.exp (((ℓ i * t : ℝ) : ℂ) * I) := by
  let g : ι → ℝ → ℂ := fun i t =>
    F t * (c i * Complex.exp (((ℓ i * t : ℝ) : ℂ) * I))
  have hnorm (i : ι) (t : ℝ) : ‖g i t‖ = ‖F t‖ * ‖c i‖ := by
    dsimp [g]
    rw [norm_mul, norm_mul, Complex.norm_exp]
    simp
  have hi (i : ι) : Integrable (g i) := by
    apply (hF.norm.mul_const ‖c i‖).mono'
      (hF.aestronglyMeasurable.mul
        ((continuous_const.mul
          (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable))
    exact Eventually.of_forall fun t => (hnorm i t).le
  have hmass (i : ι) : (∫ t : ℝ, ‖g i t‖) = (∫ t : ℝ, ‖F t‖) * ‖c i‖ := by
    simp_rw [hnorm]
    exact integral_mul_const _ _
  have hs : Summable (fun i => ∫ t : ℝ, ‖g i t‖) := by
    simp_rw [hmass]
    exact hc.mul_left _
  have he : (∫ t : ℝ, F t * ∑' i, c i * Complex.exp (((ℓ i * t : ℝ) : ℂ) * I)) =
      ∫ t : ℝ, ∑' i, g i t := by
    apply integral_congr_ae
    exact Eventually.of_forall fun t => (tsum_mul_left (f := fun i =>
      c i * Complex.exp (((ℓ i * t : ℝ) : ℂ) * I))).symm
  rw [he, ← integral_tsum_of_summable_integral_norm hi hs]
  apply tsum_congr
  intro i
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by dsimp [g]; ring

theorem d04_oneSided_fourier_tsum {ι : Type*} [Countable ι]
    (Φ : ℝ → ℂ) {T : ℝ} (hT : 0 < T) (hΦ : Integrable Φ)
    (c : ι → ℂ) (ℓ : ι → ℝ) (hc : Summable (fun i => ‖c i‖)) :
    (∫ t : ℝ, Φ (t / T) * ∑' i, c i * Complex.exp (((ℓ i * t : ℝ) : ℂ) * I)) =
      ∑' i, c i * a03ProfileTimeFourier Φ T (ℓ i) := by
  exact d04_oneSided_integral_tsum _
    ((integrable_comp_div_iff Φ hT.ne').2 hΦ) c ℓ hc

theorem d04_summable_fourier_coefficients {ι : Type*}
    (Φ : ℝ → ℂ) (hΦK : HasCompactSupport Φ) (hΦ : ContDiff ℝ ∞ Φ)
    {T : ℝ} (hT : 0 < T) (c : ι → ℂ) (ℓ : ι → ℝ)
    (hc : Summable (fun i => ‖c i‖)) :
    Summable (fun i => ‖c i * a03ProfileTimeFourier Φ T (ℓ i)‖) := by
  obtain ⟨C, hC, hb⟩ := a03_profile_frequency_power_bound hΦK hΦ 0
  have hbound (i : ι) : ‖c i * a03ProfileTimeFourier Φ T (ℓ i)‖ ≤ ‖c i‖ * (T * C) := by
    have hh := hb (T * ℓ i)
    simp only [pow_zero, one_mul] at hh
    rw [a03_profile_time_fourier_rescaling Φ hT (ℓ i), norm_mul,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hT.le]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hT.le) (norm_nonneg _)
  exact Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound (hc.mul_right (T * C))

theorem d04_oneSided_exact_diagonal_partition {ι : Type*}
    (v : ι → ℂ) (hc : Summable (fun i => ‖v i‖)) (p : ι → Prop) [DecidablePred p] :
    (∑' i, v i) = (∑' i, if p i then v i else 0) +
      ∑' i, if p i then 0 else v i := by
  have h1 : Summable (fun i => if p i then v i else 0) := by
    apply Summable.of_norm_bounded hc
    intro i
    split_ifs <;> simp
  have h2 : Summable (fun i => if p i then 0 else v i) := by
    apply Summable.of_norm_bounded hc
    intro i
    split_ifs <;> simp
  rw [← h1.tsum_add h2]
  apply tsum_congr
  intro i
  split_ifs <;> simp

end
end SixthMoment
