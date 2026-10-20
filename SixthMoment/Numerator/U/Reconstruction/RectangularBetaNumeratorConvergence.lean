import Mathlib.MeasureTheory.Integral.Prod
import SixthMoment.Analysis.Beta.WeakConvergence
import SixthMoment.Certificate.Exact.Numerator
import SixthMoment.Numerator.Kernels.Integral


namespace SixthMoment
open Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def rectangularNumeratorTerm (tr : Finite.NumeratorTerm) (x y : ℝ) : ℝ :=
  ((tr.coefficient : ℝ)/201600)*x^tr.i*y^tr.j

def rectangularNumeratorTerms (ts : List Finite.NumeratorTerm) (x y : ℝ) : ℝ :=
  (ts.map (fun tr => rectangularNumeratorTerm tr x y)).sum

def rectangularNumeratorFinite (p : Fin 5 → ℝ) (x y : ℝ) : ℝ :=
  ∑ r : Fin 5, p r*rectangularNumeratorTerms (Finite.numeratorTerms r.val) x y

theorem rectangular_numerator_finite_eq_kernel (p : Fin 5 → ℝ) {x y : ℝ} (hxy : x ≤ y) :
    rectangularNumeratorFinite p x y = numeratorPointKernel p x y := by
  rw [numeratorPointKernel_polynomial p hxy]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  fin_cases r
  all_goals first | rw [numerator_integral_0] | rw [numerator_integral_1] |
    rw [numerator_integral_2] | rw [numerator_integral_3] | rw [numerator_integral_4]
  all_goals norm_num [rectangularNumeratorTerms, rectangularNumeratorTerm,
      Finite.numeratorTerms, Finite.numeratorTerms0, Finite.numeratorTerms1,
      Finite.numeratorTerms2, Finite.numeratorTerms3, Finite.numeratorTerms4,
      numeratorClosed0, numeratorClosed1, numeratorClosed2, numeratorClosed3, numeratorClosed4]
  all_goals ring

private theorem rectangular_numerator_terms_continuous (ts : List Finite.NumeratorTerm) :
    Continuous (fun z : ℝ × ℝ => rectangularNumeratorTerms ts z.1 z.2) := by
  induction ts with
  | nil => simpa [rectangularNumeratorTerms] using (continuous_const : Continuous (fun _ : ℝ × ℝ => (0:ℝ)))
  | cons tr ts ih =>
    simp only [rectangularNumeratorTerms, List.map_cons, List.sum_cons] at *
    have htr : Continuous (fun z : ℝ × ℝ => rectangularNumeratorTerm tr z.1 z.2) := by
      unfold rectangularNumeratorTerm
      fun_prop
    exact htr.add ih

theorem rectangular_numerator_finite_continuous (p : Fin 5 → ℝ) :
    Continuous (fun z : ℝ × ℝ => rectangularNumeratorFinite p z.1 z.2) := by
  unfold rectangularNumeratorFinite
  apply continuous_finsetSum
  intro r _
  exact continuous_const.mul (rectangular_numerator_terms_continuous _)

theorem rectangular_numerator_reflected_eq (p : Fin 5 → ℝ) {η x y : ℝ}
    (hη : η < 1/4) (hx : x ∈ Set.Icc (0:ℝ) η) (hy : y ∈ Set.Icc (0:ℝ) η) :
    numeratorPointKernel p x (1-y) = rectangularNumeratorFinite p x (1-y) := by
  symm
  apply rectangular_numerator_finite_eq_kernel
  linarith [hx.2, hy.2]

def rectangularBetaPowerMoment (η : ℝ) (n k r : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..η, x^r*betaScaledProfile η n k x

def rectangularBetaReflectedMoment (η : ℝ) (n k r : ℕ) : ℝ :=
  ∫ y in (0:ℝ)..η, (1-y)^r*betaScaledProfile η n k y

def rectangularNumeratorInnerExpansion (η : ℝ) (n k : ℕ)
    (ts : List Finite.NumeratorTerm) (x : ℝ) : ℝ :=
  (ts.map (fun tr => ((tr.coefficient : ℝ)/201600)*x^tr.i*
    rectangularBetaReflectedMoment η n k tr.j)).sum

def rectangularNumeratorMomentExpansion (η : ℝ) (n k m ℓ : ℕ)
    (ts : List Finite.NumeratorTerm) : ℝ :=
  (ts.map (fun tr => ((tr.coefficient : ℝ)/201600)*
    rectangularBetaPowerMoment η n k tr.i*rectangularBetaReflectedMoment η m ℓ tr.j)).sum

def rectangularNumeratorBetaExpansion (η : ℝ) (n k m ℓ : ℕ) (p : Fin 5 → ℝ) : ℝ :=
  ∑ r : Fin 5, p r*rectangularNumeratorMomentExpansion η n k m ℓ (Finite.numeratorTerms r.val)

private theorem rectangular_numerator_terms_reflected_continuous
    (ts : List Finite.NumeratorTerm) (x : ℝ) :
    Continuous (fun y : ℝ => rectangularNumeratorTerms ts x (1-y)) :=
  (rectangular_numerator_terms_continuous ts).comp
    (continuous_const.prodMk (continuous_const.sub continuous_id))

private theorem rectangular_numerator_inner_expansion_continuous
    (η : ℝ) (n k : ℕ) (ts : List Finite.NumeratorTerm) :
    Continuous (rectangularNumeratorInnerExpansion η n k ts) := by
  change Continuous (fun x : ℝ =>
    (ts.map (fun tr => ((tr.coefficient : ℝ)/201600)*x^tr.i*
      rectangularBetaReflectedMoment η n k tr.j)).sum)
  induction ts with
  | nil => simpa [rectangularNumeratorInnerExpansion] using
      (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
  | cons tr ts ih =>
    simp only [List.map_cons, List.sum_cons] at *
    have hc : Continuous (fun x : ℝ => ((tr.coefficient : ℝ)/201600)*x^tr.i*
        rectangularBetaReflectedMoment η n k tr.j) := by fun_prop
    exact hc.add ih

private theorem rectangular_numerator_terms_inner_integral
    (η : ℝ) (n k : ℕ) (ts : List Finite.NumeratorTerm) (x : ℝ) :
    (∫ y in (0:ℝ)..η, betaScaledProfile η n k y*rectangularNumeratorTerms ts x (1-y)) =
      rectangularNumeratorInnerExpansion η n k ts x := by
  induction ts with
  | nil => simp [rectangularNumeratorTerms, rectangularNumeratorInnerExpansion]
  | cons tr ts ih =>
    simp only [rectangularNumeratorTerms, rectangularNumeratorInnerExpansion,
      List.map_cons, List.sum_cons, mul_add] at *
    have htr : Continuous (fun y : ℝ => betaScaledProfile η n k y*
        rectangularNumeratorTerm tr x (1-y)) := by
      unfold rectangularNumeratorTerm
      exact (betaScaled_continuous η n k).mul (by fun_prop)
    have hts : Continuous (fun y : ℝ => betaScaledProfile η n k y*
        (ts.map (fun tr => rectangularNumeratorTerm tr x (1-y))).sum) :=
      (betaScaled_continuous η n k).mul (rectangular_numerator_terms_reflected_continuous ts x)
    rw [intervalIntegral.integral_add (htr.intervalIntegrable _ _) (hts.intervalIntegrable _ _), ih]
    have he (y : ℝ) : betaScaledProfile η n k y*rectangularNumeratorTerm tr x (1-y) =
        (((tr.coefficient : ℝ)/201600)*x^tr.i)*((1-y)^tr.j*betaScaledProfile η n k y) := by
      unfold rectangularNumeratorTerm
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul]
    rfl

private theorem rectangular_numerator_terms_outer_integral
    (η : ℝ) (n k m ℓ : ℕ) (ts : List Finite.NumeratorTerm) :
    (∫ x in (0:ℝ)..η, betaScaledProfile η n k x*rectangularNumeratorInnerExpansion η m ℓ ts x) =
      rectangularNumeratorMomentExpansion η n k m ℓ ts := by
  induction ts with
  | nil => simp [rectangularNumeratorInnerExpansion, rectangularNumeratorMomentExpansion]
  | cons tr ts ih =>
    simp only [rectangularNumeratorInnerExpansion, rectangularNumeratorMomentExpansion,
      List.map_cons, List.sum_cons, mul_add] at *
    have htr : Continuous (fun x : ℝ => betaScaledProfile η n k x*
        (((tr.coefficient : ℝ)/201600)*x^tr.i*rectangularBetaReflectedMoment η m ℓ tr.j)) :=
      (betaScaled_continuous η n k).mul (by fun_prop)
    have hts : Continuous (fun x : ℝ => betaScaledProfile η n k x*
        (ts.map (fun tr => ((tr.coefficient : ℝ)/201600)*x^tr.i*
          rectangularBetaReflectedMoment η m ℓ tr.j)).sum) :=
      (betaScaled_continuous η n k).mul (rectangular_numerator_inner_expansion_continuous η m ℓ ts)
    rw [intervalIntegral.integral_add (htr.intervalIntegrable _ _) (hts.intervalIntegrable _ _), ih]
    have he (x : ℝ) : betaScaledProfile η n k x*
        (((tr.coefficient : ℝ)/201600)*x^tr.i*rectangularBetaReflectedMoment η m ℓ tr.j) =
        (((tr.coefficient : ℝ)/201600)*rectangularBetaReflectedMoment η m ℓ tr.j)*
          (x^tr.i*betaScaledProfile η n k x) := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul]
    unfold rectangularBetaPowerMoment
    ring

private theorem rectangular_numerator_finite_inner_integral
    (η : ℝ) (n k : ℕ) (p : Fin 5 → ℝ) (x : ℝ) :
    (∫ y in (0:ℝ)..η, betaScaledProfile η n k y*rectangularNumeratorFinite p x (1-y)) =
      ∑ r : Fin 5, p r*rectangularNumeratorInnerExpansion η n k (Finite.numeratorTerms r.val) x := by
  unfold rectangularNumeratorFinite
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    have he (y : ℝ) : betaScaledProfile η n k y*
        (p r*rectangularNumeratorTerms (Finite.numeratorTerms r.val) x (1-y)) =
        p r*(betaScaledProfile η n k y*rectangularNumeratorTerms (Finite.numeratorTerms r.val) x (1-y)) := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul, rectangular_numerator_terms_inner_integral]
  · intro r _
    exact ((betaScaled_continuous η n k).mul (continuous_const.mul
      (rectangular_numerator_terms_reflected_continuous _ x))).intervalIntegrable _ _

theorem rectangular_numerator_finite_two_beta_integral
    (η : ℝ) (n k m ℓ : ℕ) (p : Fin 5 → ℝ) :
    (∫ x in (0:ℝ)..η, ∫ y in (0:ℝ)..η,
      betaScaledProfile η n k x*betaScaledProfile η m ℓ y*
        rectangularNumeratorFinite p x (1-y)) =
      rectangularNumeratorBetaExpansion η n k m ℓ p := by
  have hp (x y : ℝ) : betaScaledProfile η n k x*betaScaledProfile η m ℓ y*
      rectangularNumeratorFinite p x (1-y) = betaScaledProfile η n k x*
        (betaScaledProfile η m ℓ y*rectangularNumeratorFinite p x (1-y)) := by ring
  simp_rw [hp, intervalIntegral.integral_const_mul, rectangular_numerator_finite_inner_integral,
    Finset.mul_sum]
  unfold rectangularNumeratorBetaExpansion
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    have he (x : ℝ) : betaScaledProfile η n k x*
        (p r*rectangularNumeratorInnerExpansion η m ℓ (Finite.numeratorTerms r.val) x) =
        p r*(betaScaledProfile η n k x*rectangularNumeratorInnerExpansion η m ℓ (Finite.numeratorTerms r.val) x) := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul, rectangular_numerator_terms_outer_integral]
  · intro r _
    exact ((betaScaled_continuous η n k).mul (continuous_const.mul
      (rectangular_numerator_inner_expansion_continuous η m ℓ _))).intervalIntegrable _ _

theorem rectangular_two_beta_numerator_integrable (p : Fin 5 → ℝ)
    {η : ℝ} (hη : η < 1/4) (n k m ℓ : ℕ) :
    Integrable (fun z : ℝ × ℝ => betaScaledProfile η n k z.1*
      betaScaledProfile η m ℓ z.2*numeratorPointKernel p z.1 (1-z.2))
      ((volume.restrict (Set.Icc (0:ℝ) η)).prod (volume.restrict (Set.Icc (0:ℝ) η))) := by
  have hf : Continuous (fun z : ℝ × ℝ => rectangularNumeratorFinite p z.1 (1-z.2)) :=
    (rectangular_numerator_finite_continuous p).comp
      (continuous_fst.prodMk (continuous_const.sub continuous_snd))
  have hc := ((betaScaled_continuous η n k).comp continuous_fst).mul
    ((betaScaled_continuous η m ℓ).comp continuous_snd) |>.mul hf
  rw [Measure.prod_restrict]
  apply (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).congr_fun
  · intro z hz
    dsimp only [Function.comp_apply, Pi.mul_apply]
    rw [rectangular_numerator_reflected_eq p hη hz.1 hz.2]
  · exact measurableSet_Icc.prod measurableSet_Icc

theorem rectangular_two_beta_numerator_inner (p : Fin 5 → ℝ)
    {η x : ℝ} (hη0 : 0 < η) (hη : η < 1/4)
    (hx : x ∈ Set.Icc (0:ℝ) η) (n k m ℓ : ℕ) :
    (∫ y in (0:ℝ)..η, betaScaledProfile η n k x*betaScaledProfile η m ℓ y*
      numeratorPointKernel p x (1-y)) =
      betaScaledProfile η n k x*∑ r : Fin 5, p r*
        rectangularNumeratorInnerExpansion η m ℓ (Finite.numeratorTerms r.val) x := by
  have he : (∫ y in (0:ℝ)..η, betaScaledProfile η n k x*betaScaledProfile η m ℓ y*
      numeratorPointKernel p x (1-y)) =
      ∫ y in (0:ℝ)..η, betaScaledProfile η n k x*betaScaledProfile η m ℓ y*
        rectangularNumeratorFinite p x (1-y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hη0.le] at hy
    dsimp only
    rw [rectangular_numerator_reflected_eq p hη hx hy]
  rw [he]
  have hp (y : ℝ) : betaScaledProfile η n k x*betaScaledProfile η m ℓ y*
      rectangularNumeratorFinite p x (1-y) = betaScaledProfile η n k x*
        (betaScaledProfile η m ℓ y*rectangularNumeratorFinite p x (1-y)) := by ring
  simp_rw [hp]
  rw [intervalIntegral.integral_const_mul, rectangular_numerator_finite_inner_integral]

theorem rectangular_two_beta_numerator_inner_integrable (p : Fin 5 → ℝ)
    {η x : ℝ} (hη0 : 0 < η) (hη : η < 1/4)
    (hx : x ∈ Set.Icc (0:ℝ) η) (n k m ℓ : ℕ) :
    IntervalIntegrable (fun y : ℝ => betaScaledProfile η n k x*betaScaledProfile η m ℓ y*
      numeratorPointKernel p x (1-y)) volume (0:ℝ) η := by
  have hf : Continuous (fun y : ℝ => rectangularNumeratorFinite p x (1-y)) :=
    (rectangular_numerator_finite_continuous p).comp
      (continuous_const.prodMk (continuous_const.sub continuous_id))
  have hc : Continuous (fun y : ℝ => betaScaledProfile η n k x*betaScaledProfile η m ℓ y*
      rectangularNumeratorFinite p x (1-y)) :=
    (continuous_const.mul (betaScaled_continuous η m ℓ)).mul hf
  apply (hc.continuousOn.congr ?_).intervalIntegrable_of_Icc hη0.le
  intro y hy
  dsimp only
  rw [rectangular_numerator_reflected_eq p hη hx hy]

theorem rectangular_two_beta_numerator_outer_integrable (p : Fin 5 → ℝ)
    {η : ℝ} (hη0 : 0 < η) (hη : η < 1/4) (n k m ℓ : ℕ) :
    IntervalIntegrable (fun x : ℝ => ∫ y in (0:ℝ)..η,
      betaScaledProfile η n k x*betaScaledProfile η m ℓ y*
        numeratorPointKernel p x (1-y)) volume (0:ℝ) η := by
  have hs : Continuous (fun x : ℝ => ∑ r : Fin 5, p r*
      rectangularNumeratorInnerExpansion η m ℓ (Finite.numeratorTerms r.val) x) := by
    apply continuous_finsetSum
    intro r _
    exact continuous_const.mul (rectangular_numerator_inner_expansion_continuous η m ℓ _)
  apply (((betaScaled_continuous η n k).mul hs).continuousOn.congr ?_).intervalIntegrable_of_Icc hη0.le
  intro x hx
  exact rectangular_two_beta_numerator_inner p hη0 hη hx n k m ℓ

theorem rectangular_two_beta_numerator_eq_expansion (p : Fin 5 → ℝ)
    {η : ℝ} (hη0 : 0 < η) (hη : η < 1/4) (n k m ℓ : ℕ) :
    (∫ x in (0:ℝ)..η, ∫ y in (0:ℝ)..η,
      betaScaledProfile η n k x*betaScaledProfile η m ℓ y*
        numeratorPointKernel p x (1-y)) =
      rectangularNumeratorBetaExpansion η n k m ℓ p := by
  rw [← rectangular_numerator_finite_two_beta_integral η n k m ℓ p]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hη0.le] at hx
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le hη0.le] at hy
  dsimp only
  rw [rectangular_numerator_reflected_eq p hη hx hy]

theorem rectangular_beta_power_moment_tendsto {η a : ℝ} (hη : 0 < η)
    (ha : 0 ≤ a) (haη : a ≤ η) (r : ℕ) :
    Tendsto (fun n : ℕ => rectangularBetaPowerMoment η n (betaProfileIndex η a n) r)
      atTop (nhds (a^r)) :=
  betaProfile_continuous_test_tendsto hη ha haη (fun x : ℝ => x^r)
    (continuous_id.pow r).continuousOn

theorem rectangular_beta_reflected_moment_tendsto {η b : ℝ} (hη : 0 < η)
    (hb : 0 ≤ b) (hbη : b ≤ η) (r : ℕ) :
    Tendsto (fun n : ℕ => rectangularBetaReflectedMoment η n (betaProfileIndex η b n) r)
      atTop (nhds ((1-b)^r)) :=
  betaProfile_continuous_test_tendsto hη hb hbη (fun y : ℝ => (1-y)^r)
    ((continuous_const.sub continuous_id).pow r).continuousOn

private theorem rectangular_numerator_moment_expansion_tendsto
    {η a b : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (haη : a ≤ η)
    (hb : 0 ≤ b) (hbη : b ≤ η) (ts : List Finite.NumeratorTerm) :
    Tendsto (fun n : ℕ => rectangularNumeratorMomentExpansion η
      n (betaProfileIndex η a n) n (betaProfileIndex η b n) ts)
      atTop (nhds (rectangularNumeratorTerms ts a (1-b))) := by
  induction ts with
  | nil => simp [rectangularNumeratorMomentExpansion, rectangularNumeratorTerms]
  | cons tr ts ih =>
    simp only [rectangularNumeratorMomentExpansion, rectangularNumeratorTerms,
      List.map_cons, List.sum_cons] at *
    have hc := ((rectangular_beta_power_moment_tendsto hη ha haη tr.i).const_mul
      ((tr.coefficient : ℝ)/201600)).mul (rectangular_beta_reflected_moment_tendsto hη hb hbη tr.j)
    exact hc.add ih

theorem rectangular_two_beta_numerator_tendsto (p : Fin 5 → ℝ)
    {η a b : ℝ} (hη0 : 0 < η) (hη : η < 1/4)
    (ha : 0 ≤ a) (haη : a ≤ η) (hb : 0 ≤ b) (hbη : b ≤ η) :
    Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..η, ∫ y in (0:ℝ)..η,
      betaScaledProfile η n (betaProfileIndex η a n) x*
      betaScaledProfile η n (betaProfileIndex η b n) y*
        numeratorPointKernel p x (1-y)) atTop (nhds (numeratorPointKernel p a (1-b))) := by
  simp_rw [rectangular_two_beta_numerator_eq_expansion p hη0 hη]
  rw [rectangular_numerator_reflected_eq p hη ⟨ha, haη⟩ ⟨hb, hbη⟩]
  unfold rectangularNumeratorBetaExpansion rectangularNumeratorFinite
  apply tendsto_finsetSum
  intro r _
  exact (rectangular_numerator_moment_expansion_tendsto hη0 ha haη hb hbη _).const_mul (p r)

end
end SixthMoment
