import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Sechstmoment.Zeta.DirichletL.CharPolynomials


namespace Sechstmoment.Source
open Complex Real Finset Filter Set
open scoped Topology BigOperators Classical
noncomputable section

def charSeriesWeightConstant : ℝ := ∑' k : ℕ, 1/((k : ℝ)+1)^2

theorem charSeriesWeight_summable : Summable (fun k : ℕ => 1/((k : ℝ)+1)^2) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))

theorem charSeriesWeightConstant_nonneg : 0 ≤ charSeriesWeightConstant :=
  tsum_nonneg (fun _ => by positivity)

theorem charResidueFibre_div_injective (q : ℕ) [NeZero q] (s : Finset ℕ) (a : ZMod q) :
    Set.InjOn (fun n : ℕ => n/q) (charResidueFibre q s a) := by
  intro n hn m hm hdiv
  change n/q = m/q at hdiv
  have hn' := (Finset.mem_filter.mp hn).2
  have hm' := (Finset.mem_filter.mp hm).2
  have hmod : n % q = m % q := by
    simpa only [ZMod.val_natCast] using congrArg ZMod.val (hn'.trans hm'.symm)
  have hn := Nat.mod_add_div n q
  have hm := Nat.mod_add_div m q
  rw [hmod,hdiv] at hn
  omega

theorem charResidueFibre_weight_sum_le (q : ℕ) [NeZero q] (s : Finset ℕ) (a : ZMod q) :
    ∑ n ∈ charResidueFibre q s a, 1/((n/q : ℕ)+1 : ℝ)^2 ≤ charSeriesWeightConstant := by
  have hinj := charResidueFibre_div_injective q s a
  have h := charSeriesWeight_summable.sum_le_tsum
    ((charResidueFibre q s a).image (fun n => n/q)) (fun _ _ => by positivity)
  rw [Finset.sum_image hinj] at h
  exact h

theorem finite_sum_norm_sq_le_weighted {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (w : ι → ℝ) (hw : ∀ n ∈ s, 0 < w n) :
    ‖∑ n ∈ s, c n‖^2 ≤
      (∑ n ∈ s, (w n)^2*‖c n‖^2)*(∑ n ∈ s, 1/(w n)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun n => w n*‖c n‖) (fun n => (w n)⁻¹)
  have he : (∑ n ∈ s, (w n*‖c n‖)*(w n)⁻¹) = ∑ n ∈ s, ‖c n‖ := by
    apply Finset.sum_congr rfl
    intro n hn
    field_simp [(hw n hn).ne']
  rw [he] at h
  calc
    _ ≤ (∑ n ∈ s, ‖c n‖)^2 := by gcongr; exact norm_sum_le _ _
    _ ≤ _ := by simpa only [mul_pow, inv_pow, one_div] using h

theorem charPolynomial_weighted_l2_bound (q : ℕ) [NeZero q]
    (s : Finset ℕ) (c : ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ s, c n*χ n‖^2 ≤
      (q.totient : ℝ)*charSeriesWeightConstant*
        ∑ n ∈ s, ((n/q : ℕ)+1 : ℝ)^2*‖c n‖^2 := by
  rw [charPolynomial_parseval]
  calc
    _ ≤ (q.totient : ℝ)*∑ a : ZMod q with IsUnit a,
        charSeriesWeightConstant*∑ n ∈ charResidueFibre q s a,
          ((n/q : ℕ)+1 : ℝ)^2*‖c n‖^2 := by
      gcongr with a ha
      have h := finite_sum_norm_sq_le_weighted (charResidueFibre q s a) c
        (fun n => ((n/q : ℕ)+1 : ℝ)) (fun _ _ => by positivity)
      calc
        _ ≤ _ := h
        _ ≤ _ := by
          rw [mul_comm]
          gcongr
          exact charResidueFibre_weight_sum_le q s a
    _ ≤ (q.totient : ℝ)*∑ a : ZMod q,
        charSeriesWeightConstant*∑ n ∈ charResidueFibre q s a,
          ((n/q : ℕ)+1 : ℝ)^2*‖c n‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q.totient)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ =>
        mul_nonneg charSeriesWeightConstant_nonneg (Finset.sum_nonneg fun _ _ => by positivity))
    _ = _ := by
      unfold charResidueFibre
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _)]
      ring

theorem charSeries_weighted_l2_bound (q : ℕ) [NeZero q] (c : ℕ → ℂ)
    (hc : Summable c)
    (hw : Summable (fun n : ℕ => ((n/q : ℕ)+1 : ℝ)^2*‖c n‖^2)) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑' n : ℕ, c n*χ n‖^2 ≤
      (q.totient : ℝ)*charSeriesWeightConstant*
        ∑' n : ℕ, ((n/q : ℕ)+1 : ℝ)^2*‖c n‖^2 := by
  have hχ (χ : DirichletCharacter ℂ q) : Summable (fun n : ℕ => c n*χ n) := by
    apply Summable.of_norm
    exact hc.norm.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
  have hlim : Tendsto (fun N : ℕ => ∑ χ : DirichletCharacter ℂ q,
      ‖∑ n ∈ Finset.range N, c n*χ n‖^2) atTop
      (𝓝 (∑ χ : DirichletCharacter ℂ q, ‖∑' n : ℕ, c n*χ n‖^2)) := by
    exact tendsto_finsetSum Finset.univ (fun χ _ => (hχ χ).hasSum.tendsto_sum_nat.norm.pow 2)
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro N
  apply (charPolynomial_weighted_l2_bound q (Finset.range N) c).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) charSeriesWeightConstant_nonneg)
  exact hw.sum_le_tsum (Finset.range N) (fun _ _ => by positivity)

end
end Sechstmoment.Source
