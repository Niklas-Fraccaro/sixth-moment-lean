import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Order.Compact
import Sechstmoment.Analysis.Integration.FiniteFubini
import Sechstmoment.Certificate.Kernels.Balanced.DensityBridge
import Sechstmoment.Certificate.Kernels.Balanced.RegionCoordinates

namespace Sechstmoment
open MeasureTheory

set_option maxHeartbeats 0

theorem denominatorRegion_compact (a b c d : ℝ) : IsCompact (denominatorRegion a b c d) := by
  apply (isCompact_Icc (a := fun _ : Fin 4 => (0 : ℝ))
    (b := fun _ => max a b)).of_isClosed_subset (denominatorRegion_closed a b c d)
  intro v hv
  rcases hv with ⟨h0,h1,h2,h3,ha,hb,hc,hd⟩
  constructor
  · intro i
    fin_cases i <;> assumption
  · intro i
    fin_cases i <;> dsimp
    · exact le_trans (by linarith) (le_max_left _ _)
    · exact le_trans (by linarith) (le_max_left _ _)
    · exact le_trans (by linarith) (le_max_right _ _)
    · exact le_trans (by linarith) (le_max_right _ _)

theorem denominatorCoordinateRegion_compact (a b c d : ℝ) :
    IsCompact (denominatorCoordinateRegion a b c d) := by
  have he : denominatorCoordinateRegion a b c d =
      denominatorCoordinateChange '' denominatorRegion a b c d := by
    rw [denominatorRegion_coordinate_preimage]
    exact (Set.image_preimage_eq _ denominatorCoordinateHomeomorph.surjective).symm
  rw [he]
  exact (denominatorRegion_compact a b c d).image
    denominatorCoordinateHomeomorph.continuous

theorem denominator_region_indicator_integrable (a b c d : ℝ)
    (f : (Fin 4 → ℝ) → ℝ) (hf : Continuous f) :
    Integrable ((denominatorCoordinateRegion a b c d).indicator f) := by
  apply (hf.continuousOn.integrableOn_compact
    (denominatorCoordinateRegion_compact a b c d)).integrable_indicator
  exact (denominatorCoordinateRegion_closed a b c d).measurableSet

theorem denominator_region_integral_fubini (a b c d : ℝ)
    (f : (Fin 4 → ℝ) → ℝ) (hf : Continuous f) :
    (∫ w in denominatorCoordinateRegion a b c d, f w) =
      ∫ t, ∫ r, ∫ s, ∫ x,
        (denominatorCoordinateRegion a b c d).indicator f ![t,r,s,x] := by
  rw [← integral_indicator (denominatorCoordinateRegion_closed a b c d).measurableSet]
  exact integral_fin_four _ (denominator_region_indicator_integrable a b c d f hf)

theorem indicator_Icc_integral (a b : ℝ) (f : ℝ → ℝ) (hab : a ≤ b) :
    (∫ x, (Set.Icc a b).indicator f x) = ∫ x in a..b, f x := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

theorem denominator_row_bounds {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 ≤ t) (hab : t ≤ a+b) : max 0 (t-b) ≤ min a t := by
  simp only [max_le_iff, le_min_iff]
  (repeat' constructor) <;> linarith

theorem denominator_region_nested_indicator (a b c d t r s x : ℝ)
    (f : (Fin 4 → ℝ) → ℝ) :
    (denominatorCoordinateRegion a b c d).indicator f ![t,r,s,x] =
      (Set.Icc 0 (min (a+b) (c+d))).indicator (fun t =>
        (Set.Icc (max 0 (t-b)) (min a t)).indicator (fun r =>
          (Set.Icc (max 0 (t-d)) (min c t)).indicator (fun s =>
            (Set.Icc (max 0 (r+s-t)) (min r s)).indicator (fun x =>
              f ![t,r,s,x]) x) s) r) t := by
  classical
  have hm : ![t,r,s,x] ∈ denominatorCoordinateRegion a b c d ↔
      t ∈ Set.Icc 0 (min (a+b) (c+d)) ∧
        r ∈ Set.Icc (max 0 (t-b)) (min a t) ∧
          s ∈ Set.Icc (max 0 (t-d)) (min c t) ∧
            x ∈ Set.Icc (max 0 (r+s-t)) (min r s) := by
    change (0 ≤ t ∧ t ≤ min (a+b) (c+d) ∧
      max 0 (t-b) ≤ r ∧ r ≤ min a t ∧
      max 0 (t-d) ≤ s ∧ s ≤ min c t ∧
      max 0 (r+s-t) ≤ x ∧ x ≤ min r s) ↔ _
    simp only [Set.mem_Icc, and_assoc]
  rw [Set.indicator_apply, hm]
  simp only [Set.indicator_apply]
  by_cases ht : t ∈ Set.Icc 0 (min (a+b) (c+d))
  <;> by_cases hr : r ∈ Set.Icc (max 0 (t-b)) (min a t)
  <;> by_cases hs : s ∈ Set.Icc (max 0 (t-d)) (min c t)
  <;> by_cases hx : x ∈ Set.Icc (max 0 (r+s-t)) (min r s)
  <;> simp only [ht, hr, hs, hx, and_true, and_false, ite_true, ite_false]

theorem denominator_region_iterated_integral {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (f : (Fin 4 → ℝ) → ℝ) (hf : Continuous f) :
    (∫ w in denominatorCoordinateRegion a b c d, f w) =
      ∫ t in 0..min (a+b) (c+d),
        ∫ r in max 0 (t-b)..min a t,
          ∫ s in max 0 (t-d)..min c t,
            ∫ x in max 0 (r+s-t)..min r s, f ![t,r,s,x] := by
  have hE : (0 : ℝ) ≤ min (a+b) (c+d) := le_min (add_nonneg ha hb) (add_nonneg hc hd)
  rw [denominator_region_integral_fubini a b c d f hf]
  simp_rw [denominator_region_nested_indicator, integral_indicator₂]
  rw [indicator_Icc_integral 0 _ _ hE]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [Set.uIcc_of_le hE] at ht
  have hr := denominator_row_bounds ha hb ht.1 (ht.2.trans (min_le_left _ _))
  have hs := denominator_row_bounds hc hd ht.1 (ht.2.trans (min_le_right _ _))
  rw [indicator_Icc_integral _ _ _ hr]
  apply intervalIntegral.integral_congr
  intro r hrr
  dsimp only
  rw [Set.uIcc_of_le hr] at hrr
  rw [indicator_Icc_integral _ _ _ hs]
  apply intervalIntegral.integral_congr
  intro s hss
  dsimp only
  rw [Set.uIcc_of_le hs] at hss
  have hx := denominator_free_interval_nonnegative
    ((le_max_left _ _).trans hrr.1) ((le_max_left _ _).trans hss.1)
    (hrr.2.trans (min_le_right _ _)) (hss.2.trans (min_le_right _ _))
  exact indicator_Icc_integral _ _ _ hx

theorem denominator_original_iterated_integral {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (f : (Fin 4 → ℝ) → ℝ) (hf : Continuous f) :
    (∫ v in denominatorRegion a b c d, f (denominatorCoordinateChange v)) =
      ∫ t in 0..min (a+b) (c+d),
        ∫ r in max 0 (t-b)..min a t,
          ∫ s in max 0 (t-d)..min c t,
            ∫ x in max 0 (r+s-t)..min r s, f ![t,r,s,x] := by
  rw [denominator_region_integral_coordinate_change]
  exact denominator_region_iterated_integral ha hb hc hd f hf

end Sechstmoment
