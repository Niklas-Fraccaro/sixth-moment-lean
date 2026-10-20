import SixthMoment.Certificate.Gram.GroupingNorm
import SixthMoment.Final.CauchySchwarz

namespace SixthMoment
open Complex MeasureTheory Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem certificateFeatureZetaTest_continuous (n : ℕ) (hn : 0 < n)
    {T : ℝ} (hT : 1 < T) (x : Finite.Feature) :
    Continuous (fun t : ℝ => featureZetaTest (certificateActualProfiles n) T t x) := by
  have hF : Continuous (fun t : ℝ => featureRawZetaTest (certificateActualProfiles n) T t x) :=
    rawZetaTest_continuous x.typ hT
      (max ((x.A:ℝ)/base) eta) (max ((x.B:ℝ)/base) eta) _ _ _
      (certificateActualProfiles_zero_above n hn x.typ _)
      (certificateActualProfiles_zero_above n hn x.typ _)
  unfold featureZetaTest phaseProjection
  exact (hF.add ((criticalChi_continuous.pow 3).mul hF.star)).div_const 2

private theorem certificateGram_weighted_continuous_integrable
    {T : ℝ} (hT : T ≠ 0) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (K : ℝ → ℝ) (hK : Continuous K) :
    Integrable (fun t : ℝ => Φ (t/T)*K t) := by
  have hΦs : HasCompactSupport Φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport Φ) hΦ.2
  have hs := hΦs.comp_smul (inv_ne_zero hT)
  have hss : HasCompactSupport (fun t : ℝ => Φ (t/T)) := by
    simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using hs
  have hc : Continuous (fun t : ℝ => Φ (t/T)*K t) :=
    (hΦ.1.continuous.comp (continuous_id.div_const T)).mul hK
  exact hc.integrable_of_hasCompactSupport hss.mul_right

def certificateFeatureProjectedGramMoment (n : ℕ) (T : ℝ) (Φ : ℝ → ℝ)
    (x y : Finite.Feature) : ℝ :=
  ∫ t : ℝ, Φ (t/T)*
    (featureZetaTest (certificateActualProfiles n) T t x*
      star (featureZetaTest (certificateActualProfiles n) T t y)).re

theorem certificateFeatureProjectedGramIntegrand_integrable (n : ℕ) (hn : 0 < n)
    {T : ℝ} (hT : 1 < T) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (x y : Finite.Feature) :
    Integrable (fun t : ℝ => Φ (t/T)*
      (featureZetaTest (certificateActualProfiles n) T t x*
        star (featureZetaTest (certificateActualProfiles n) T t y)).re) := by
  exact certificateGram_weighted_continuous_integrable
    (ne_of_gt (zero_lt_one.trans hT)) Φ hΦ _
    (Complex.continuous_re.comp ((certificateFeatureZetaTest_continuous n hn hT x).mul
      (certificateFeatureZetaTest_continuous n hn hT y).star))

theorem actual250ProjectedGramMomentIntegrand_integrable (n : ℕ) (hn : 0 < n)
    {T : ℝ} (hT : 1 < T) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t : ℝ => Φ (t/T)*
      ‖certificateZetaTest (certificateActualProfiles n) T t‖^2) :=
  certificateGram_weighted_continuous_integrable (ne_of_gt (zero_lt_one.trans hT))
    Φ hΦ _ ((certificateActualZetaTest_continuous n hn hT).norm.pow 2)

private theorem certificateGram_list_integrable {α : Type} (l : List α) (f : α → ℝ → ℝ)
    (hi : ∀ a ∈ l, Integrable (f a)) :
    Integrable (fun t : ℝ => (l.map fun a => f a t).sum) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (hi a List.mem_cons_self).add
      (ih (fun b hb => hi b (List.mem_cons_of_mem a hb)))

private theorem certificateGram_integral_list_sum {α : Type} (l : List α) (f : α → ℝ → ℝ)
    (hi : ∀ a ∈ l, Integrable (f a)) :
    (∫ t : ℝ, (l.map fun a => f a t).sum) =
      (l.map fun a => ∫ t : ℝ, f a t).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hi a List.mem_cons_self)
      (certificateGram_list_integrable l f (fun b hb => hi b (List.mem_cons_of_mem a hb)))]
    rw [ih (fun b hb => hi b (List.mem_cons_of_mem a hb))]

theorem actual250ProjectedGramMoment_eq_certificate_pair_sum
    (n : ℕ) (hn : 0 < n) {T : ℝ} (hT : 1 < T)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    actual250ProjectedGramMoment n T Φ =
      (Finite.pairs.map fun ij => (if ij.1=ij.2 then (1:ℝ) else 2)*
        certificateFeatureProjectedGramMoment n T Φ
          (Finite.feature ij.1) (Finite.feature ij.2)).sum := by
  let f : (ℕ × ℕ) → ℝ → ℝ := fun ij t =>
    (if ij.1=ij.2 then (1:ℝ) else 2)*
      (Φ (t/T)*(featureZetaTest (certificateActualProfiles n) T t (Finite.feature ij.1)*
        star (featureZetaTest (certificateActualProfiles n) T t (Finite.feature ij.2))).re)
  have hi (ij : ℕ × ℕ) : Integrable (f ij) :=
    (certificateFeatureProjectedGramIntegrand_integrable n hn hT Φ hΦ
      (Finite.feature ij.1) (Finite.feature ij.2)).const_mul _
  have he (t : ℝ) : Φ (t/T)*
      ‖certificateZetaTest (certificateActualProfiles n) T t‖^2 =
      (Finite.pairs.map fun ij => f ij t).sum := by
    rw [certificateZetaTest_norm_sq_pair_sum,←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro ij _
    dsimp only [f]
    ring
  unfold actual250ProjectedGramMoment
  simp_rw [he]
  rw [certificateGram_integral_list_sum _ _ (fun ij _ => hi ij)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ij _
  dsimp only [f]
  rw [integral_const_mul]
  rfl

end
end SixthMoment
